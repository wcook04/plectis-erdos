#!/usr/bin/env python3
"""Memory-bounded Lake build for projects with wide local import graphs.

Lake 5 schedules every ready build job and no longer exposes a build-worker
limit.  That is fast for small modules, but a wide layer of memory-heavy Lean
files can make a workstation swap.  This wrapper builds stale local modules in
topological waves with a bounded process pool, then delegates the requested
target to ordinary ``lake build`` as the final authority check.

``--plan`` reports compact dependency-wave sizes. Add ``--verbose-plan`` when
the exact module names are needed for diagnosis.
"""

from __future__ import annotations

import argparse
import fcntl
import hashlib
import json
import os
from pathlib import Path
import re
import shlex
import shutil
import subprocess
import sys
import time
from typing import Iterable

CONTROL_PLANE_CHILD_ENV = "AIW_LEAN_FAST_BUILD_SINGLEFLIGHT_CHILD"
RESOURCE_LEASE_TOKEN_ENV = "AIW_RESOURCE_LEASE_TOKEN"
HOST_MATHLIB_BUILD_CONFLICT_KEY = "lean-mathlib-host-build:v1"
PLECTIS_LEAN_HOST_LOCK_ROOT_ENV = "PLECTIS_LEAN_HOST_LOCK_ROOT"
DEFAULT_LAKE_FIREWALL_MIN_FREE_BYTES = 12 * 1024**3
DEFAULT_LAKE_BUILD_LAUNCH_RESERVE_BYTES = 2 * 1024**3
LAKE_BUILD_LAUNCH_RESERVE_GIB_ENV = "AIW_LEAN_BUILD_DISK_RESERVE_GIB"
LAKE_FIREWALL_STATUS_PATH = (
    Path.home()
    / "Library"
    / "Application Support"
    / "ai_workflow"
    / "lake-build-firewall-status.json"
)

command_run_singleflight = None
resource_capacity_broker = None
command_future = None
lean_build_cache = None
_CONTROL_PLANE_LOADED = False


def public_lean_host_lock_path() -> Path:
    """Return the lock shared with every public Plectis cold clone.

    This intentionally has no checkout identity in its path. The public repo
    implements the same small filesystem protocol without importing this
    private control plane.
    """

    override = os.environ.get(PLECTIS_LEAN_HOST_LOCK_ROOT_ENV)
    if override:
        root = Path(override).expanduser()
        if not root.is_absolute():
            root = Path.cwd() / root
    else:
        xdg_cache = os.environ.get("XDG_CACHE_HOME")
        if xdg_cache:
            cache_home = Path(xdg_cache).expanduser()
        elif sys.platform == "darwin":
            cache_home = Path.home() / "Library" / "Caches"
        else:
            cache_home = Path.home() / ".cache"
        root = cache_home / "plectis-lean" / "host-locks-v1"
    return root / "resource-lean-host.lock"


def try_public_lean_host_lock() -> tuple[object | None, Path]:
    """Acquire the public/private host-build mutex without occupying the caller."""

    path = public_lean_host_lock_path()
    path.parent.mkdir(parents=True, exist_ok=True)
    handle = path.open("a+", encoding="utf-8")
    try:
        fcntl.flock(handle.fileno(), fcntl.LOCK_EX | fcntl.LOCK_NB)
    except BlockingIOError:
        handle.close()
        return None, path
    return handle, path


IMPORT_RE = re.compile(r"^\s*import\s+([A-Za-z0-9_'.]+)\s*(?:--.*)?$")


def load_control_plane() -> None:
    """Load mutation guards only when a build, rather than a plan, will run."""

    global _CONTROL_PLANE_LOADED, command_run_singleflight, resource_capacity_broker
    global command_future
    global lean_build_cache
    if _CONTROL_PLANE_LOADED:
        return
    _CONTROL_PLANE_LOADED = True
    try:
        from system.lib import command_run_singleflight as singleflight
        from system.lib import command_future as future_runner
        from system.lib import resource_capacity_broker as capacity_broker
        from tools.meta import lean_build_cache as cache_manager
    except ImportError:  # Public/standalone copies remain usable without ai_workflow.
        return
    command_run_singleflight = singleflight
    command_future = future_runner
    resource_capacity_broker = capacity_broker
    lean_build_cache = cache_manager


def admit_workspace_dependency_cache(project_root: Path) -> dict[str, object]:
    """Safely attach a compatible dependency cache for detached checkouts.

    The global validator owns this admission so agents never need to copy an
    11GB ``.lake`` tree or point a mutable checkout at another checkout with a
    symlink. Existing independent package caches are left untouched.
    """

    if not all(
        (project_root / name).is_file()
        for name in ("lean-toolchain", "lake-manifest.json")
    ):
        return {
            "schema": "lean_workspace_cache_attachment_v0",
            "status": "not_applicable_without_semantic_lock",
            "action": "unavailable",
            "target": str(project_root),
        }
    if lean_build_cache is None:
        return {
            "schema": "lean_workspace_cache_attachment_v0",
            "status": "control_plane_unavailable",
            "action": "unavailable",
            "target": str(project_root),
        }
    broker_root = control_plane_root(project_root)
    roots = lean_build_cache.discover_workspaces(broker_root, Path.home())
    return lean_build_cache.attach_workspace_cache(project_root, roots, yes=True)


def restore_compatible_build_artifacts(
    project_root: Path,
    identity: dict[str, object],
) -> dict[str, object]:
    """Seed an exact checkout-local build tree without sharing mutable state."""

    if lean_build_cache is None:
        return {"status": "control_plane_unavailable", "action": "build_normally"}
    broker_root = control_plane_root(project_root)
    roots = lean_build_cache.discover_workspaces(broker_root, Path.home())
    return lean_build_cache.restore_build_artifact_seed(project_root, roots, identity)


def publish_compatible_build_artifacts(
    project_root: Path,
    identity: dict[str, object],
) -> dict[str, object]:
    """Make a successful Lake result available as an exact immutable seed."""

    if lean_build_cache is None:
        return {"status": "control_plane_unavailable"}
    return lean_build_cache.publish_build_artifact_seed(project_root, identity)


def emit_workspace_cache_admission(payload: dict[str, object]) -> None:
    """Emit attachment/defer/rejection receipts without polluting stdout."""

    print(json.dumps(payload, sort_keys=True), file=sys.stderr, flush=True)


def default_jobs() -> int:
    configured = os.environ.get("LEAN_BUILD_JOBS") or os.environ.get("AIW_CHILD_PROCESS_BUDGET")
    if configured:
        try:
            return max(1, int(configured))
        except ValueError:
            pass
    cpu_count = max(1, os.cpu_count() or 1)
    interactive_reserve = max(1, cpu_count // 4)
    return min(2, max(1, (cpu_count - interactive_reserve) // 2))


def disk_admission_decision(
    *,
    free_bytes: int,
    minimum_free_bytes: int,
    launch_reserve_bytes: int,
    minimum_source: str,
) -> dict[str, int | bool | str]:
    """Return the deterministic floor-plus-reserve launch verdict."""
    minimum_launch_free_bytes = minimum_free_bytes + launch_reserve_bytes
    allow = free_bytes >= minimum_launch_free_bytes
    reason = (
        "clear"
        if allow
        else "low_disk_floor"
        if free_bytes < minimum_free_bytes
        else "insufficient_build_headroom"
    )
    return {
        "allow": allow,
        "reason": reason,
        "free_bytes": free_bytes,
        "minimum_free_bytes": minimum_free_bytes,
        "launch_reserve_bytes": launch_reserve_bytes,
        "minimum_launch_free_bytes": minimum_launch_free_bytes,
        "minimum_source": minimum_source,
    }


def disk_admission(project_root: Path) -> dict[str, int | bool | str]:
    """Require enough headroom that the firewall will not kill a new build."""

    minimum_free_bytes = DEFAULT_LAKE_FIREWALL_MIN_FREE_BYTES
    minimum_source = "default_lake_firewall_floor"
    try:
        status = json.loads(LAKE_FIREWALL_STATUS_PATH.read_text(encoding="utf-8"))
    except (OSError, json.JSONDecodeError, TypeError):
        status = {}
    if isinstance(status, dict) and int(status.get("minimum_free_bytes") or 0) > 0:
        minimum_free_bytes = int(status["minimum_free_bytes"])
        minimum_source = "live_lake_build_firewall_status"
    launch_reserve_bytes = DEFAULT_LAKE_BUILD_LAUNCH_RESERVE_BYTES
    if isinstance(status, dict) and int(status.get("launch_reserve_bytes") or 0) > 0:
        launch_reserve_bytes = int(status["launch_reserve_bytes"])
    configured_reserve = os.environ.get(LAKE_BUILD_LAUNCH_RESERVE_GIB_ENV)
    if configured_reserve:
        try:
            launch_reserve_bytes = max(0, int(float(configured_reserve) * 1024**3))
        except ValueError:
            pass
    return disk_admission_decision(
        free_bytes=shutil.disk_usage(project_root).free,
        minimum_free_bytes=minimum_free_bytes,
        launch_reserve_bytes=launch_reserve_bytes,
        minimum_source=minimum_source,
    )


def source_module(project_root: Path, source: Path) -> str:
    return ".".join(source.relative_to(project_root).with_suffix("").parts)


def discover_modules(project_root: Path) -> dict[str, Path]:
    modules: dict[str, Path] = {}
    for directory, dirnames, filenames in os.walk(project_root):
        dirnames[:] = [name for name in dirnames if not name.startswith(".")]
        directory_path = Path(directory)
        module_prefix = directory_path.relative_to(project_root).parts
        for filename in filenames:
            if not filename.endswith(".lean") or filename.startswith("_"):
                continue
            source = directory_path / filename
            module = ".".join((*module_prefix, filename[:-5]))
            modules[module] = source
    return modules


def code_without_comments(line: str, block_depth: int) -> tuple[str, int]:
    """Remove nested Lean comments from one header line."""

    code: list[str] = []
    index = 0
    while index < len(line):
        if block_depth:
            if line.startswith("/-", index):
                block_depth += 1
                index += 2
            elif line.startswith("-/", index):
                block_depth -= 1
                index += 2
            else:
                index += 1
        elif line.startswith("--", index):
            break
        elif line.startswith("/-", index):
            block_depth = 1
            index += 2
        else:
            code.append(line[index])
            index += 1
    return "".join(code), block_depth


def local_imports(source: Path, modules: dict[str, Path]) -> set[str]:
    """Read only Lean's import header instead of the complete source file."""

    imports: set[str] = set()
    block_depth = 0
    with source.open(encoding="utf-8") as lines:
        for raw_line in lines:
            code, block_depth = code_without_comments(raw_line, block_depth)
            stripped = code.strip()
            if not stripped or stripped == "prelude":
                continue
            match = IMPORT_RE.match(stripped)
            if match:
                if match.group(1) in modules:
                    imports.add(match.group(1))
                continue
            break
    return imports


def import_graph(modules: dict[str, Path]) -> dict[str, set[str]]:
    return {name: local_imports(source, modules) for name, source in modules.items()}


def reachable_import_graph(
    roots: Iterable[str], modules: dict[str, Path]
) -> dict[str, set[str]]:
    """Parse only the local import cone reachable from ``roots``."""

    graph: dict[str, set[str]] = {}
    pending = list(roots)
    while pending:
        module = pending.pop()
        if module in graph:
            continue
        imports = local_imports(modules[module], modules)
        graph[module] = imports
        pending.extend(imports - graph.keys())
    return graph


def target_module(target: str, project_root: Path, modules: dict[str, Path]) -> str | None:
    candidate, _facet = split_target_facet(target)
    candidate = candidate.removeprefix("+")
    if candidate in modules:
        return candidate
    target_path = (project_root / candidate).resolve()
    if target_path.suffix == ".lean":
        try:
            path_module = source_module(project_root.resolve(), target_path)
        except ValueError:
            path_module = None
        if path_module in modules and modules[path_module].resolve() == target_path:
            return path_module
    return None


def split_target_facet(target: str) -> tuple[str, str | None]:
    """Separate the supported OLean-only facet without changing other targets."""

    candidate, separator, facet = target.rpartition(":")
    if separator and candidate and facet == "olean":
        return candidate, facet
    return target, None


def common_prebuild_facet(targets: Iterable[str]) -> str | None:
    """Preserve OLean-only intent when every requested target asks for it."""

    requested = list(targets)
    if requested and all(
        split_target_facet(target)[1] == "olean" for target in requested
    ):
        return "olean"
    return None


def module_build_target(module: str, facet: str | None = None) -> str:
    suffix = f":{facet}" if facet else ""
    return f"+{module}{suffix}"


def changed_lean_paths(base: str, project_root: Path) -> set[Path]:
    """Return tracked or untracked Lean paths changed from ``base``."""

    commands = (
        ["git", "diff", "--name-only", "--diff-filter=ACMR", base, "--", "*.lean"],
        ["git", "ls-files", "--others", "--exclude-standard", "--", "*.lean"],
    )
    changed_paths: set[Path] = set()
    for command in commands:
        completed = subprocess.run(
            command,
            cwd=project_root,
            capture_output=True,
            text=True,
            check=False,
        )
        if completed.returncode:
            detail = completed.stderr.strip() or f"exit {completed.returncode}"
            raise RuntimeError(f"cannot resolve changed Lean modules: {detail}")
        changed_paths.update(
            (project_root / line).resolve()
            for line in completed.stdout.splitlines()
            if line.strip()
        )
    return changed_paths


def changed_modules_from_paths(
    changed_paths: Iterable[Path], modules: dict[str, Path], project_root: Path
) -> list[str]:
    resolved_root = project_root.resolve()
    changed: set[str] = set()
    for path in changed_paths:
        resolved_path = path.resolve()
        try:
            module = source_module(resolved_root, resolved_path)
        except ValueError:
            continue
        if module in modules and modules[module].resolve() == resolved_path:
            changed.add(module)
    return sorted(changed)


def changed_modules(
    base: str,
    project_root: Path,
    modules: dict[str, Path],
) -> list[str]:
    """Return tracked or untracked local Lean modules changed from ``base``."""

    return changed_modules_from_paths(
        changed_lean_paths(base, project_root), modules, project_root
    )


def mixed_root_and_focused_targets(
    project_root: Path,
    targets: Iterable[str],
) -> tuple[list[str], list[str]]:
    """Separate project-root modules from narrower local module targets."""

    requested = list(targets)
    if len(requested) < 2:
        return [], []
    modules = discover_modules(project_root)
    root_targets: list[str] = []
    focused_targets: list[str] = []
    for target in requested:
        module = target_module(target, project_root, modules)
        if module is None:
            continue
        if modules[module].parent == project_root:
            root_targets.append(target)
        else:
            focused_targets.append(target)
    return root_targets, focused_targets


def reachable_modules(targets: Iterable[str], graph: dict[str, set[str]]) -> set[str]:
    reachable: set[str] = set()
    stack = list(targets)
    while stack:
        module = stack.pop()
        if module in reachable:
            continue
        reachable.add(module)
        stack.extend(graph[module])
    return reachable


def topological_waves(selected: set[str], graph: dict[str, set[str]]) -> list[list[str]]:
    remaining = set(selected)
    completed: set[str] = set()
    waves: list[list[str]] = []
    while remaining:
        ready = sorted(module for module in remaining if (graph[module] & selected) <= completed)
        if not ready:
            cycle = ", ".join(sorted(remaining)[:8])
            raise ValueError(f"local import cycle detected near: {cycle}")
        waves.append(ready)
        completed.update(ready)
        remaining.difference_update(ready)
    return waves


def olean_path(project_root: Path, module: str) -> Path:
    return project_root / ".lake" / "build" / "lib" / "lean" / Path(*module.split(".")).with_suffix(".olean")


def file_mtime_ns(path: Path) -> int | None:
    try:
        return path.stat().st_mtime_ns
    except FileNotFoundError:
        return None


def project_config_mtime_ns(project_root: Path) -> int | None:
    mtimes = [
        mtime
        for name in ("lakefile.toml", "lakefile.lean", "lake-manifest.json", "lean-toolchain")
        if (mtime := file_mtime_ns(project_root / name)) is not None
    ]
    return max(mtimes, default=None)


def olean_mtime_ns(
    project_root: Path,
    module: str,
    cache: dict[str, int | None] | None = None,
) -> int | None:
    if cache is not None and module in cache:
        return cache[module]
    mtime = file_mtime_ns(olean_path(project_root, module))
    if cache is not None:
        cache[module] = mtime
    return mtime


def module_is_stale(
    project_root: Path,
    module: str,
    modules: dict[str, Path],
    graph: dict[str, set[str]],
    *,
    cached_olean_mtimes: dict[str, int | None] | None = None,
    cached_config_mtime_ns: int | None = None,
) -> bool:
    output_mtime = olean_mtime_ns(project_root, module, cached_olean_mtimes)
    if output_mtime is None:
        return True
    if modules[module].stat().st_mtime_ns > output_mtime:
        return True
    for dependency in graph[module]:
        dependency_mtime = olean_mtime_ns(
            project_root, dependency, cached_olean_mtimes
        )
        if dependency_mtime is None or dependency_mtime > output_mtime:
            return True
    config_mtime = (
        cached_config_mtime_ns
        if cached_olean_mtimes is not None
        else project_config_mtime_ns(project_root)
    )
    return config_mtime is not None and config_mtime > output_mtime


def lake_targets_up_to_date(
    project_root: Path,
    lake: str,
    modules: Iterable[str],
    *,
    rehash: bool = True,
    facet: str | None = None,
) -> bool:
    """Ask Lake for a content-trace verdict without starting a build."""

    targets = list(modules)
    if not targets:
        return True
    command = [lake]
    if rehash:
        command.append("--rehash")
    command.extend(
        [
            "--no-build",
            "build",
            *(module_build_target(module, facet) for module in targets),
        ]
    )
    result = subprocess.run(
        command,
        cwd=project_root,
        stdout=subprocess.DEVNULL,
        stderr=subprocess.DEVNULL,
        check=False,
    )
    return result.returncode == 0


def lake_stale_modules(
    project_root: Path,
    lake: str,
    modules: Iterable[str],
    *,
    rehash: bool = True,
    facet: str | None = None,
) -> list[str]:
    """Bisect a module batch to the members Lake marks stale by content trace."""

    targets = list(modules)
    if not targets or lake_targets_up_to_date(
        project_root,
        lake,
        targets,
        rehash=rehash,
        facet=facet,
    ):
        return []
    if len(targets) == 1:
        return targets
    midpoint = len(targets) // 2
    return lake_stale_modules(
        project_root,
        lake,
        targets[:midpoint],
        rehash=False,
        facet=facet,
    ) + lake_stale_modules(
        project_root,
        lake,
        targets[midpoint:],
        rehash=False,
        facet=facet,
    )


def run_module(
    project_root: Path,
    lake: str,
    module: str,
    facet: str | None = None,
) -> tuple[str, int, float]:
    started = time.monotonic()
    result = subprocess.run(
        [lake, "build", module_build_target(module, facet)],
        cwd=project_root,
        check=False,
    )
    return module, result.returncode, time.monotonic() - started


def build_wave(
    project_root: Path,
    lake: str,
    modules: list[str],
    jobs: int,
    *,
    facet: str | None = None,
) -> None:
    if not modules:
        return
    from concurrent.futures import ThreadPoolExecutor, as_completed

    print(f"lean-fast-build: prebuilding {len(modules)} module(s), max {jobs} concurrent")
    with ThreadPoolExecutor(max_workers=jobs) as executor:
        futures = {
            executor.submit(run_module, project_root, lake, module, facet): module
            for module in modules
        }
        failures: list[str] = []
        for future in as_completed(futures):
            module, returncode, duration = future.result()
            print(f"lean-fast-build: {module} -> {returncode} ({duration:.1f}s)")
            if returncode:
                failures.append(module)
        if failures:
            raise RuntimeError("module prebuild failed: " + ", ".join(sorted(failures)))


def plan_lines(build_waves: Iterable[Iterable[str]], *, verbose: bool) -> list[str]:
    """Format a readable build plan without flooding normal terminals."""

    lines: list[str] = []
    for index, wave in enumerate(build_waves, 1):
        modules = list(wave)
        detail = " ".join(modules) if verbose else f"{len(modules)} module(s)"
        lines.append(f"wave {index}: {detail}")
    return lines


def run_final_authority_check(project_root: Path, lake: str, targets: Iterable[str]) -> int:
    """Check requested targets without restoring Lake's unbounded fan-out.

    The bounded prebuild above has already materialized every stale local
    dependency in the target cone.  Passing several roots back to one raw
    ``lake build`` call lets Lake schedule the roots together and can recreate
    the memory spike this wrapper exists to prevent.  Checking roots one at a
    time preserves the ordinary Lake authority check while keeping the process
    bound intact.
    """
    target_list = list(targets)
    if not target_list:
        return subprocess.run([lake, "build"], cwd=project_root, check=False).returncode
    modules = discover_modules(project_root)
    for target in target_list:
        module = target_module(target, project_root, modules)
        unqualified_target, facet = split_target_facet(target)
        # A bare nested module name can collide with another Lake target kind.
        # The bounded prebuild is explicitly module-scoped, so preserve that
        # meaning in the final authority check.  Root-level names remain bare
        # because they commonly denote the project's lean_lib target.
        authority_target = (
            module_build_target(module, facet)
            if module is not None
            and modules[module].parent != project_root
            and not target.startswith("+")
            and not unqualified_target.endswith(".lean")
            else target
        )
        result = subprocess.run(
            [lake, "build", authority_target], cwd=project_root, check=False
        )
        if result.returncode:
            return result.returncode
    return 0


def materialize_dependencies(args: argparse.Namespace, project_root: Path) -> int:
    """Fetch dependency sources and the Mathlib olean cache under the host lock.

    ``lake update`` and ``lake exe cache get`` are package-materializing Lake
    operations. The build firewall terminates them outside the canonical
    checkout unless a ``lean_fast_build.py`` ancestor governs them, so this
    mode runs them as direct children of the wrapper while holding the same
    host mutex a build would hold. It compiles nothing and reports a receipt.
    """

    lake = str(args.lake)
    packages = [str(name) for name in args.materialize_dependencies]
    host_lock, host_lock_path = try_public_lean_host_lock()
    if host_lock is None:
        print(
            json.dumps(
                {
                    "schema": "lean_fast_build_materialize_receipt_v0",
                    "status": "deferred_host_lock_busy",
                    "project_root": str(project_root),
                    "host_lock": str(host_lock_path),
                    "exit_code": 75,
                    "next_action": "reinvoke_after_the_current_host_build_releases_the_lock",
                },
                sort_keys=True,
            ),
            file=sys.stderr,
        )
        return 75
    steps: list[dict[str, object]] = []
    exit_code = 0
    try:
        commands = []
        if packages:
            commands.append([lake, "update", *packages])
        commands.append([lake, "exe", "cache", "get"])
        for command in commands:
            started = time.monotonic()
            result = subprocess.run(command, cwd=project_root, check=False)
            steps.append(
                {
                    "command": command,
                    "exit_code": result.returncode,
                    "elapsed_seconds": round(time.monotonic() - started, 1),
                }
            )
            if result.returncode:
                exit_code = result.returncode
                break
    finally:
        fcntl.flock(host_lock.fileno(), fcntl.LOCK_UN)
        host_lock.close()
    print(
        json.dumps(
            {
                "schema": "lean_fast_build_materialize_receipt_v0",
                "status": "materialized" if exit_code == 0 else "failed",
                "project_root": str(project_root),
                "packages": packages,
                "steps": steps,
                "exit_code": exit_code,
                "proof_scope": "not_proof_evidence",
            },
            sort_keys=True,
        )
    )
    return exit_code


def parser() -> argparse.ArgumentParser:
    arg_parser = argparse.ArgumentParser(description=__doc__)
    arg_parser.add_argument("targets", nargs="*", help="Lake target/module; defaults to the project root module")
    arg_parser.add_argument(
        "--changed-from",
        nargs="?",
        const="HEAD",
        metavar="REF",
        help="build changed Lean modules relative to REF (default: HEAD), plus untracked Lean files",
    )
    arg_parser.add_argument(
        "--jobs",
        type=int,
        default=default_jobs(),
        help="maximum concurrent Lean processes (default: environment/host-derived)",
    )
    arg_parser.add_argument("--project-root", type=Path, default=Path(__file__).resolve().parents[1])
    arg_parser.add_argument("--lake", default="lake", help="Lake executable (default: lake)")
    arg_parser.add_argument(
        "--plan",
        action="store_true",
        help="print compact stale topological-wave sizes without building",
    )
    arg_parser.add_argument(
        "--verbose-plan",
        action="store_true",
        help="print every module in the plan; implies --plan",
    )
    arg_parser.add_argument(
        "--lake-staleness",
        action="store_true",
        help="use Lake content traces for restored outputs instead of checkout mtimes",
    )
    arg_parser.add_argument("--no-final-build", action="store_true", help="skip the final ordinary Lake authority check")
    arg_parser.add_argument(
        "--materialize-dependencies",
        nargs="*",
        metavar="PACKAGE",
        default=None,
        help=(
            "governed dependency materialization instead of a build: under the host build "
            "lock run `lake update <PACKAGE...>` (omit packages to keep the manifest) and "
            "then `lake exe cache get` in --project-root. This is the only sanctioned way "
            "to fetch a new Mathlib revision outside the canonical checkout, because the "
            "build firewall terminates ungoverned materializers"
        ),
    )
    arg_parser.add_argument(
        "--no-singleflight",
        action="store_true",
        help=argparse.SUPPRESS,
    )
    arg_parser.add_argument(
        "--wait-if-duplicate",
        action="store_true",
        help=(
            "retired attached-wait option; requests are rejected with a typed manual-reinvoke "
            "handoff so an agent never stays alive to supervise a build queue"
        ),
    )
    arg_parser.add_argument(
        "--capacity-wait-seconds",
        type=float,
        default=0,
        help=(
            "retired for attached callers; values above zero are rejected. The default 0 returns "
            "exit 75 immediately with an exact operator reinvocation command"
        ),
    )
    return arg_parser


def main(argv: list[str] | None = None) -> int:
    raw_argv = list(argv) if argv is not None else list(sys.argv[1:])
    args = parser().parse_args(raw_argv)
    if args.jobs < 1:
        raise SystemExit("--jobs must be at least 1")
    if args.verbose_plan:
        args.plan = True
    project_root = args.project_root.resolve()
    if args.no_singleflight and not (
        os.environ.get(CONTROL_PLANE_CHILD_ENV) == "1"
        and bool(os.environ.get(RESOURCE_LEASE_TOKEN_ENV))
    ):
        emit_internal_singleflight_rejection(project_root)
        return 64
    if args.wait_if_duplicate or float(args.capacity_wait_seconds or 0) > 0:
        emit_attached_wait_rejection(args, project_root)
        return 64
    if args.changed_from is not None:
        if args.targets:
            print(
                "lean-fast-build: positional targets and --changed-from are mutually exclusive",
                file=sys.stderr,
            )
            return 64
        try:
            changed_paths = changed_lean_paths(args.changed_from, project_root)
        except RuntimeError as error:
            print(f"lean-fast-build: {error}", file=sys.stderr)
            return 64
        if not changed_paths:
            print(f"lean-fast-build: no changed Lean modules relative to {args.changed_from}")
            return 0
        modules = discover_modules(project_root)
        changed = changed_modules_from_paths(changed_paths, modules, project_root)
        if not changed:
            print(f"lean-fast-build: no changed local Lean modules relative to {args.changed_from}")
            return 0
        # Freeze the Git-derived set into explicit targets before singleflight
        # and capacity admission so retries use the same local partition.
        args.targets = [f"+{module}" for module in changed]
        args.changed_from = None
    root_targets, focused_targets = mixed_root_and_focused_targets(project_root, args.targets)
    if root_targets and focused_targets:
        print(
            json.dumps(
                {
                    "schema": "lean_fast_build_invalid_target_mix_v0",
                    "status": "rejected_redundant_root_target",
                    "proof_scope": "not_proof_evidence",
                    "root_targets": root_targets,
                    "focused_targets": focused_targets,
                    "exit_code": 64,
                    "next_action": "run_focused_targets_only_and_leave_root_integration_separate",
                },
                sort_keys=True,
            ),
            file=sys.stderr,
        )
        return 64
    if args.plan:
        return _main_admitted(args, project_root)
    load_control_plane()
    if private_control_plane_required(project_root) and (
        command_run_singleflight is None
        or resource_capacity_broker is None
        or command_future is None
    ):
        emit_private_control_plane_rejection(project_root)
        return 69
    admission = disk_admission(project_root)
    if not bool(admission["allow"]):
        future = submit_deferred_build_future(args, project_root, repository_root(project_root))
        emit_low_disk_deferred_turn_handoff(args, project_root, admission, future)
        return 75
    if args.materialize_dependencies is not None:
        return materialize_dependencies(args, project_root)
    cache_admission = admit_workspace_dependency_cache(project_root)
    cache_action = str(cache_admission.get("action") or "")
    if cache_action in {"reject", "defer"}:
        emit_workspace_cache_admission(cache_admission)
        default_exit = 75 if cache_action == "defer" else 64
        return int(cache_admission.get("exit_code") or default_exit)
    if cache_action == "attached":
        emit_workspace_cache_admission(cache_admission)
    broker_root = control_plane_root(project_root)
    conflict_keys = build_conflict_keys(project_root, broker_root)
    build_identity = semantic_build_identity(
        project_root,
        args.targets,
        no_final_build=bool(args.no_final_build),
        lake=str(args.lake),
    )
    if command_run_singleflight is not None and not args.no_singleflight:
        command = [
            sys.executable,
            str(Path(__file__).resolve()),
            *inner_build_argv(args, project_root),
        ]
        inner_env = os.environ.copy()
        inner_env[CONTROL_PLANE_CHILD_ENV] = "1"
        inner_env["AIW_PLECTIS_LEAN_HOST_LOCK_HELD"] = "1"
        host_lock, _host_lock_path = try_public_lean_host_lock()
        if host_lock is None:
            future = submit_deferred_build_future(args, project_root, broker_root)
            emit_deferred_turn_handoff(args, project_root, broker_root, future)
            return resource_capacity_broker.DEFER_EXIT_CODE
        try:
            result = command_run_singleflight.run_command_singleflight(
                broker_root,
                argv=command,
                cwd=project_root,
                resource_class="lean_build",
                owner_surface="lean_fast_build.py",
                scope_paths=singleflight_scope_paths(project_root, broker_root, args.targets),
                semantic_identity=build_identity,
                reuse_completed=True,
                reuse_completed_exit_codes=(0,),
                requested_seats=args.jobs,
                conflict_keys=conflict_keys,
                capacity_wait_seconds=0,
                active_wait_mode="defer",
                env=inner_env,
            )
        finally:
            fcntl.flock(host_lock.fileno(), fcntl.LOCK_UN)
            host_lock.close()
        if result == resource_capacity_broker.DEFER_EXIT_CODE:
            future = submit_deferred_build_future(args, project_root, broker_root)
            emit_deferred_turn_handoff(args, project_root, broker_root, future)
        return result
    # Normal private executions reach this branch only inside the semantic
    # singleflight child, after the project/dependency/host conflict keys are
    # held. Restoring before that lease would race a build in the same target.
    restore = restore_compatible_build_artifacts(project_root, build_identity)
    if restore.get("action") == "restored":
        args.lake_staleness = True
        print(json.dumps(restore, sort_keys=True))
    capacity = None
    previous_env: dict[str, str | None] = {}
    if resource_capacity_broker is not None:
        capacity = resource_capacity_broker.acquire_capacity(
            broker_root,
            work_key="lean-fast-build:" + ",".join(args.targets or [project_root.name]),
            resource_class="lean_build",
            owner_surface="lean_fast_build.py",
            flow_id=resource_capacity_broker.derive_flow_id("lean-fast-build", env=os.environ),
            requested_seats=args.jobs,
            conflict_keys=conflict_keys,
            env=os.environ,
        )
        if capacity.get("decision") == "DEFER":
            ticket = capacity.get("ticket") or {}
            print(f"lean-fast-build: capacity deferred; ticket={ticket.get('ticket_id')}", file=sys.stderr)
            future = submit_deferred_build_future(args, project_root, broker_root)
            emit_deferred_turn_handoff(args, project_root, broker_root, future)
            return resource_capacity_broker.DEFER_EXIT_CODE
        args.jobs = min(args.jobs, int(capacity.get("child_process_budget") or args.jobs))
        lease_env = resource_capacity_broker.lease_environment(capacity)
        previous_env = {name: os.environ.get(name) for name in lease_env}
        os.environ.update(lease_env)

    exit_code: int | None = None
    try:
        exit_code = _main_admitted(args, project_root)
        return exit_code
    finally:
        for name, value in previous_env.items():
            if value is None:
                os.environ.pop(name, None)
            else:
                os.environ[name] = value
        if resource_capacity_broker is not None and capacity is not None:
            resource_capacity_broker.release_capacity(
                broker_root,
                capacity,
                outcome="completed" if exit_code is not None else "build_failed",
                exit_code=exit_code,
            )


def repository_root(project_root: Path) -> Path:
    return next(
        (parent for parent in (project_root, *project_root.parents) if (parent / ".git").exists()),
        project_root,
    )


def control_plane_root(project_root: Path) -> Path:
    """Use one private broker root even when the guarded project is external.

    A project-local broker cannot see a sibling repository, so identical
    Mathlib builds in the private and standalone checkouts used to acquire
    independent leases. The private wrapper owns the host control plane; its
    repository therefore owns every cross-repository lease and receipt.
    """

    candidate = Path(__file__).resolve().parents[3]
    if all(
        (candidate / relative).is_file()
        for relative in (
            "system/lib/command_run_singleflight.py",
            "system/lib/resource_capacity_broker.py",
        )
    ):
        return candidate
    return repository_root(project_root)


def private_control_plane_required(project_root: Path) -> bool:
    """Return true when this checkout carries the ai_workflow safety runtime."""

    repo_root = repository_root(project_root)
    return all(
        (repo_root / relative).is_file()
        for relative in (
            "system/lib/command_run_singleflight.py",
            "system/lib/resource_capacity_broker.py",
        )
    )


def project_build_conflict_key(project_root: Path, repo_root: Path) -> str:
    """Name the shared mutable Lake build tree independently of the requested target."""

    try:
        identity = project_root.resolve().relative_to(repo_root.resolve()).as_posix()
    except ValueError:
        identity = project_root.resolve().as_posix()
    return f"lean-project-build:{identity}"


def dependency_cache_conflict_key(project_root: Path) -> str:
    """Name the semantic dependency cache shared by compatible workspaces."""

    try:
        toolchain = (project_root / "lean-toolchain").read_text(encoding="utf-8").strip()
        payload = json.loads(
            (project_root / "lake-manifest.json").read_text(encoding="utf-8")
        )
        packages = sorted(
            {
                (
                    str(row.get("name") or ""),
                    str(row.get("type") or ""),
                    str(row.get("url") or ""),
                    str(row.get("rev") or ""),
                )
                for row in payload.get("packages", [])
                if isinstance(row, dict)
            }
        )
        encoded = json.dumps(
            {"toolchain": toolchain, "packages": packages},
            sort_keys=True,
            separators=(",", ":"),
        ).encode("utf-8")
        fingerprint = hashlib.sha256(encoded).hexdigest()
    except (OSError, json.JSONDecodeError, TypeError):
        fingerprint = hashlib.sha256(str(project_root.resolve()).encode("utf-8")).hexdigest()
    return f"lean-dependency-cache:{fingerprint}"


def build_conflict_keys(project_root: Path, broker_root: Path) -> list[str]:
    return [
        project_build_conflict_key(project_root, broker_root),
        dependency_cache_conflict_key(project_root),
        HOST_MATHLIB_BUILD_CONFLICT_KEY,
    ]


def emit_private_control_plane_rejection(project_root: Path) -> None:
    """Fail closed when the private checkout cannot import its resource guards."""

    print(
        json.dumps(
            {
                "schema": "lean_fast_build_private_control_plane_required_v0",
                "status": "rejected_missing_private_control_plane",
                "validation_state": "not_started",
                "proof_scope": "not_proof_evidence",
                "exit_code": 69,
                "project_root": str(project_root),
                "required_modules": [
                    "system.lib.command_run_singleflight",
                    "system.lib.resource_capacity_broker",
                ],
                "next_action": "run_through_repo_python_from_repository_root",
                "forbidden_action": "standalone_interpreter_resource_guard_bypass",
            },
            sort_keys=True,
        ),
        file=sys.stderr,
    )


def emit_internal_singleflight_rejection(project_root: Path) -> None:
    """Reject direct use of the child-only recursion flag."""

    print(
        json.dumps(
            {
                "schema": "lean_fast_build_internal_flag_rejected_v0",
                "status": "rejected_internal_singleflight_flag",
                "validation_state": "not_started",
                "proof_scope": "not_proof_evidence",
                "exit_code": 64,
                "project_root": str(project_root),
                "next_action": "remove_internal_flag_and_use_normal_wrapper_entry",
                "forbidden_action": "direct_singleflight_bypass",
            },
            sort_keys=True,
        ),
        file=sys.stderr,
    )


def operator_reinvoke_argv(args: argparse.Namespace, project_root: Path) -> list[str]:
    """Return the exact non-waiting command an operator can invoke later."""

    values = [
        sys.executable,
        str(Path(__file__).resolve()),
        *list(args.targets or []),
        "--jobs",
        str(args.jobs),
        "--project-root",
        str(project_root),
        "--lake",
        str(args.lake),
    ]
    if args.no_final_build:
        values.append("--no-final-build")
    if args.lake_staleness:
        values.append("--lake-staleness")
    return values


def detached_requeue_argv(
    args: argparse.Namespace,
    project_root: Path,
    broker_root: Path,
) -> list[str]:
    """Return a detached future command that waits without occupying an agent."""

    values = [
        "./repo-python",
        "-m",
        "system.lib.command_future",
        "--repo-root",
        str(broker_root),
        "submit",
        "--cwd",
        str(project_root),
        "--resource-class",
        "lean_build",
        "--owner-surface",
        "lean_fast_build.py",
        "--requested-seats",
        str(args.jobs),
        "--reuse-completed-success-only",
        "--capacity-wait-seconds",
        str(24 * 60 * 60),
        "--retry-child-defer-seconds",
        str(30),
        "--dependency-barrier-reason",
        "Lean validation is queued behind the current host build owner",
    ]
    if os.environ.get("CODEX_THREAD_ID"):
        values.append("--wake-codex")
    for conflict_key in build_conflict_keys(project_root, broker_root):
        values.extend(["--conflict-key", conflict_key])
    for scope_path in singleflight_scope_paths(project_root, broker_root, args.targets):
        values.extend(["--scope-path", scope_path])
    values.extend(["--", *operator_reinvoke_argv(args, project_root)])
    return values


def submit_deferred_build_future(
    args: argparse.Namespace,
    project_root: Path,
    broker_root: Path,
) -> dict[str, object]:
    """Transfer deferred validation to a detached, capacity-waiting owner."""

    inherited_job_id = str(os.environ.get("AIW_COMMAND_FUTURE_JOB_ID") or "").strip()
    if inherited_job_id:
        return {
            "schema": "lean_fast_build_auto_future_v0",
            "status": "owned_by_current_command_future",
            "validation_state": "pending",
            "proof_scope": "not_proof_evidence",
            "job_id": inherited_job_id,
            "mode": "automatic_retry_owned",
        }
    if command_future is None:
        return {
            "schema": "lean_fast_build_auto_future_v0",
            "status": "unavailable_missing_control_plane",
            "validation_state": "pending",
            "proof_scope": "not_proof_evidence",
        }
    receipt = command_future.submit_command_future(
        broker_root,
        argv=operator_reinvoke_argv(args, project_root),
        cwd=project_root,
        resource_class="lean_build",
        owner_surface="lean_fast_build.py:auto_future",
        scope_paths=singleflight_scope_paths(project_root, broker_root, args.targets),
        requested_seats=args.jobs,
        conflict_keys=build_conflict_keys(project_root, broker_root),
        inline_budget_ms=50,
        capacity_wait_seconds=24 * 60 * 60,
        retry_child_defer_seconds=30,
        reuse_completed_success_only=True,
        dependency_barrier_reason=(
            "Lean validation owns its durable continuation while the caller advances "
            "result-independent work"
        ),
    )
    return {
        "schema": "lean_fast_build_auto_future_v0",
        "status": "submitted",
        "validation_state": "pending",
        "proof_scope": "not_proof_evidence",
        "job_id": receipt.get("job_id"),
        "mode": receipt.get("mode"),
        "submission": receipt,
    }


def emit_attached_wait_rejection(args: argparse.Namespace, project_root: Path) -> None:
    repo_root = repository_root(project_root)
    reinvoke_argv = operator_reinvoke_argv(args, project_root)
    print(
        json.dumps(
            {
                "schema": "lean_fast_build_attached_wait_rejected_v0",
                "status": "rejected_attached_build_wait",
                "validation_state": "not_started",
                "proof_scope": "not_proof_evidence",
                "exit_code": 64,
                "requested_wait_if_duplicate": bool(args.wait_if_duplicate),
                "requested_capacity_wait_seconds": float(args.capacity_wait_seconds or 0),
                "project_conflict_key": project_build_conflict_key(project_root, repo_root),
                "turn_action": "run_ready_disjoint_work_then_end_turn",
                "operator_action": "manually_reinvoke_after_project_build_lease_clears",
                "reinvoke_argv": reinvoke_argv,
                "reinvoke_command": shlex.join(reinvoke_argv),
            },
            sort_keys=True,
        ),
        file=sys.stderr,
    )


def emit_deferred_turn_handoff(
    args: argparse.Namespace,
    project_root: Path,
    repo_root: Path,
    future: dict[str, object],
) -> None:
    """Make exit 75 a terminal agent-turn state with an exact re-entry edge."""

    conflict_key = project_build_conflict_key(project_root, repo_root)
    reinvoke_argv = operator_reinvoke_argv(args, project_root)
    detached_argv = detached_requeue_argv(args, project_root, repo_root)
    print(
        json.dumps(
            {
                "schema": "lean_fast_build_deferred_turn_handoff_v0",
                "status": "validation_queued_automatically",
                "validation_state": "pending",
                "proof_scope": "not_proof_evidence",
                "exit_code": resource_capacity_broker.DEFER_EXIT_CODE,
                "project_conflict_key": conflict_key,
                "turn_action": "finish_ready_disjoint_work_then_end_turn",
                "operator_action": "none",
                "automatic_future": future,
                "reentry_condition": "automatic_future_reaches_terminal_state",
                "reinvoke_argv": reinvoke_argv,
                "reinvoke_command": shlex.join(reinvoke_argv),
                "detached_requeue_argv": detached_argv,
                "detached_requeue_command": shlex.join(detached_argv),
                "forbidden_actions": [
                    "attached_capacity_wait",
                    "retry_loop",
                    "ticket_polling",
                    "raw_lake_bypass",
                ],
            },
            sort_keys=True,
        ),
        file=sys.stderr,
    )


def emit_low_disk_deferred_turn_handoff(
    args: argparse.Namespace,
    project_root: Path,
    admission: dict[str, int | bool | str],
    future: dict[str, object],
) -> None:
    """Explain a firewall-equivalent prelaunch refusal as deferred validation."""

    repo_root = repository_root(project_root)
    reinvoke_argv = operator_reinvoke_argv(args, project_root)
    conflict_key = project_build_conflict_key(project_root, repo_root)
    print(
        json.dumps(
            {
                "schema": "lean_fast_build_low_disk_deferred_v0",
                "status": "validation_queued_automatically_low_disk",
                "validation_state": "pending",
                "proof_scope": "not_proof_evidence",
                "exit_code": 75,
                "reason": admission["reason"],
                "free_bytes": admission["free_bytes"],
                "minimum_free_bytes": admission["minimum_free_bytes"],
                "launch_reserve_bytes": admission.get("launch_reserve_bytes", 0),
                "minimum_launch_free_bytes": admission.get(
                    "minimum_launch_free_bytes", admission["minimum_free_bytes"]
                ),
                "minimum_source": admission["minimum_source"],
                "project_conflict_key": conflict_key,
                "turn_action": "stop_build_retries_and_continue_non_build_work",
                "operator_action": "none",
                "automatic_future": future,
                "reentry_condition": (
                    f"free_bytes >= {admission.get('minimum_launch_free_bytes', admission['minimum_free_bytes'])} "
                    "after Storage Doctor pressure relief and no active owner holds "
                    f"{conflict_key}"
                ),
                "pressure_relief_command": (
                    "./repo-python -m tools.meta.storage_doctor clean --scope all --level caution "
                    "--smart --owner-check-completed --apply --yes --format card"
                ),
                "reinvoke_argv": reinvoke_argv,
                "reinvoke_command": shlex.join(reinvoke_argv),
                "forbidden_actions": [
                    "retry_loop",
                    "raw_lake_bypass",
                    "infer_coagent_contention_without_firewall_receipt",
                ],
            },
            sort_keys=True,
        ),
        file=sys.stderr,
    )


def inner_build_argv(args: argparse.Namespace, project_root: Path) -> list[str]:
    """Canonicalize only build-semantic arguments for singleflight identity."""

    values = [
        *list(args.targets or []),
        "--jobs",
        str(args.jobs),
        "--project-root",
        str(project_root),
        "--lake",
        str(args.lake),
    ]
    if args.no_final_build:
        values.append("--no-final-build")
    if args.lake_staleness:
        values.append("--lake-staleness")
    values.append("--no-singleflight")
    return values


def singleflight_scope_paths(
    project_root: Path,
    repo_root: Path,
    targets: Iterable[str],
) -> list[str]:
    """Fingerprint the exact local import partition used by a focused build."""

    modules = discover_modules(project_root)
    requested = list(targets) or sorted(
        name for name, source in modules.items() if source.parent == project_root
    )
    roots = [module for target in requested if (module := target_module(target, project_root, modules))]
    selected = reachable_modules(roots, import_graph(modules)) if roots else set()
    paths = [modules[module] for module in sorted(selected)]
    paths.extend(
        project_root / name
        for name in ("lakefile.toml", "lakefile.lean", "lake-manifest.json", "lean-toolchain")
        if (project_root / name).is_file()
    )
    if not paths:
        paths = [project_root]
    scoped: list[str] = []
    for path in paths:
        try:
            scoped.append(str(path.resolve().relative_to(repo_root.resolve())))
        except ValueError:
            scoped.append(str(path.resolve()))
    return sorted(dict.fromkeys(scoped))


def _content_sha256(path: Path) -> str:
    digest = hashlib.sha256()
    with path.open("rb") as handle:
        for chunk in iter(lambda: handle.read(1024 * 1024), b""):
            digest.update(chunk)
    return digest.hexdigest()


def semantic_build_identity(
    project_root: Path,
    targets: Iterable[str],
    *,
    no_final_build: bool,
    lake: str = "lake",
) -> dict[str, object]:
    """Describe proof-relevant build input without checkout-local paths.

    This identity is deliberately stricter than a Git revision.  It hashes the
    complete reachable local source cone, exact Lake configuration, pinned
    dependency state, toolchain, requested logical roots/facets, and authority
    mode.  Two worktrees may therefore share a successful validation result,
    while any source/config/dependency difference forces a fresh build.
    """

    project_root = project_root.resolve()
    modules = discover_modules(project_root)
    requested = list(targets) or sorted(
        name for name, source in modules.items() if source.parent == project_root
    )
    target_rows: list[dict[str, str]] = []
    roots: list[str] = []
    for target in requested:
        module = target_module(target, project_root, modules)
        _target, facet = split_target_facet(target)
        if module is None:
            target_rows.append({"target": target, "module": "", "facet": facet or "default"})
            continue
        roots.append(module)
        target_rows.append(
            {"target": module, "module": module, "facet": facet or "default"}
        )
    selected = (
        reachable_modules(roots, import_graph(modules)) if roots else set(modules)
    )
    source_rows = [
        {
            "module": module,
            "bytes": modules[module].stat().st_size,
            "sha256": _content_sha256(modules[module]),
        }
        for module in sorted(selected)
    ]
    config_rows = []
    for name in ("lakefile.toml", "lakefile.lean", "lean-toolchain"):
        path = project_root / name
        if path.is_file():
            config_rows.append(
                {"name": name, "bytes": path.stat().st_size, "sha256": _content_sha256(path)}
            )
    resolved_lake = Path(lake).expanduser()
    if not resolved_lake.is_absolute():
        located = shutil.which(lake)
        resolved_lake = Path(located) if located else resolved_lake
    lake_driver = {
        "name": resolved_lake.name,
        "sha256": _content_sha256(resolved_lake.resolve())
        if resolved_lake.is_file()
        else "unresolved",
    }
    return {
        "schema": "lean_semantic_build_identity_v1",
        "dependency_cache_key": dependency_cache_conflict_key(project_root),
        "targets": sorted(target_rows, key=lambda row: (row["module"], row["target"], row["facet"])),
        "sources": source_rows,
        "config": config_rows,
        "lake_driver": lake_driver,
        "environment": {
            name: os.environ.get(name, "")
            for name in (
                "LEAN_PATH",
                "LEAN_SRC_PATH",
                "LAKE_HOME",
                "LEAN_OPTS",
                "LAKE_OPTS",
            )
        },
        "final_authority_check": not no_final_build,
    }


def compact_reconstructable_build_metadata(project_root: Path) -> dict[str, object]:
    """Compress Lake setup manifests without changing their visible bytes."""

    if str(os.environ.get("AIW_LEAN_DISABLE_ARTIFACT_COMPACTION") or "").lower() in {
        "1",
        "true",
        "yes",
        "on",
    }:
        return {"status": "disabled_by_environment"}
    try:
        from tools.meta import lean_build_cache

        receipt = lean_build_cache.compact_workspace_setup_json(
            project_root,
            include_dependency_packages=True,
        )
    except Exception as exc:  # Disk hygiene must never rewrite proof truth.
        receipt = {
            "schema": "lean_setup_json_compaction_receipt_v1",
            "status": "compaction_failed_validation_unchanged",
            "error": f"{type(exc).__name__}: {exc}",
        }
    print(json.dumps(receipt, sort_keys=True))
    return receipt


def _main_admitted(args: argparse.Namespace, project_root: Path) -> int:
    modules = discover_modules(project_root)
    targets = args.targets or sorted(name for name, source in modules.items() if source.parent == project_root)
    roots = [module for target in targets if (module := target_module(target, project_root, modules))]
    prebuild_facet = common_prebuild_facet(targets)
    if not roots:
        print("lean-fast-build: no local module target resolved; delegating directly to Lake")
        if args.plan or args.no_final_build:
            return 0
        result = run_final_authority_check(project_root, args.lake, targets)
        if result == 0:
            compact_reconstructable_build_metadata(project_root)
        return result

    graph = reachable_import_graph(roots, modules)
    selected = reachable_modules(roots, graph)
    waves = topological_waves(selected, graph)
    use_lake_staleness = args.lake_staleness and all(
        olean_path(project_root, module).exists() for module in roots
    )
    if args.lake_staleness and not use_lake_staleness:
        print("lean-fast-build: no complete restored target cache; using mtime planner")
    if use_lake_staleness:
        # A current root proves its complete local import cone is current, so
        # cache-hit checks need one Lake trace query rather than one per wave.
        stale_waves = (
            []
            if lake_targets_up_to_date(
                project_root,
                args.lake,
                roots,
                facet=prebuild_facet,
            )
            else [
                lake_stale_modules(
                    project_root,
                    args.lake,
                    wave,
                    facet=prebuild_facet,
                )
                for wave in waves
            ]
        )
    else:
        output_mtimes: dict[str, int | None] = {}
        config_mtime = project_config_mtime_ns(project_root)
        stale_waves = [
            [
                module
                for module in wave
                if module_is_stale(
                    project_root,
                    module,
                    modules,
                    graph,
                    cached_olean_mtimes=output_mtimes,
                    cached_config_mtime_ns=config_mtime,
                )
            ]
            for wave in waves
        ]
    stale_waves = [wave for wave in stale_waves if wave]
    print(
        f"lean-fast-build: partition={len(selected)}/{len(modules)} local modules for "
        f"{len(roots)} root(s); {sum(map(len, stale_waves))} stale/missing across "
        f"{len(stale_waves)} wave(s); jobs={args.jobs}; "
        f"staleness={'lake-trace' if use_lake_staleness else 'mtime'}"
    )
    if args.plan:
        for line in plan_lines(stale_waves, verbose=args.verbose_plan):
            print(line)
        return 0

    for wave in stale_waves:
        current = (
            lake_stale_modules(
                project_root,
                args.lake,
                wave,
                facet=prebuild_facet,
            )
            if use_lake_staleness
            else [module for module in wave if module_is_stale(project_root, module, modules, graph)]
        )
        build_wave(
            project_root,
            args.lake,
            current,
            args.jobs,
            facet=prebuild_facet,
        )

    if args.no_final_build:
        compact_reconstructable_build_metadata(project_root)
        return 0
    print("lean-fast-build: final serialized Lake authority check")
    result = run_final_authority_check(project_root, args.lake, targets)
    if result == 0:
        compact_reconstructable_build_metadata(project_root)
        seed = publish_compatible_build_artifacts(
            project_root,
            semantic_build_identity(
                project_root,
                targets,
                no_final_build=False,
                lake=str(args.lake),
            ),
        )
        print(json.dumps(seed, sort_keys=True))
    return result


if __name__ == "__main__":
    sys.exit(main())
