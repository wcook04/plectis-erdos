#!/usr/bin/env python3
"""Build stale local Lean modules with bounded memory, then verify with Lake.

The optional targets may be module names or ``.lean`` paths. With no targets,
each supported public root is built serially. Focused targets keep the
edit/test loop from paying for every public certificate module while preserving
a bounded Lake authority check. ``--changed-from`` derives those focused
targets from Git, including untracked Lean files. ``--lake-staleness`` asks
Lake's content-trace checker to validate restored CI outputs instead of using
checkout mtimes, which are new on every GitHub runner.

``--plan`` reports compact dependency-wave sizes. Add ``--verbose-plan`` when
the exact module names are needed for diagnosis.
"""

from __future__ import annotations

import argparse
import os
from pathlib import Path
import re
import subprocess
import sys
import time
from typing import Iterable

import validation_singleflight as singleflight


ROOT = Path(__file__).resolve().parents[1]
TOOLCHAIN_BIN = Path.home() / ".elan" / "bin"
LAKE = TOOLCHAIN_BIN / "lake"
IMPORT_RE = re.compile(r"^\s*import\s+([A-Za-z0-9_'.]+)\s*(?:--.*)?$")
GIT_COMMAND_TIMEOUT_SECONDS = singleflight.GIT_COMMAND_TIMEOUT_SECONDS
LAKE_COMMAND_TIMEOUT_SECONDS = singleflight.DEFAULT_WORKER_TIMEOUT_SECONDS


def lake_command(*arguments: str) -> list[str]:
    """Build a Lake argv with the canonical installed toolchain executable."""
    return [str(LAKE), *arguments]


def _run(
    command: list[str],
    *,
    cwd: Path,
    timeout_seconds: float,
    **kwargs: object,
) -> subprocess.CompletedProcess[str]:
    """Run Git/Lake without ambient selectors and with an explicit deadline."""
    return subprocess.run(
        command,
        cwd=cwd,
        env=singleflight.command_environment(),
        timeout=timeout_seconds,
        **kwargs,
    )


def default_jobs() -> int:
    configured = os.environ.get("LEAN_BUILD_JOBS")
    if configured:
        try:
            return max(1, int(configured))
        except ValueError:
            pass
    cpu_count = max(1, os.cpu_count() or 1)
    interactive_reserve = max(1, cpu_count // 4)
    return min(2, max(1, (cpu_count - interactive_reserve) // 2))


def module_name(source: Path, root: Path = ROOT) -> str:
    return ".".join(source.relative_to(root).with_suffix("").parts)


def discover(root: Path = ROOT) -> dict[str, Path]:
    modules: dict[str, Path] = {}
    for directory, dirnames, filenames in os.walk(root):
        # Prune .lake and other hidden trees before traversal; filtering after
        # Path.rglob still pays to enumerate the complete dependency cache.
        dirnames[:] = [name for name in dirnames if not name.startswith(".")]
        directory_path = Path(directory)
        module_prefix = directory_path.relative_to(root).parts
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
    """Read only the Lean header, where import commands are legal."""

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


def local_graph(modules: dict[str, Path]) -> dict[str, set[str]]:
    return {name: local_imports(source, modules) for name, source in modules.items()}


def reachable_graph(
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


def resolve_targets(
    targets: Iterable[str], modules: dict[str, Path], root: Path = ROOT
) -> list[str]:
    requested = list(targets) or default_root_targets(modules, root)
    resolved: list[str] = []
    for target in requested:
        candidate = target.removeprefix("+")
        if candidate in modules:
            resolved.append(candidate)
            continue
        target_path = (root / candidate).resolve()
        if target_path.suffix == ".lean":
            try:
                path_module = module_name(target_path, root.resolve())
            except ValueError:
                path_module = None
            if path_module in modules and modules[path_module].resolve() == target_path:
                resolved.append(path_module)
                continue
        raise ValueError(f"unknown local Lean target: {target}")
    return resolved


def default_root_targets(modules: dict[str, Path], root: Path = ROOT) -> list[str]:
    """Return the package roots without relying on Lake's unbounded default."""

    resolved_root = root.resolve()
    targets = sorted(
        name
        for name, source in modules.items()
        if source.parent.resolve() == resolved_root
    )
    if not targets:
        raise ValueError("no public root Lean modules found")
    return targets


def changed_lean_paths(base: str, root: Path = ROOT) -> set[Path]:
    """Return tracked or untracked Lean paths changed relative to ``base``."""

    commands = (
        ["git", "diff", "--name-only", "--diff-filter=ACMR", base, "--", "*.lean"],
        ["git", "ls-files", "--others", "--exclude-standard", "--", "*.lean"],
    )
    changed_paths: set[Path] = set()
    for command in commands:
        completed = _run(
            command,
            cwd=root,
            timeout_seconds=GIT_COMMAND_TIMEOUT_SECONDS,
            capture_output=True,
            text=True,
            check=False,
        )
        if completed.returncode:
            detail = completed.stderr.strip() or f"exit {completed.returncode}"
            raise RuntimeError(f"cannot resolve changed Lean targets: {detail}")
        changed_paths.update(
            (root / line).resolve()
            for line in completed.stdout.splitlines()
            if line.strip()
        )
    return changed_paths


def changed_targets_from_paths(
    changed_paths: Iterable[Path], modules: dict[str, Path], root: Path = ROOT
) -> list[str]:
    resolved_root = root.resolve()
    changed: set[str] = set()
    for path in changed_paths:
        resolved_path = path.resolve()
        try:
            name = module_name(resolved_path, resolved_root)
        except ValueError:
            continue
        if name in modules and modules[name].resolve() == resolved_path:
            changed.add(name)
    return sorted(changed)


def changed_targets(
    base: str, modules: dict[str, Path], root: Path = ROOT
) -> list[str]:
    """Return changed local Lean modules relative to ``base``."""

    return changed_targets_from_paths(changed_lean_paths(base, root), modules, root)


def reachable(roots: Iterable[str], graph: dict[str, set[str]]) -> set[str]:
    result: set[str] = set()
    stack = list(roots)
    while stack:
        item = stack.pop()
        if item not in result:
            result.add(item)
            stack.extend(graph[item])
    return result


def waves(selected: set[str], graph: dict[str, set[str]]) -> list[list[str]]:
    pending = set(selected)
    done: set[str] = set()
    result: list[list[str]] = []
    while pending:
        ready = sorted(name for name in pending if (graph[name] & selected) <= done)
        if not ready:
            raise RuntimeError("cycle in local Lean import graph")
        result.append(ready)
        done.update(ready)
        pending.difference_update(ready)
    return result


def olean(name: str, root: Path = ROOT) -> Path:
    return root / ".lake" / "build" / "lib" / "lean" / Path(*name.split(".")).with_suffix(".olean")


def file_mtime_ns(path: Path) -> int | None:
    try:
        return path.stat().st_mtime_ns
    except FileNotFoundError:
        return None


def project_config_mtime_ns(root: Path = ROOT) -> int | None:
    mtimes = [
        mtime
        for name in ("lakefile.toml", "lakefile.lean", "lake-manifest.json", "lean-toolchain")
        if (mtime := file_mtime_ns(root / name)) is not None
    ]
    return max(mtimes, default=None)


def olean_mtime_ns(
    name: str,
    root: Path = ROOT,
    cache: dict[str, int | None] | None = None,
) -> int | None:
    if cache is not None and name in cache:
        return cache[name]
    mtime = file_mtime_ns(olean(name, root))
    if cache is not None:
        cache[name] = mtime
    return mtime


def stale(
    name: str,
    modules: dict[str, Path],
    graph: dict[str, set[str]],
    root: Path = ROOT,
    *,
    cached_olean_mtimes: dict[str, int | None] | None = None,
    cached_config_mtime_ns: int | None = None,
) -> bool:
    timestamp = olean_mtime_ns(name, root, cached_olean_mtimes)
    if timestamp is None:
        return True
    if modules[name].stat().st_mtime_ns > timestamp:
        return True
    for dependency in graph[name]:
        dependency_timestamp = olean_mtime_ns(
            dependency, root, cached_olean_mtimes
        )
        if dependency_timestamp is None or dependency_timestamp > timestamp:
            return True
    config_timestamp = (
        cached_config_mtime_ns
        if cached_olean_mtimes is not None
        else project_config_mtime_ns(root)
    )
    return config_timestamp is not None and config_timestamp > timestamp


def lake_targets_up_to_date(
    names: Iterable[str],
    root: Path = ROOT,
    *,
    rehash: bool = True,
) -> bool:
    """Ask Lake whether a target batch is current without rebuilding it."""

    targets = list(names)
    if not targets:
        return True
    command = lake_command()
    if rehash:
        command.append("--rehash")
    command.extend(["--no-build", "build", *(f"+{name}" for name in targets)])
    result = _run(
        command,
        cwd=root,
        timeout_seconds=LAKE_COMMAND_TIMEOUT_SECONDS,
        stdout=subprocess.DEVNULL,
        stderr=subprocess.DEVNULL,
        check=False,
    )
    return result.returncode == 0


def lake_stale_targets(
    names: Iterable[str],
    root: Path = ROOT,
    *,
    rehash: bool = True,
) -> list[str]:
    """Return Lake's complete stale local-module set in one graph traversal.

    With ``--no-build -v``, Lake ends a failed authority check with a stable
    ``Some required targets logged failures`` list.  That list contains every
    stale module in the requested import closure, so parsing it avoids the
    former logarithmic bisection's repeated workspace and graph scans.  Fall
    back to bisection if a future Lake changes the diagnostic format.
    """

    targets = list(names)
    if not targets:
        return []
    command = lake_command()
    if rehash:
        command.append("--rehash")
    command.extend(["--no-build", "-v", "build", *(f"+{name}" for name in targets)])
    result = _run(
        command,
        cwd=root,
        timeout_seconds=LAKE_COMMAND_TIMEOUT_SECONDS,
        stdout=subprocess.PIPE,
        stderr=subprocess.STDOUT,
        text=True,
        check=False,
    )
    if result.returncode == 0:
        return []

    marker = "Some required targets logged failures:"
    if marker in result.stdout:
        failures = []
        for line in result.stdout.split(marker, 1)[1].splitlines():
            match = re.fullmatch(r"- ([A-Za-z0-9_.]+)", line.strip())
            if match:
                failures.append(match.group(1))
        if failures:
            return failures

    # Diagnostic compatibility fallback.  Do not rehash again: the failed
    # verbose query above has already refreshed Lake's content hashes.
    if len(targets) == 1:
        return targets
    midpoint = len(targets) // 2
    return lake_stale_targets(
        targets[:midpoint], root, rehash=False
    ) + lake_stale_targets(targets[midpoint:], root, rehash=False)


def propagate_stale_targets(
    initial: Iterable[str],
    build_waves: Iterable[Iterable[str]],
    graph: dict[str, set[str]],
) -> set[str]:
    """Expand a Lake stale frontier through all local import dependents."""

    stale = set(initial)
    for wave in build_waves:
        for name in wave:
            if name in stale or graph[name] & stale:
                stale.add(name)
    return stale


def build_one(name: str, root: Path = ROOT) -> tuple[str, int, float]:
    started = time.monotonic()
    result = _run(
        lake_command(
            "--quiet",
            "--no-ansi",
            "--log-level=error",
            "build",
            f"+{name}",
        ),
        cwd=root,
        timeout_seconds=LAKE_COMMAND_TIMEOUT_SECONDS,
        check=False,
    )
    return name, result.returncode, time.monotonic() - started


def build_batch(names: Iterable[str], root: Path = ROOT) -> tuple[int, float]:
    """Build a bounded target batch in one Lake graph traversal."""

    modules = list(names)
    if not modules:
        return 0, 0.0
    started = time.monotonic()
    result = _run(
        lake_command(
            "--quiet",
            "--no-ansi",
            "--log-level=error",
            "build",
            *(f"+{name}" for name in modules),
        ),
        cwd=root,
        timeout_seconds=LAKE_COMMAND_TIMEOUT_SECONDS,
        check=False,
    )
    return result.returncode, time.monotonic() - started


def build_wave(names: Iterable[str], jobs: int, root: Path = ROOT) -> list[str]:
    """Build one dependency wave in batches of at most ``jobs`` modules.

    Earlier dependency waves are already current, so Lake can elaborate at
    most the modules named in each batch. This preserves the memory/process
    ceiling while amortizing Lake's workspace and dependency-graph scan across
    up to ``jobs`` targets. A failed batch is retried one module at a time so
    the final diagnostic still names the exact failures.
    """

    modules = list(names)
    failed: list[str] = []
    if not modules:
        return failed
    print(
        f"lean-fast-build: prebuilding {len(modules)} module(s), "
        f"batches of at most {jobs}",
        flush=True,
    )
    for offset in range(0, len(modules), jobs):
        batch = modules[offset : offset + jobs]
        code, duration = build_batch(batch, root)
        label = ",".join(batch)
        print(
            f"lean-fast-build: [{label}] -> {code} ({duration:.1f}s)",
            flush=True,
        )
        if code:
            for name in batch:
                name, single_code, single_duration = build_one(name, root)
                print(
                    f"lean-fast-build: retry {name} -> {single_code} "
                    f"({single_duration:.1f}s)",
                    flush=True,
                )
                if single_code:
                    failed.append(name)
    return failed


def plan_lines(build_waves: Iterable[Iterable[str]], *, verbose: bool) -> list[str]:
    """Format a readable build plan without flooding normal terminals."""

    lines: list[str] = []
    for index, wave in enumerate(build_waves, 1):
        names = list(wave)
        detail = " ".join(names) if verbose else f"{len(names)} module(s)"
        lines.append(f"wave {index}: {detail}")
    return lines


def run_final_authority_check(
    targets: Iterable[str], root: Path = ROOT
) -> int:
    """Run focused authority checks serially to preserve the process bound."""

    target_list = list(targets)
    if not target_list:
        raise ValueError("final authority check requires at least one target")
    for name in target_list:
        result = _run(
            lake_command(
                "--quiet",
                "--no-ansi",
                "--log-level=error",
                "build",
                f"+{name}",
            ),
            cwd=root,
            timeout_seconds=LAKE_COMMAND_TIMEOUT_SECONDS,
            check=False,
        )
        if result.returncode:
            return result.returncode
    return 0


def main(argv: list[str] | None = None) -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument(
        "targets",
        nargs="*",
        help="local module name or .lean path; defaults to all supported public roots",
    )
    parser.add_argument(
        "--changed-from",
        nargs="?",
        const="HEAD",
        metavar="REF",
        help="build changed Lean modules relative to REF (default: HEAD), plus untracked Lean files",
    )
    parser.add_argument("--jobs", type=int, default=default_jobs())
    parser.add_argument("--plan", action="store_true")
    parser.add_argument(
        "--verbose-plan",
        action="store_true",
        help="print every module in the plan; implies --plan",
    )
    parser.add_argument(
        "--lake-staleness",
        action="store_true",
        help="use Lake content traces for restored outputs instead of checkout mtimes",
    )
    args = parser.parse_args(argv)
    if args.jobs < 1:
        parser.error("--jobs must be at least 1")
    if args.verbose_plan:
        args.plan = True

    root = ROOT
    try:
        if args.changed_from is not None:
            if args.targets:
                parser.error("positional targets and --changed-from are mutually exclusive")
            changed_paths = changed_lean_paths(args.changed_from, root)
            if not changed_paths:
                print(
                    f"lean-fast-build: no changed Lean modules relative to {args.changed_from}",
                    flush=True,
                )
                return 0
            modules = discover(root)
            target_modules = changed_targets_from_paths(changed_paths, modules, root)
            if not target_modules:
                print(
                    "lean-fast-build: no changed local Lean modules relative to "
                    f"{args.changed_from}",
                    flush=True,
                )
                return 0
        else:
            modules = discover(root)
            target_modules = resolve_targets(args.targets, modules, root)
    except (RuntimeError, ValueError) as error:
        parser.error(str(error))
    graph = reachable_graph(target_modules, modules)
    build_waves = waves(reachable(target_modules, graph), graph)
    use_lake_staleness = args.lake_staleness

    if use_lake_staleness:
        # One verbose Lake authority query reports the complete stale import
        # closure.  Partition that verdict into topological waves locally.
        stale_targets = propagate_stale_targets(
            lake_stale_targets(target_modules, root), build_waves, graph
        )
        pending = [
            [name for name in wave if name in stale_targets]
            for wave in build_waves
        ]
        pending = [wave for wave in pending if wave]
    else:
        output_mtimes: dict[str, int | None] = {}
        config_mtime = project_config_mtime_ns(root)
        pending = [
            [
                name
                for name in wave
                if stale(
                    name,
                    modules,
                    graph,
                    root,
                    cached_olean_mtimes=output_mtimes,
                    cached_config_mtime_ns=config_mtime,
                )
            ]
            for wave in build_waves
        ]
    pending = [wave for wave in pending if wave]
    print(
        f"lean-fast-build: targets={','.join(target_modules)}; "
        f"{sum(map(len, pending))} stale/missing module(s), jobs={args.jobs}, "
        f"staleness={'lake-trace' if use_lake_staleness else 'mtime'}",
        flush=True,
    )
    if args.plan:
        for line in plan_lines(pending, verbose=args.verbose_plan):
            print(line, flush=True)
        return 0

    for wave in pending:
        current = (
            wave
            if use_lake_staleness
            else [name for name in wave if stale(name, modules, graph, root)]
        )
        failed = build_wave(current, args.jobs, root)
        if failed:
            raise RuntimeError("module prebuild failed: " + ", ".join(sorted(failed)))

    print("lean-fast-build: final serialized Lake authority check", flush=True)
    return run_final_authority_check(target_modules, root)


if __name__ == "__main__":
    sys.exit(main())
