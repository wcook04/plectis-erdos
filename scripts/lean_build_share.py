#!/usr/bin/env python3
"""Share successful local Lean build outputs across equivalent cold clones.

The validation key fingerprints all visible Lean sources, but its command may
validate only one import closure. Publish and hydrate only artifacts belonging
to that selected closure: neither the broad key manifest nor a worker's entire
``.lake/build`` proves unrelated cached outputs current. Seeds remain acceleration
only; the normal Lake authority check still creates them.
"""

from __future__ import annotations

import hashlib
import io
import json
import os
from pathlib import Path
import secrets
import shutil
import subprocess
import sys
import tomllib
from collections import defaultdict
from typing import Any

import lean_package_share as package_share


SCHEMA = "public-lean-build-share/1"
SEED_DIRECTORY = "build-seeds"
DEFAULT_RETAINED_SEEDS = 2
MATERIALIZATION_MARKER = ".plectis-singleflight-key"


class BuildShareError(RuntimeError):
    """A build seed cannot be published or hydrated safely."""


def _is_key(value: str) -> bool:
    return len(value) == 64 and all(
        character in "0123456789abcdef" for character in value
    )


def _validated_key(key: str) -> str:
    if not _is_key(key):
        raise BuildShareError("build seed key must be a lowercase SHA-256 digest")
    return key


def seed_paths(state_root: Path, key: str) -> tuple[Path, Path]:
    key = _validated_key(key)
    root = state_root.expanduser().resolve() / SEED_DIRECTORY / key
    return root / "build", root / "seed.json"


def _remove_tree(path: Path) -> None:
    if path.is_symlink():
        raise BuildShareError(f"refusing to remove symbolic-link build seed: {path}")
    if path.exists():
        shutil.rmtree(path)


def _write_json(path: Path, payload: dict[str, Any]) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    temporary = path.with_name(f".{path.name}.{secrets.token_hex(8)}.tmp")
    temporary.write_text(
        json.dumps(payload, sort_keys=True, separators=(",", ":")) + "\n",
        encoding="utf-8",
    )
    os.replace(temporary, path)


def _load_seed(state_root: Path, key: str) -> Path | None:
    build, receipt_path = seed_paths(state_root, key)
    try:
        receipt = json.loads(receipt_path.read_text(encoding="utf-8"))
    except (OSError, json.JSONDecodeError):
        return None
    if (
        not isinstance(receipt, dict)
        or receipt.get("schema") != SCHEMA
        or receipt.get("key") != key
        or receipt.get("status") != "ready"
        or not build.is_dir()
        or build.is_symlink()
    ):
        return None
    return build


def _worker_targets(inputs: dict[str, Any]) -> list[str]:
    """Read the scheduler's canonical command without guessing unknown modes."""
    command = inputs.get("normalized_command")
    if not isinstance(command, list) or len(command) < 3 or not all(isinstance(arg, str) for arg in command):
        raise BuildShareError("missing normalized Lean worker command")
    if command[1] != "scripts/lean_fast_build.py" or "--singleflight-worker" not in command[2:]:
        raise BuildShareError("unsupported normalized Lean worker command")
    targets = []
    index = 2
    while index < len(command):
        argument = command[index]
        if argument in {"--singleflight-state-root", "--jobs"}:
            if index + 1 >= len(command) or command[index + 1].startswith("-"):
                raise BuildShareError("incomplete normalized worker option")
            if argument == "--jobs" and (not command[index + 1].isdigit() or int(command[index + 1]) < 1):
                raise BuildShareError("invalid normalized worker job count")
            index += 2
        elif argument in {"--singleflight-worker", "--lake-staleness"}:
            index += 1
        elif argument.startswith("-"):
            raise BuildShareError("unsupported normalized worker option")
        else:
            targets.append(argument)
            index += 1
    return targets


def _validated_modules(root: Path, state_root: Path, key: str) -> set[Path]:
    """Derive the selected import closure from command and hash-verified sources."""
    _validated_key(key)
    receipt = json.loads((state_root / "jobs" / f"{key}.json").read_text(encoding="utf-8"))
    if not isinstance(receipt, dict):
        raise BuildShareError("validation receipt has no keyed source scope")
    inputs = receipt.get("inputs", {})
    if not isinstance(inputs, dict) or not isinstance(inputs.get("relevant_sources"), list):
        raise BuildShareError("validation receipt has no keyed source scope")
    encoded = json.dumps(inputs, sort_keys=True, separators=(",", ":"), ensure_ascii=False).encode("utf-8")
    if receipt.get("key") != key or hashlib.sha256(encoded).hexdigest() != key:
        raise BuildShareError("build artifact scope does not match the validation key")
    if inputs.get("validation_class") != "lean":
        raise BuildShareError("build artifact scope requires a Lean validation receipt")
    rows = inputs.get("relevant_sources", [])
    source_rows = {row["path"]: row for row in rows if isinstance(row, dict) and isinstance(row.get("path"), str)}
    lakefile = root / "lakefile.toml"
    lake_bytes = lakefile.read_bytes()
    expected_lake_digest = "sha256:" + hashlib.sha256(lake_bytes).hexdigest()
    if not any(row.get("path") == "lakefile.toml" and row.get("sha256") == expected_lake_digest
               for row in rows if isinstance(row, dict)):
        raise BuildShareError("Lake source layout does not match the validation key")
    config = tomllib.loads(lake_bytes.decode("utf-8"))
    source_roots = {Path(".")}
    for library in config.get("lean_lib", []):
        if isinstance(library, dict) and isinstance(library.get("srcDir"), str):
            source_roots.add(Path(library["srcDir"]))
    if any(path.is_absolute() or ".." in path.parts for path in source_roots):
        raise BuildShareError("Lake source layout escapes the checkout")
    ordered_roots = sorted(source_roots, key=lambda path: len(path.parts), reverse=True)
    # Lazy import avoids the scheduler -> build-share -> fast-build import cycle.
    # Reuse the native resolver/header parser, but parse bytes already hashed here.
    import lean_fast_build as fast_build

    modules = {}
    for relative in source_rows:
        source = Path(relative)
        if source.is_absolute() or ".." in source.parts:
            raise BuildShareError("validation source path escapes the checkout")
        if source.suffix != ".lean" or source.name.startswith("_") or any(part.startswith(".") for part in source.parts):
            continue
        prefix = next(path for path in ordered_roots if source.is_relative_to(path))
        name = fast_build.module_name(source, prefix)
        if name in modules:
            raise BuildShareError("ambiguous keyed Lean module")
        modules[name] = root / source
    if not modules:
        raise BuildShareError("validation receipt has no Lean source closure")
    targets = _worker_targets(inputs)
    if not targets:
        # Use the already verified Lake configuration, not a second mutable read.
        targets = config.get("defaultTargets") or sorted(
            name for name, source in modules.items() if source.parent == root
        )
    if not isinstance(targets, list) or not targets or not all(isinstance(target, str) for target in targets):
        raise BuildShareError("no selected public root Lean modules")
    pending = fast_build.resolve_targets(targets, modules, root)
    # Direct source checks use `lake env lean` without emitting cache artifacts.
    # Their registered library imports are built and remain eligible for sharing.
    direct_targets = fast_build.direct_source_targets(pending, modules, root)
    selected = set()
    while pending:
        name = pending.pop()
        if name in selected:
            continue
        source = modules[name]
        if source.is_symlink() or not source.resolve().is_relative_to(root.resolve()):
            raise BuildShareError("selected source escapes checkout")
        data = source.read_bytes()
        expected = source_rows[source.relative_to(root).as_posix()].get("sha256")
        if "sha256:" + hashlib.sha256(data).hexdigest() != expected:
            raise BuildShareError("selected source differs from keyed bytes")
        selected.add(name)
        block_depth = 0
        for line in io.StringIO(data.decode("utf-8")):
            code, block_depth = fast_build.code_without_comments(line, block_depth)
            stripped = code.strip()
            if not stripped or stripped == "prelude":
                continue
            match = fast_build.IMPORT_RE.match(stripped)
            if not match:
                break
            imported = match.group(1)
            if imported in modules and imported not in selected:
                pending.append(imported)
            elif imported not in modules and any(
                (root / prefix / (imported.replace(".", "/") + ".lean")).is_file()
                for prefix in ordered_roots
            ):
                raise BuildShareError("local import has no keyed source")
    return {Path(*name.split(".")) for name in selected if name not in direct_targets}


def _module_artifacts(build: Path, modules: set[Path]) -> list[Path]:
    """Include module companions, not package-wide or unrelated cached outputs."""
    paths = []
    for prefix in (Path("lib/lean"), Path("ir")):
        for directory, _subdirs, filenames in os.walk(build / prefix):
            parent = Path(directory).relative_to(build / prefix)
            for filename in filenames:
                if "." not in filename or parent / filename.split(".", 1)[0] not in modules:
                    continue
                path = Path(directory) / filename
                if path.is_symlink() or not path.is_file():
                    raise BuildShareError("module build artifact is not a regular file")
                paths.append(path.relative_to(build))
    return sorted(paths)


def prune_seeds(
    state_root: Path,
    *,
    retain: int = DEFAULT_RETAINED_SEEDS,
    preserve_key: str | None = None,
) -> list[str]:
    root = state_root.expanduser().resolve() / SEED_DIRECTORY
    if not root.is_dir() or root.is_symlink():
        return []
    rows = sorted(
        (
            (child.stat().st_mtime_ns, child)
            for child in root.iterdir()
            if child.is_dir() and not child.is_symlink() and _is_key(child.name)
        ),
        reverse=True,
    )
    retained = {child.name for _, child in rows[: max(0, retain)]}
    if preserve_key:
        retained.add(_validated_key(preserve_key))
    removed: list[str] = []
    for _, child in rows:
        if child.name in retained:
            continue
        _validated_key(child.name)
        _remove_tree(child)
        removed.append(child.name)
    return removed


def publish(root: Path, state_root: Path, key: str) -> dict[str, Any]:
    """Publish one immutable CoW seed after a successful authoritative build."""

    source = root.resolve() / ".lake/build"
    if not source.is_dir() or source.is_symlink():
        return {"schema": SCHEMA, "status": "unavailable", "reason": "build_missing"}
    try:
        modules = _validated_modules(root.resolve(), state_root.resolve(), key)
        (source / MATERIALIZATION_MARKER).write_text(key + "\n", encoding="utf-8")
        existing = _load_seed(state_root, key)
    except (OSError, ValueError, BuildShareError) as exc:
        return {
            "schema": SCHEMA,
            "status": "unavailable",
            "reason": str(exc)[:300],
        }
    if existing is not None:
        return {"schema": SCHEMA, "status": "ready", "key": key, "reuse": "existing"}
    build, receipt_path = seed_paths(state_root, key)
    seed_root = build.parent
    seed_root.parent.mkdir(parents=True, exist_ok=True)
    stage = seed_root.with_name(f".{key}.{secrets.token_hex(8)}.tmp")
    _remove_tree(stage)
    stage.mkdir()
    try:
        artifacts = _module_artifacts(source, modules)
        _copy_contents(source, stage / "build", artifacts)
        _write_json(
            stage / "seed.json",
            {"schema": SCHEMA, "status": "ready", "key": key,
             "artifact_scope": "validated_lean_source_closure",
             "modules": sorted(path.as_posix() for path in modules)},
        )
        if seed_root.exists():
            _remove_tree(seed_root)
        os.replace(stage, seed_root)
    except (OSError, subprocess.TimeoutExpired, BuildShareError) as exc:
        _remove_tree(stage)
        return {
            "schema": SCHEMA,
            "status": "unavailable",
            "reason": str(exc)[:300],
        }
    try:
        removed = prune_seeds(state_root, preserve_key=key)
    except (OSError, BuildShareError) as exc:
        return {
            "schema": SCHEMA,
            "status": "ready",
            "key": key,
            "reuse": "published",
            "prune_warning": str(exc)[:300],
        }
    return {
        "schema": SCHEMA,
        "status": "ready",
        "key": key,
        "reuse": "published",
        "pruned_keys": removed,
    }


def _copy_contents(source: Path, target: Path, relative_paths: list[Path]) -> None:
    """Copy explicit module files in bounded CoW batches, preserving other files."""
    target.mkdir(parents=True, exist_ok=True)
    if sys.platform == "darwin" and Path("/bin/cp").is_file():
        command = ["/bin/cp", "-cp"]
    elif sys.platform.startswith("linux") and shutil.which("cp"):
        command = ["cp", "--reflink=always", "-p"]
    else:
        raise BuildShareError("copy-on-write build hydration is unavailable")
    groups: dict[Path, list[Path]] = defaultdict(list)
    for relative in relative_paths:
        if relative.is_absolute() or ".." in relative.parts:
            raise BuildShareError("build artifact path escapes its scope")
        destination = target / relative
        for path in (destination, *destination.parents):
            if path.is_symlink():
                raise BuildShareError("build artifact destination traverses a symbolic link")
            if path == target:
                break
        groups[relative.parent].append(source / relative)
    for parent, files in groups.items():
        destination = target / parent
        destination.mkdir(parents=True, exist_ok=True)
        for offset in range(0, len(files), 64):
            completed = subprocess.run(
                [*command, *(str(path) for path in files[offset:offset + 64]), str(destination)],
                capture_output=True,
                text=True,
                errors="replace",
                timeout=600,
                check=False,
            )
            if completed.returncode:
                raise BuildShareError(
                    f"copy-on-write build hydration failed: {completed.stderr.strip()[:300]}"
                )


def hydrate(root: Path, state_root: Path, key: str) -> dict[str, Any]:
    """Materialize only keyed module artifacts, including from legacy full seeds."""

    source = _load_seed(state_root, key)
    if source is None:
        return {"schema": SCHEMA, "status": "unavailable", "reason": "seed_missing"}
    target = root.resolve() / ".lake/build"
    if target.is_symlink():
        raise BuildShareError("mutable Lean build output must not be a symlink")
    try:
        modules = _validated_modules(root.resolve(), state_root.resolve(), key)
        _copy_contents(source, target, _module_artifacts(source, modules))
        (target / MATERIALIZATION_MARKER).write_text(key + "\n", encoding="utf-8")
    except (OSError, ValueError, subprocess.TimeoutExpired, BuildShareError) as exc:
        return {
            "schema": SCHEMA,
            "status": "unavailable",
            "reason": str(exc)[:300],
        }
    return {"schema": SCHEMA, "status": "hydrated", "key": key}


def is_materialized(root: Path, key: str) -> bool:
    """Return whether this checkout already carries the exact shared build."""

    _validated_key(key)
    marker = root.resolve() / ".lake/build" / MATERIALIZATION_MARKER
    try:
        return marker.is_file() and not marker.is_symlink() and marker.read_text(
            encoding="utf-8"
        ).strip() == key
    except OSError:
        return False
