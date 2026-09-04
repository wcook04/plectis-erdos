#!/usr/bin/env python3
"""Share successful local Lean build outputs across equivalent cold clones.

The validation key already proves that the visible Lean sources, toolchain, and
build authorities are identical.  This module makes the corresponding success
receipt useful in another checkout by retaining a bounded copy-on-write seed of
``.lake/build``.  Seeds are acceleration only; the normal Lake authority check
still creates them, and no mutable build directory is ever symlinked.
"""

from __future__ import annotations

import json
import os
from pathlib import Path
import secrets
import shutil
import subprocess
import sys
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
        receipt.get("schema") != SCHEMA
        or receipt.get("key") != key
        or receipt.get("status") != "ready"
        or not build.is_dir()
        or build.is_symlink()
    ):
        return None
    return build


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
        (source / MATERIALIZATION_MARKER).write_text(key + "\n", encoding="utf-8")
        existing = _load_seed(state_root, key)
    except OSError as exc:
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
        package_share.clone_tree(source, stage / "build")
        _write_json(
            stage / "seed.json",
            {"schema": SCHEMA, "status": "ready", "key": key},
        )
        if seed_root.exists():
            _remove_tree(seed_root)
        os.replace(stage, seed_root)
    except (OSError, package_share.PackageShareError) as exc:
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


def _copy_contents(source: Path, target: Path) -> None:
    target.mkdir(parents=True, exist_ok=True)
    if sys.platform == "darwin" and Path("/bin/cp").is_file():
        command = ["/bin/cp", "-cR", f"{source}/.", str(target)]
    elif sys.platform.startswith("linux") and shutil.which("cp"):
        command = ["cp", "--reflink=always", "-a", f"{source}/.", str(target)]
    else:
        raise BuildShareError("copy-on-write build hydration is unavailable")
    completed = subprocess.run(
        command,
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
    """Merge a matching CoW seed into one checkout's reconstructable output."""

    source = _load_seed(state_root, key)
    if source is None:
        return {"schema": SCHEMA, "status": "unavailable", "reason": "seed_missing"}
    target = root.resolve() / ".lake/build"
    if target.is_symlink():
        raise BuildShareError("mutable Lean build output must not be a symlink")
    try:
        _copy_contents(source, target)
        (target / MATERIALIZATION_MARKER).write_text(key + "\n", encoding="utf-8")
    except (OSError, subprocess.TimeoutExpired, BuildShareError) as exc:
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
