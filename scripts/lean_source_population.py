#!/usr/bin/env python3
# SPDX-FileCopyrightText: 2026 Will Cook
# SPDX-License-Identifier: Apache-2.0
"""Describe the complete current local Lean source population without Lean.

This module reuses ``lean_fast_build`` for source discovery and import parsing,
then exposes the graph-maximal roots whose closures cover every discovered
module.  It also checks that each configured Lake library has at least one
source matching its ``srcDir`` and ``globs`` declaration.  The result is a
read-only plan and content identity, not an elaboration verdict.
"""

from __future__ import annotations

import argparse
import fnmatch
import hashlib
import json
import os
from pathlib import Path
import tomllib
from types import ModuleType

import lean_fast_build


ROOT = Path(__file__).resolve().parents[1]


class SourcePopulationError(RuntimeError):
    """The local source population cannot form one complete acyclic plan."""


def sha256_bytes(data: bytes) -> str:
    return "sha256:" + hashlib.sha256(data).hexdigest()


def sha256_path(path: Path) -> str:
    digest = hashlib.sha256()
    with path.open("rb") as handle:
        for chunk in iter(lambda: handle.read(1024 * 1024), b""):
            digest.update(chunk)
    return "sha256:" + digest.hexdigest()


def _source_modules(src_dir: Path) -> list[str]:
    modules: list[str] = []
    if not src_dir.is_dir():
        return modules
    for directory, dirnames, filenames in os.walk(src_dir):
        dirnames[:] = [name for name in dirnames if not name.startswith(".")]
        prefix = Path(directory).relative_to(src_dir).parts
        modules.extend(
            ".".join((*prefix, filename.removesuffix(".lean")))
            for filename in filenames
            if filename.endswith(".lean") and not filename.startswith("_")
        )
    return modules


def declared_lean_library_inventory(root: Path = ROOT) -> dict[str, object]:
    """Resolve configured Lean libraries to sources under srcDir/globs."""

    lakefile = root / "lakefile.toml"
    if not lakefile.is_file():
        return {
            "declared_library_count": 0,
            "missing_declared_libraries": [],
            "lakefile_sha256": None,
        }
    config = tomllib.loads(lakefile.read_text(encoding="utf-8"))
    libraries = config.get("lean_lib", [])
    if not isinstance(libraries, list):
        raise SourcePopulationError("lakefile lean_lib configuration is not a list")
    available_by_src_dir: dict[Path, list[str]] = {}
    missing: list[str] = []
    for library in libraries:
        if not isinstance(library, dict):
            raise SourcePopulationError("configured Lean library is not a table")
        name = library.get("name")
        if not isinstance(name, str):
            raise SourcePopulationError("configured Lean library has no string name")
        configured_src_dir = library.get("srcDir", ".")
        if not isinstance(configured_src_dir, str):
            raise SourcePopulationError(f"configured Lean library {name} has invalid srcDir")
        src_dir = root / configured_src_dir
        available = available_by_src_dir.get(src_dir)
        if available is None:
            available = _source_modules(src_dir)
            available_by_src_dir[src_dir] = available
        globs = library.get("globs")
        if globs is None:
            matched = any(
                module == name or module.startswith(f"{name}.")
                for module in available
            )
        else:
            if not isinstance(globs, list) or not all(
                isinstance(pattern, str) for pattern in globs
            ):
                raise SourcePopulationError(
                    f"configured Lean library {name} has invalid globs"
                )
            matched = any(
                fnmatch.fnmatchcase(module, pattern)
                for module in available
                for pattern in globs
            )
        if not matched:
            missing.append(name)
    return {
        "declared_library_count": len(libraries),
        "missing_declared_libraries": sorted(missing),
        "lakefile_sha256": sha256_path(lakefile),
    }


def current_source_plan(
    root: Path = ROOT, planner: ModuleType = lean_fast_build
) -> dict[str, object]:
    """Return the source-current maximal-root plan and population digest."""

    modules = planner.discover(root)
    if not modules:
        raise SourcePopulationError("no local Lean source modules discovered")
    graph = planner.local_graph(modules)
    try:
        planner.waves(set(modules), graph)
    except RuntimeError as error:
        raise SourcePopulationError(f"local Lean import graph is cyclic: {error}") from error
    imported = set().union(*graph.values()) if graph else set()
    targets = sorted(set(modules) - imported)
    closure = planner.reachable(targets, graph)
    uncovered = sorted(set(modules) - closure)
    if not targets or uncovered:
        raise SourcePopulationError(
            "maximal roots do not cover every local Lean module: "
            + ", ".join(uncovered[:10])
        )
    rows = [
        {
            "module": module,
            "path": modules[module].relative_to(root).as_posix(),
            "sha256": sha256_path(modules[module]),
        }
        for module in sorted(modules)
    ]
    denominator_bytes = json.dumps(
        rows, sort_keys=True, separators=(",", ":")
    ).encode()
    return {
        "schema": "plectis-lean-source-population/1",
        "root": str(root),
        "targets": targets,
        "module_count": len(modules),
        "maximal_root_count": len(targets),
        "closure_count": len(closure),
        "sha256": sha256_bytes(denominator_bytes),
        "digest_definition": (
            "sha256 of canonical JSON rows (module, relative path, source sha256) "
            "for every source discovered by lean_fast_build"
        ),
        "discovery_exclusions": ["hidden directories", "_*.lean"],
        **declared_lean_library_inventory(root),
    }


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--root", type=Path, default=ROOT)
    parser.add_argument("--pretty", action="store_true")
    args = parser.parse_args()
    plan = current_source_plan(args.root.resolve())
    print(json.dumps(plan, indent=2 if args.pretty else None, sort_keys=True))
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
