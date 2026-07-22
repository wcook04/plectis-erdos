#!/usr/bin/env python3
# SPDX-FileCopyrightText: 2026 Will Cook
# SPDX-License-Identifier: Apache-2.0
"""Verify that the supported root import reaches every public Lean module."""

from __future__ import annotations

import json
import re
from pathlib import Path


ROOT = Path(__file__).resolve().parent.parent
LIBRARY_ROOTS = ("Erdos249257", "ErdosProblems")
ROOT_FILES = tuple(f"{root}.lean" for root in LIBRARY_ROOTS)
IMPORT_RE = re.compile(
    rf"^import ((?:{'|'.join(LIBRARY_ROOTS)})(?:\.[A-Za-z0-9_]+)+)\s*$",
    re.M,
)


def registry_errors(
    nodes: list[dict[str, object]], public_paths: set[str]
) -> list[str]:
    """Return identity and disk-coverage errors for the public module registry."""
    module_paths = [str(node["path"]) for node in nodes]
    duplicate_paths = sorted(
        module_path
        for module_path in set(module_paths)
        if module_paths.count(module_path) > 1
    )
    errors = [
        f"machine-readable module graph contains duplicate path: {module_path}"
        for module_path in duplicate_paths
    ]
    for node in nodes:
        module_id = str(node["id"])
        module_path = str(node["path"])
        expected_path = module_id.replace(".", "/") + ".lean"
        if module_path != expected_path:
            errors.append(
                f"module id/path mismatch: {module_id} should use {expected_path}, "
                f"not {module_path}"
            )

    registered_paths = set(module_paths)
    for module_path in sorted(public_paths - registered_paths):
        errors.append(f"public Lean file is missing from module graph: {module_path}")
    for module_path in sorted(registered_paths - public_paths):
        errors.append(f"module graph path is missing from disk: {module_path}")
    return errors


def closure_errors(
    nodes: list[dict[str, object]], root_imports: list[str]
) -> list[str]:
    """Return identity, missing-edge, and orphan errors for a public import graph."""
    module_ids = [str(node["id"]) for node in nodes]
    duplicate_ids = sorted(
        module_id for module_id in set(module_ids) if module_ids.count(module_id) > 1
    )
    errors = [
        f"machine-readable module graph contains duplicate id: {module_id}"
        for module_id in duplicate_ids
    ]
    imports_by_id = {str(node["id"]): list(node["imports"]) for node in nodes}
    for importer, imports in [("supported roots", root_imports), *imports_by_id.items()]:
        for imported in imports:
            if imported not in imports_by_id:
                errors.append(f"{importer} imports unknown public module {imported}")

    reachable: set[str] = set()
    pending = list(root_imports)
    while pending:
        module = pending.pop()
        if module in reachable or module not in imports_by_id:
            continue
        reachable.add(module)
        pending.extend(imports_by_id[module])
    for module in sorted(set(imports_by_id) - reachable):
        errors.append(f"public module is outside supported root-import closure: {module}")
    return errors


def check_fixtures() -> None:
    connected = [
        {
            "id": "Erdos249257.A",
            "path": "Erdos249257/A.lean",
            "imports": ["Erdos249257.B"],
        },
        {
            "id": "Erdos249257.B",
            "path": "Erdos249257/B.lean",
            "imports": [],
        },
    ]
    connected_paths = {"Erdos249257/A.lean", "Erdos249257/B.lean"}
    assert registry_errors(connected, connected_paths) == []
    assert closure_errors(connected, ["Erdos249257.A"]) == []

    orphaned = [
        *connected,
        {
            "id": "Erdos249257.Orphan",
            "path": "Erdos249257/Orphan.lean",
            "imports": [],
        },
    ]
    assert closure_errors(orphaned, ["Erdos249257.A"]) == [
        "public module is outside supported root-import closure: Erdos249257.Orphan"
    ]

    missing = [
        {
            "id": "Erdos249257.A",
            "path": "Erdos249257/A.lean",
            "imports": ["Erdos249257.Missing"],
        }
    ]
    assert closure_errors(missing, ["Erdos249257.A"]) == [
        "Erdos249257.A imports unknown public module Erdos249257.Missing"
    ]

    duplicate = [
        {"id": "Erdos249257.A", "path": "Erdos249257/A.lean", "imports": []},
        {"id": "Erdos249257.A", "path": "Erdos249257/A2.lean", "imports": []},
    ]
    assert closure_errors(duplicate, ["Erdos249257.A"]) == [
        "machine-readable module graph contains duplicate id: Erdos249257.A"
    ]

    duplicate_path = [
        {"id": "Erdos249257.A", "path": "Erdos249257/A.lean", "imports": []},
        {"id": "Erdos249257.B", "path": "Erdos249257/A.lean", "imports": []},
    ]
    duplicate_path_errors = registry_errors(
        duplicate_path, {"Erdos249257/A.lean"}
    )
    assert (
        "machine-readable module graph contains duplicate path: "
        "Erdos249257/A.lean"
    ) in duplicate_path_errors

    mismatched_path = [
        {"id": "Erdos249257.A", "path": "Erdos249257/B.lean", "imports": []}
    ]
    assert any(
        error.startswith("module id/path mismatch:")
        for error in registry_errors(mismatched_path, {"Erdos249257/B.lean"})
    )

    assert registry_errors(connected, connected_paths | {"Erdos249257/New.lean"}) == [
        "public Lean file is missing from module graph: Erdos249257/New.lean"
    ]
    assert registry_errors(connected, {"Erdos249257/A.lean"}) == [
        "module graph path is missing from disk: Erdos249257/B.lean"
    ]


def main() -> int:
    check_fixtures()
    claims = json.loads((ROOT / "docs" / "claims.json").read_text(encoding="utf-8"))
    graph = claims["machine_readable_paper"]["module_graph"]
    assert graph["root"] == "Erdos249257.lean"
    roots = [graph["root"], *graph.get("additional_roots", [])]
    assert roots == list(ROOT_FILES)
    root_imports = [
        imported
        for root in roots
        for imported in IMPORT_RE.findall((ROOT / root).read_text(encoding="utf-8"))
    ]
    public_paths = {
        path.relative_to(ROOT).as_posix()
        for library_root in LIBRARY_ROOTS
        for path in (ROOT / library_root).rglob("*.lean")
    }
    errors = [
        *registry_errors(graph["nodes"], public_paths),
        *closure_errors(graph["nodes"], root_imports),
    ]
    assert not errors, "\n".join(errors)
    print(
        "test_root_import_closure: registry exactly matches disk and supported "
        f"roots reach all {len(graph['nodes'])} public Lean modules"
    )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
