#!/usr/bin/env python3
# SPDX-FileCopyrightText: 2026 Will Cook
# SPDX-License-Identifier: Apache-2.0
"""Verify the compact roots plus auxiliary forest cover every public module."""

from __future__ import annotations

import json
import os
import re
import stat
import tempfile
from pathlib import Path


ROOT = Path(__file__).resolve().parent.parent
from lean_source import (
    LIBRARY_ROOTS,
    library_root_file,
    library_source_paths,
    library_storage_variants,
)

ROOT_FILES = tuple(
    library_root_file(ROOT, root).relative_to(ROOT).as_posix()
    for root in LIBRARY_ROOTS
)
IMPORT_RE = re.compile(
    rf"^import ((?:{'|'.join(LIBRARY_ROOTS)})(?:\.[A-Za-z0-9_]+)+)\s*$",
    re.M,
)
# Every CI build elaborates the supported-root closure, so a module header in it that
# calls the module unrun or uncompiled is false. Such prose was read as status by
# external reviewers and held checked results back (15 September 2026).
BUILD_STATUS_PROSE_RE = re.compile(
    r"\bUNRUN\b|\bUNCOMPILED\b|\b[Uu]ncompiled\b|\bNOT (?:been |yet )?compiled\b"
    r"|\bnot (?:been |yet )?compiled\b|No local compilation|not a compilation receipt"
)
BUILD_STATUS_HEADER_LINES = 60


def require(condition: bool, message: str) -> None:
    """Keep root-closure failures active when run with ``python -O``."""
    if not condition:
        raise AssertionError(message)


def safe_public_file(root: Path, path: Path) -> Path:
    """Resolve only regular files without symlinked checkout components."""
    root = Path(os.path.abspath(root))
    candidate = Path(os.path.abspath(path))
    current = candidate
    while True:
        require(
            not current.is_symlink(),
            f"public root-closure path traverses a symbolic link: {candidate}",
        )
        if current == root:
            break
        require(current.parent != current, f"public root-closure path escaped checkout: {candidate}")
        current = current.parent
    require(candidate.is_file(), f"public root-closure path is not a regular file: {candidate}")
    return candidate


def safe_public_bytes(root: Path, path: Path) -> bytes:
    """Read one public file through a no-follow descriptor."""
    candidate = safe_public_file(root, path)
    flags = os.O_RDONLY | os.O_NOFOLLOW | os.O_NONBLOCK
    if hasattr(os, "O_CLOEXEC"):
        flags |= os.O_CLOEXEC
    try:
        descriptor = os.open(candidate, flags)
    except OSError as exc:
        raise AssertionError(
            f"public root-closure path could not be opened safely: {candidate}"
        ) from exc
    try:
        metadata = os.fstat(descriptor)
        require(
            stat.S_ISREG(metadata.st_mode),
            f"public root-closure path is not a regular file: {candidate}",
        )
        chunks: list[bytes] = []
        while True:
            chunk = os.read(descriptor, 1024 * 1024)
            if not chunk:
                return b"".join(chunks)
            chunks.append(chunk)
    finally:
        os.close(descriptor)


def safe_public_text(root: Path, path: Path) -> str:
    """Decode one descriptor-bound public file as UTF-8."""
    try:
        return safe_public_bytes(root, path).decode("utf-8")
    except UnicodeDecodeError as exc:
        raise AssertionError(f"public root-closure file is not UTF-8: {path}") from exc


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
        expected_paths = library_storage_variants(module_id.replace(".", "/") + ".lean")
        if module_path not in expected_paths:
            errors.append(
                f"module id/path mismatch: {module_id} should use {expected_paths[0]}, "
                f"not {module_path}"
            )

    registered_paths = set(module_paths)
    for module_path in sorted(public_paths - registered_paths):
        errors.append(f"public Lean file is missing from module graph: {module_path}")
    for module_path in sorted(registered_paths - public_paths):
        errors.append(f"module graph path is missing from disk: {module_path}")
    return errors


def closure_errors(
    nodes: list[dict[str, object]],
    root_imports: list[str],
    auxiliary_roots: list[str] | None = None,
    allowed_auxiliary_prefixes: tuple[str, ...] = (),
) -> list[str]:
    """Return identity, missing-edge, and orphan errors for a public module forest."""
    auxiliary_roots = auxiliary_roots or []
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
    if len(auxiliary_roots) != len(set(auxiliary_roots)):
        errors.append("auxiliary root list contains duplicates")
    for auxiliary_root in auxiliary_roots:
        if auxiliary_root not in imports_by_id:
            errors.append(f"auxiliary root names unknown public module {auxiliary_root}")
        elif not allowed_auxiliary_prefixes or not auxiliary_root.startswith(
            allowed_auxiliary_prefixes
        ):
            errors.append(
                f"auxiliary root is outside allowed namespaces: {auxiliary_root}"
            )

    reachable: set[str] = set()
    pending = [*root_imports, *auxiliary_roots]
    while pending:
        module = pending.pop()
        if module in reachable or module not in imports_by_id:
            continue
        reachable.add(module)
        pending.extend(imports_by_id[module])
    for module in sorted(set(imports_by_id) - reachable):
        errors.append(f"public module is outside supported root-import closure: {module}")
    return errors


def build_status_prose_errors(texts_by_module: dict[str, str]) -> list[str]:
    """Return header lines of supported-root modules that describe their build status in prose."""
    errors = []
    for module, text in sorted(texts_by_module.items()):
        for number, line in enumerate(text.splitlines()[:BUILD_STATUS_HEADER_LINES], 1):
            if BUILD_STATUS_PROSE_RE.search(line):
                errors.append(
                    f"supported-root module {module} line {number} states its build status "
                    f"in prose; CI compiles it, so remove: {line.strip()}"
                )
    return errors


def check_build_status_prose_fixtures() -> None:
    stale = {
        "Erdos249257.A": "/-!\nCandidate source, UNRUN. One support is chosen first.\n-/\n",
        "Erdos249257.B": "/-!\nNew proof source, NOT compiled in the return environment.\n-/\n",
        "Erdos249257.C": "/-!\nUncompiled candidates.  The state theorem is assembled.\n-/\n",
    }
    found = build_status_prose_errors(stale)
    require(len(found) == 3, f"build-status prose fixture missed a stale header: {found}")
    clean = {
        "Erdos249257.D": "/-!\nThe candidate root is checked against every residue class.\n-/\n",
        "Erdos249257.E": "/-!\nProves F(a/b) irrational on the contour region.\n-/\n",
    }
    require(
        build_status_prose_errors(clean) == [],
        "build-status prose check flagged a mathematical use of the word candidate",
    )
    late = {"Erdos249257.F": "\n" * BUILD_STATUS_HEADER_LINES + "-- UNRUN note far below the header\n"}
    require(build_status_prose_errors(late) == [], "build-status prose check read past the header window")


def check_fixtures() -> None:
    with tempfile.TemporaryDirectory() as raw:
        root = Path(raw)
        outside = root / "outside"
        outside.mkdir()
        (outside / "Escaped.lean").write_text("theorem escaped : True := True.intro\n", encoding="utf-8")
        source_dir = root / "Erdos249257"
        source_dir.mkdir()
        (source_dir / "linked").symlink_to(outside, target_is_directory=True)
        try:
            safe_public_file(root, source_dir / "linked" / "Escaped.lean")
        except AssertionError:
            pass
        else:
            require(False, "root-closure source guard followed a symlinked parent")

    if hasattr(os, "mkfifo"):
        with tempfile.TemporaryDirectory(prefix="root-closure-fifo-") as raw:
            root = Path(raw)
            fifo = root / "Erdos249257.lean"
            os.mkfifo(fifo)
            try:
                safe_public_bytes(root, fifo)
            except AssertionError as exc:
                require("regular file" in str(exc), str(exc))
            else:
                require(False, "root-closure source guard opened a FIFO")

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
    require(
        registry_errors(connected, connected_paths) == [],
        "connected module registry fixture was rejected",
    )
    require(
        closure_errors(connected, ["Erdos249257.A"]) == [],
        "connected root closure fixture was rejected",
    )

    orphaned = [
        *connected,
        {
            "id": "Erdos249257.Orphan",
            "path": "Erdos249257/Orphan.lean",
            "imports": [],
        },
    ]
    require(
        closure_errors(orphaned, ["Erdos249257.A"]) == [
            "public module is outside supported root-import closure: "
            "Erdos249257.Orphan"
        ],
        "orphan module fixture was not rejected",
    )
    auxiliary = {
        "id": "ErdosProblems.FreePosition.Aux",
        "path": "ErdosProblems/FreePosition/Aux.lean",
        "imports": [],
    }
    require(
        closure_errors(
            [*connected, auxiliary],
            ["Erdos249257.A"],
            ["ErdosProblems.FreePosition.Aux"],
            ("ErdosProblems.FreePosition.",),
        )
        == [],
        "allowed auxiliary root fixture was rejected",
    )
    require(
        closure_errors(
            [*connected, auxiliary],
            ["Erdos249257.A"],
            ["Erdos249257.A"],
            ("ErdosProblems.FreePosition.",),
        )
        == [
            "auxiliary root is outside allowed namespaces: Erdos249257.A",
            "public module is outside supported root-import closure: "
            "ErdosProblems.FreePosition.Aux",
        ],
        "out-of-namespace auxiliary root fixture was not rejected",
    )

    missing = [
        {
            "id": "Erdos249257.A",
            "path": "Erdos249257/A.lean",
            "imports": ["Erdos249257.Missing"],
        }
    ]
    require(
        closure_errors(missing, ["Erdos249257.A"]) == [
            "Erdos249257.A imports unknown public module Erdos249257.Missing"
        ],
        "missing import fixture was not rejected",
    )

    duplicate = [
        {"id": "Erdos249257.A", "path": "Erdos249257/A.lean", "imports": []},
        {"id": "Erdos249257.A", "path": "Erdos249257/A2.lean", "imports": []},
    ]
    require(
        closure_errors(duplicate, ["Erdos249257.A"]) == [
            "machine-readable module graph contains duplicate id: Erdos249257.A"
        ],
        "duplicate module id fixture was not rejected",
    )

    duplicate_path = [
        {"id": "Erdos249257.A", "path": "Erdos249257/A.lean", "imports": []},
        {"id": "Erdos249257.B", "path": "Erdos249257/A.lean", "imports": []},
    ]
    duplicate_path_errors = registry_errors(
        duplicate_path, {"Erdos249257/A.lean"}
    )
    require(
        (
            "machine-readable module graph contains duplicate path: "
            "Erdos249257/A.lean"
        )
        in duplicate_path_errors,
        "duplicate module path fixture was not rejected",
    )

    mismatched_path = [
        {"id": "Erdos249257.A", "path": "Erdos249257/B.lean", "imports": []}
    ]
    require(
        any(
            error.startswith("module id/path mismatch:")
            for error in registry_errors(mismatched_path, {"Erdos249257/B.lean"})
        ),
        "module id/path mismatch fixture was not rejected",
    )

    require(
        registry_errors(connected, connected_paths | {"Erdos249257/New.lean"}) == [
            "public Lean file is missing from module graph: Erdos249257/New.lean"
        ],
        "unregistered public file fixture was not rejected",
    )
    require(
        registry_errors(connected, {"Erdos249257/A.lean"}) == [
            "module graph path is missing from disk: Erdos249257/B.lean"
        ],
        "missing public file fixture was not rejected",
    )


def main() -> int:
    check_fixtures()
    check_build_status_prose_fixtures()
    claims = json.loads(
        safe_public_text(ROOT, ROOT / "docs" / "claims.json")
    )
    graph = claims["machine_readable_paper"]["module_graph"]
    require(
        graph["root"] == "lean/Erdos249257.lean",
        "machine-readable graph has the wrong primary root",
    )
    roots = [graph["root"], *graph.get("additional_roots", [])]
    require(
        roots == ["lean/Erdos249257.lean", "lean/ErdosProblems.lean"],
        "machine-readable graph does not expose both supported roots",
    )
    root_imports = [
        imported
        for root_name in LIBRARY_ROOTS
        for imported in IMPORT_RE.findall(
            safe_public_text(ROOT, library_root_file(ROOT, root_name))
        )
    ]
    imports_by_id = {
        str(node["id"]): list(node["imports"]) for node in graph["nodes"]
    }
    supported_root_reachable: set[str] = set()
    pending = list(root_imports)
    while pending:
        module = pending.pop()
        if module in supported_root_reachable or module not in imports_by_id:
            continue
        supported_root_reachable.add(module)
        pending.extend(imports_by_id[module])
    require(
        "ErdosProblems.Skip.LadderT67" in supported_root_reachable,
        "the reviewed t ≤ 82 finite-certificate theorem must be elaborated by "
        "a supported-root build, not only covered by the auxiliary forest",
    )
    public_paths = {
        path.relative_to(ROOT).as_posix()
        for path in library_source_paths(ROOT)
        if path != library_root_file(ROOT, LIBRARY_ROOTS[0])
        and path != library_root_file(ROOT, LIBRARY_ROOTS[1])
    }
    auxiliary_contract = graph["auxiliary_root_contract"]
    errors = [
        *registry_errors(graph["nodes"], public_paths),
        *closure_errors(
            graph["nodes"],
            root_imports,
            graph["auxiliary_roots"],
            tuple(auxiliary_contract["allowed_prefixes"]),
        ),
    ]
    paths_by_id = {str(node["id"]): str(node["path"]) for node in graph["nodes"]}
    errors.extend(
        build_status_prose_errors(
            {
                module: safe_public_text(ROOT, ROOT / paths_by_id[module])
                for module in supported_root_reachable
                if module in paths_by_id
            }
        )
    )
    require(not errors, "\n".join(errors))
    print(
        "test_root_import_closure: registry exactly matches disk and compact "
        "roots plus the validated auxiliary forest reach all "
        f"{len(graph['nodes'])} public Lean modules"
    )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
