#!/usr/bin/env python3
"""Read-only location and role catalog for Lean-corpus computation scripts."""

from __future__ import annotations

import argparse
import json
from collections import Counter
from pathlib import Path
from typing import Any


SCRIPT_SUFFIXES = {".py", ".cpp"}
SCRIPT_ROLES = {
    "audit",
    "corpus_navigation",
    "corpus_structure_check",
    "experiment_or_helper",
    "lean_build_wrapper",
    "test",
    "verification",
}
SCRIPT_SCOPES = {"corpus", "problem"}


def _normalize_problem_id(value: str) -> str:
    compact = value.strip().lower().replace("-", "_")
    if compact.startswith("erdos_"):
        suffix = compact.removeprefix("erdos_")
    elif compact.startswith("erdos"):
        suffix = compact.removeprefix("erdos").lstrip("_")
    else:
        suffix = compact
    if not suffix.isdecimal():
        raise ValueError(f"expected an Erdős number or erdos_<number>, got {value!r}")
    return f"erdos_{int(suffix)}"


def _role(path: Path) -> str:
    name = path.name
    if name == "lean_fast_build.py":
        return "lean_build_wrapper"
    if name == "check_problem_corpus_index.py":
        return "corpus_structure_check"
    if name in {"script_catalog.py", "corpus_navigation.py"}:
        return "corpus_navigation"
    if name.startswith("test_"):
        return "test"
    if name.startswith("check_"):
        return "audit"
    if name.startswith("verify_"):
        return "verification"
    return "experiment_or_helper"


def _problem_scope(project_root: Path, path: Path) -> tuple[str, str | None]:
    relative = path.relative_to(project_root)
    parts = relative.parts
    if len(parts) >= 4 and parts[0] == "ErdosProblems" and parts[1].startswith("Erdos"):
        return "problem", f"erdos_{parts[1][5:]}"
    return "corpus", None


def catalog(
    project_root: Path,
    *,
    problem: str | None = None,
    role: str | None = None,
    scope: str | None = None,
) -> dict[str, Any]:
    """Catalog source files beneath the two supported script roots.

    This reports filesystem organization only. It neither runs a script nor
    interprets its computation as mathematical evidence.
    """

    selected_problem_id = _normalize_problem_id(problem) if problem is not None else None
    if role is not None and role not in SCRIPT_ROLES:
        raise ValueError(f"unknown script role: {role!r}")
    if scope is not None and scope not in SCRIPT_SCOPES:
        raise ValueError(f"unknown script scope: {scope!r}")
    script_dirs = [project_root / "scripts"]
    problem_root = project_root / "ErdosProblems"
    script_dirs.extend(sorted(problem_root.glob("Erdos*/scripts")))

    entries: list[dict[str, Any]] = []
    for script_dir in script_dirs:
        if not script_dir.is_dir():
            continue
        for path in sorted(script_dir.iterdir()):
            if not path.is_file() or path.suffix not in SCRIPT_SUFFIXES:
                continue
            entry_scope, entry_problem_id = _problem_scope(project_root, path)
            entries.append(
                {
                    "path": path.relative_to(project_root).as_posix(),
                    "scope": entry_scope,
                    "problem_id": entry_problem_id,
                    "role": _role(path),
                    "language": path.suffix.removeprefix("."),
                }
            )

    if selected_problem_id is not None:
        entries = [entry for entry in entries if entry["problem_id"] == selected_problem_id]
    if role is not None:
        entries = [entry for entry in entries if entry["role"] == role]
    if scope is not None:
        entries = [entry for entry in entries if entry["scope"] == scope]
    entries.sort(key=lambda entry: entry["path"])
    return {
        "schema_version": "lean_script_catalog_v0",
        "kind": "lean_script_catalog",
        "boundary": "filesystem classification only; scripts are not executed and no mathematical status is inferred",
        "filters": {"problem_id": selected_problem_id, "role": role, "scope": scope},
        "summary": {
            "script_count": len(entries),
            "by_scope": dict(sorted(Counter(entry["scope"] for entry in entries).items())),
            "by_role": dict(sorted(Counter(entry["role"] for entry in entries).items())),
            "by_language": dict(sorted(Counter(entry["language"] for entry in entries).items())),
        },
        "scripts": entries,
    }


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument(
        "--project-root",
        type=Path,
        default=Path(__file__).resolve().parents[1],
        help="Lean project root (defaults to this script's parent)",
    )
    parser.add_argument(
        "--problem",
        help="restrict to scripts physically owned by one Erdős problem (for example 257 or erdos_257)",
    )
    parser.add_argument(
        "--role",
        choices=sorted(SCRIPT_ROLES),
        help="restrict to one read-only operational role; combine with --problem when useful",
    )
    parser.add_argument(
        "--scope",
        choices=sorted(SCRIPT_SCOPES),
        help="restrict to corpus-level or problem-owned scripts before opening a tool",
    )
    parser.add_argument("--json", action="store_true", help="emit the full deterministic JSON catalog")
    args = parser.parse_args()

    try:
        payload = catalog(
            args.project_root.resolve(),
            problem=args.problem,
            role=args.role,
            scope=args.scope,
        )
    except ValueError as error:
        parser.error(str(error))
    if args.json:
        print(json.dumps(payload, indent=2, sort_keys=True))
    else:
        print(json.dumps(payload["summary"], indent=2, sort_keys=True))
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
