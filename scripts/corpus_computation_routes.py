#!/usr/bin/env python3
"""Map explicitly declared problem identities on corpus-level computation scripts."""

from __future__ import annotations

import argparse
import ast
import json
import re
from collections import Counter
from pathlib import Path
from typing import Any

from script_catalog import _normalize_problem_id, catalog


PROBLEM_ID_PATTERN = re.compile(
    r"(?<![A-Za-z0-9_])['\"]?problem_id['\"]?\s*(?:=|:)\s*['\"](erdos[_-]?\d+)['\"]",
    flags=re.IGNORECASE,
)
UNKNOWN_METADATA_LINK_PREVIEW_LIMIT = 4
UNCLASSIFIED_ROLE_PREVIEW_LIMIT = 4
DEFAULT_UNCLASSIFIED_PATH_LIMIT = 40


def _manifest_problem_ids(project_root: Path) -> list[str]:
    path = project_root / "ErdosProblems" / "assimilation_manifest.json"
    payload = json.loads(path.read_text(encoding="utf-8"))
    problems = payload.get("problems") if isinstance(payload, dict) else None
    if not isinstance(problems, list):
        raise ValueError("manifest problems must be a list")
    ids = [row.get("id") for row in problems if isinstance(row, dict)]
    if not all(isinstance(problem_id, str) and problem_id for problem_id in ids):
        raise ValueError("manifest problems must all have ids")
    return sorted(set(ids), key=_problem_sort_key)


def _problem_sort_key(problem_id: str) -> tuple[int, str]:
    suffix = problem_id.removeprefix("erdos_")
    return (int(suffix) if suffix.isdecimal() else 0, problem_id)


def _declared_problem_ids(path: Path) -> list[str]:
    """Read literal identity declarations only; never infer from filenames or prose."""

    try:
        text = path.read_text(encoding="utf-8")
    except (OSError, UnicodeDecodeError):
        return []
    literal_ids: set[str] = set()
    if path.suffix == ".py":
        try:
            tree = ast.parse(text, filename=str(path))
        except SyntaxError:
            return []
        for node in ast.walk(tree):
            value: object | None = None
            if isinstance(node, ast.keyword) and node.arg == "problem_id":
                value = node.value
            elif isinstance(node, ast.Assign) and any(
                isinstance(target, ast.Name) and target.id == "problem_id"
                for target in node.targets
            ):
                value = node.value
            elif (
                isinstance(node, ast.AnnAssign)
                and isinstance(node.target, ast.Name)
                and node.target.id == "problem_id"
            ):
                value = node.value
            if isinstance(value, ast.Constant) and isinstance(value.value, str):
                literal_ids.add(value.value)
    else:
        literal_ids.update(match.group(1) for match in PROBLEM_ID_PATTERN.finditer(text))

    ids: set[str] = set()
    for literal_id in literal_ids:
        try:
            ids.add(_normalize_problem_id(literal_id))
        except ValueError:
            continue
    return sorted(ids, key=_problem_sort_key)


def computation_routes(
    project_root: Path,
    *,
    problem: str | None = None,
    unclassified_role: str | None = None,
    path_limit: int = DEFAULT_UNCLASSIFIED_PATH_LIMIT,
) -> dict[str, Any]:
    """Return read-only routes from literal script metadata to manifest problems."""

    if problem is not None and unclassified_role is not None:
        raise ValueError("problem and unclassified_role are mutually exclusive")
    if path_limit < 1:
        raise ValueError("path_limit must be positive")

    known_problem_ids = _manifest_problem_ids(project_root)
    selected_problem_id = _normalize_problem_id(problem) if problem is not None else None
    if selected_problem_id is not None and selected_problem_id not in known_problem_ids:
        raise ValueError(f"unknown manifest problem id: {selected_problem_id}")

    corpus_entries = [
        entry
        for entry in catalog(project_root)["scripts"]
        if entry["scope"] == "corpus"
    ]
    paths_by_problem = {problem_id: [] for problem_id in known_problem_ids}
    explicit_script_count = 0
    unknown_metadata_links: set[tuple[str, str, str]] = set()
    role_counts_by_metadata = {
        "with_literal_problem_id": Counter(),
        "without_literal_problem_id": Counter(),
    }
    unclassified_scripts_by_role: dict[str, list[dict[str, str]]] = {}
    for entry in corpus_entries:
        path = project_root / entry["path"]
        declared_ids = _declared_problem_ids(path)
        role_counts_by_metadata[
            "with_literal_problem_id" if declared_ids else "without_literal_problem_id"
        ][entry["role"]] += 1
        if declared_ids:
            explicit_script_count += 1
        else:
            unclassified_scripts_by_role.setdefault(entry["role"], []).append(
                {
                    "path": entry["path"],
                    "role": entry["role"],
                    "language": entry["language"],
                    "classification_state": "no_literal_problem_id_metadata",
                }
            )
        for problem_id in declared_ids:
            if problem_id not in paths_by_problem:
                unknown_metadata_links.add((entry["path"], problem_id, entry["role"]))
                continue
            paths_by_problem[problem_id].append(
                {
                    "path": entry["path"],
                    "role": entry["role"],
                    "language": entry["language"],
                    "declared_problem_ids": declared_ids,
                    "route_reason": "literal_problem_id_metadata",
                }
            )

    known_unclassified_roles = sorted(unclassified_scripts_by_role)
    if unclassified_role is not None and unclassified_role not in known_unclassified_roles:
        raise ValueError(
            "unknown unclassified role: "
            f"{unclassified_role}; choose from {', '.join(known_unclassified_roles)}"
        )

    selected_ids = (
        []
        if unclassified_role is not None
        else ([selected_problem_id] if selected_problem_id else known_problem_ids)
    )
    manifest_problem_with_explicit_script_count = sum(
        1 for problem_id in known_problem_ids if paths_by_problem[problem_id]
    )
    problems: list[dict[str, Any]] = []
    for problem_id in selected_ids:
        routes = sorted(paths_by_problem[problem_id], key=lambda route: route["path"])
        row: dict[str, Any] = {
            "problem_id": problem_id,
            "explicit_corpus_script_count": len(routes),
            "explicit_corpus_script_role_counts": dict(
                sorted(Counter(route["role"] for route in routes).items())
            ),
            "representative_paths": [route["path"] for route in routes[:4]],
            "omitted_path_count": max(0, len(routes) - 4),
            "drilldown_command": (
                "./repo-python formal_math/erdos257_period_noncollapse/scripts/"
                "corpus_computation_routes.py "
                f"--problem {problem_id} --json"
            ),
            "problem_cockpit_command": (
                "./repo-python -m system.lib.mathematical_working_memory "
                f"--query 'Erdos #{problem_id.removeprefix('erdos_')}' "
                "--problem-cockpit --context-budget 12000"
            ),
            "source_topology_command": (
                "./repo-python formal_math/erdos257_period_noncollapse/scripts/"
                "corpus_navigation.py "
                f"--problem {problem_id} --source-summary --json"
            ),
            "bounded_source_inventory_command": (
                "./repo-python formal_math/erdos257_period_noncollapse/scripts/"
                "corpus_navigation.py "
                f"--problem {problem_id} --source-paths --source-kind markdown "
                "--source-path-limit 40 --json"
            ),
            "computation_surface_routes": {
                "physically_problem_owned_scripts": (
                    "./repo-python formal_math/erdos257_period_noncollapse/scripts/"
                    f"script_catalog.py --problem {problem_id} --json"
                ),
                "literal_corpus_script_metadata": (
                    "./repo-python formal_math/erdos257_period_noncollapse/scripts/"
                    f"corpus_computation_routes.py --problem {problem_id} --json"
                ),
                "packet_bound_probe_receipts": (
                    "./repo-python -m system.lib.formal_math_probe_registry "
                    f"--problem {problem_id} --coverage"
                ),
            },
            "classification_boundary": {
                "physically_problem_owned_scripts": (
                    "filesystem ownership only; no execution or evidence claim"
                ),
                "literal_corpus_script_metadata": (
                    "explicit problem_id declarations only; no inferred relevance"
                ),
                "packet_bound_probe_receipts": (
                    "receipt-to-open-producer bindings; finite evidence, not proof authority"
                ),
            },
        }
        if selected_problem_id:
            row["corpus_scripts"] = routes
        problems.append(row)

    unknown_metadata_link_preview = [
        {"path": path, "declared_problem_id": problem_id, "role": role}
        for path, problem_id, role in sorted(unknown_metadata_links)
    ][:UNKNOWN_METADATA_LINK_PREVIEW_LIMIT]
    unclassified_role_choices = []
    for role in known_unclassified_roles:
        entries = sorted(unclassified_scripts_by_role[role], key=lambda entry: entry["path"])
        preview = [entry["path"] for entry in entries[:UNCLASSIFIED_ROLE_PREVIEW_LIMIT]]
        unclassified_role_choices.append(
            {
                "role": role,
                "script_count": len(entries),
                "representative_paths": preview,
                "omitted_path_count": max(0, len(entries) - len(preview)),
                "bounded_drilldown_command": (
                    "./repo-python formal_math/erdos257_period_noncollapse/scripts/"
                    "corpus_computation_routes.py "
                    f"--unclassified-role {role} "
                    f"--path-limit {DEFAULT_UNCLASSIFIED_PATH_LIMIT} --json"
                ),
            }
        )

    selected_unclassified_scripts: list[dict[str, str]] = []
    omitted_selected_unclassified_script_count = 0
    if unclassified_role is not None:
        all_selected = sorted(
            unclassified_scripts_by_role[unclassified_role], key=lambda entry: entry["path"]
        )
        selected_unclassified_scripts = all_selected[:path_limit]
        omitted_selected_unclassified_script_count = max(
            0, len(all_selected) - len(selected_unclassified_scripts)
        )
    return {
        "schema_version": "lean_corpus_computation_routes_v1",
        "kind": "lean_corpus_computation_routes",
        "boundary": (
            "Links arise only from literal problem_id metadata in corpus-level script "
            "source. Scripts are not executed, and these links do not imply mathematical "
            "status, relevance, or a recommendation to run a computation."
        ),
        "filters": {
            "problem_id": selected_problem_id,
            "unclassified_role": unclassified_role,
            "path_limit": path_limit if unclassified_role is not None else None,
        },
        "summary": {
            "corpus_script_count": len(corpus_entries),
            "corpus_script_with_explicit_problem_id_count": explicit_script_count,
            "corpus_script_without_explicit_problem_id_count": (
                len(corpus_entries) - explicit_script_count
            ),
            "manifest_problem_with_explicit_corpus_script_count": (
                manifest_problem_with_explicit_script_count
            ),
            "manifest_problem_without_explicit_corpus_script_count": (
                len(known_problem_ids) - manifest_problem_with_explicit_script_count
            ),
            "corpus_script_role_counts_by_problem_id_metadata": {
                metadata_state: dict(sorted(counts.items()))
                for metadata_state, counts in role_counts_by_metadata.items()
            },
            "unknown_declared_problem_id_count": len(unknown_metadata_links),
            "unknown_declared_problem_id_role_counts": dict(
                sorted(Counter(role for _, _, role in unknown_metadata_links).items())
            ),
            "unknown_declared_problem_id_links_preview": unknown_metadata_link_preview,
            "omitted_unknown_declared_problem_id_link_count": max(
                0, len(unknown_metadata_links) - len(unknown_metadata_link_preview)
            ),
            "unclassified_role_choices": unclassified_role_choices,
        },
        "problems": problems,
        "unclassified_corpus_scripts": selected_unclassified_scripts,
        "omitted_unclassified_corpus_script_count": (
            omitted_selected_unclassified_script_count
        ),
        "unclassified_boundary": (
            "Unclassified means only that no literal problem_id metadata was found. "
            "Filenames and operational roles are not evidence of mathematical relevance, "
            "and listed scripts are not recommended for execution."
        ),
    }


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument(
        "--project-root",
        type=Path,
        default=Path(__file__).resolve().parents[1],
        help="Lean project root (defaults to this script's parent)",
    )
    selection = parser.add_mutually_exclusive_group()
    selection.add_argument(
        "--problem",
        help="show every corpus-level script with literal metadata for one problem",
    )
    selection.add_argument(
        "--unclassified-role",
        help=(
            "show a bounded inventory for one operational role among corpus scripts "
            "without literal problem_id metadata"
        ),
    )
    parser.add_argument(
        "--path-limit",
        type=int,
        default=DEFAULT_UNCLASSIFIED_PATH_LIMIT,
        help="maximum paths emitted by --unclassified-role (default: 40)",
    )
    parser.add_argument("--json", action="store_true", help="emit the full deterministic route map")
    args = parser.parse_args()

    try:
        payload = computation_routes(
            args.project_root.resolve(),
            problem=args.problem,
            unclassified_role=args.unclassified_role,
            path_limit=args.path_limit,
        )
    except (OSError, ValueError, json.JSONDecodeError) as error:
        parser.error(str(error))
    if args.json:
        print(json.dumps(payload, indent=2, sort_keys=True))
    else:
        print(json.dumps(payload["summary"], indent=2, sort_keys=True))
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
