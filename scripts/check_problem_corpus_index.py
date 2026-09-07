#!/usr/bin/env python3
"""Check that the problem-centric Lean corpus index still resolves on disk.

The checker validates organization only: manifest rows, problem directories,
research packets, declared Lean modules, and supported-root imports. It never
reads theorem bodies or changes mathematical claim status.
"""

from __future__ import annotations

import argparse
import json
import re
import sys
from pathlib import Path
from typing import Any, Iterable


DEFAULT_PROJECT_ROOT = Path(__file__).resolve().parents[1]
IMPORT_RE = re.compile(r"^\s*import\s+([A-Za-z0-9_.']+)\s*(?:--.*)?$")

# These are discoverability markers, not mathematical assertions. They bind
# the maintained corpus adapters to the narrow helper routes that keep a large
# mixed Lean/research corpus navigable without making the guide a status ledger.
ENTRY_ROUTE_MARKERS = (
    (
        "AGENTS.md",
        "corpus_navigation.py --entry --json",
        "project_adapter_missing_corpus_entry_card_route",
    ),
    (
        "AGENTS.md",
        "--source-overview",
        "project_adapter_missing_corpus_source_overview_route",
    ),
    (
        "AGENTS.md",
        "--frontier-overview",
        "project_adapter_missing_corpus_frontier_overview_route",
    ),
    (
        "AGENTS.md",
        "recommended_routes",
        "project_adapter_missing_corpus_entry_decision_map",
    ),
    (
        "AGENTS.md",
        "problem_choices",
        "project_adapter_missing_live_problem_choice_index",
    ),
    (
        "AGENTS.md",
        "global_mathematical_connection_index",
        "project_adapter_missing_connection_index_route",
    ),
    (
        "AGENTS.md",
        "problem_navigation_routes",
        "project_adapter_missing_selected_problem_control_panel",
    ),
    (
        "AGENTS.md",
        "formal_math_corpus_registry.json",
        "project_adapter_missing_comparator_identity_registry",
    ),
    (
        "AGENTS.md",
        "system.lib.formal_math_corpus_registry",
        "project_adapter_missing_bounded_comparator_registry_route",
    ),
    (
        "AGENTS.md",
        "--problem erdos_<number>",
        "project_adapter_missing_problem_filtered_comparator_route",
    ),
    (
        "ErdosProblems/WORKING_GUIDE.md",
        "--problem-cockpit",
        "guide_missing_problem_cockpit_route",
    ),
    (
        "ErdosProblems/WORKING_GUIDE.md",
        "corpus_navigation.py --entry --json",
        "guide_missing_corpus_entry_card_route",
    ),
    (
        "ErdosProblems/WORKING_GUIDE.md",
        "recommended_routes",
        "guide_missing_corpus_entry_decision_map",
    ),
    (
        "ErdosProblems/WORKING_GUIDE.md",
        "formal_math_probe_registry --overview",
        "guide_missing_computation_overview_route",
    ),
    (
        "ErdosProblems/WORKING_GUIDE.md",
        "--source-summary",
        "guide_missing_source_summary_route",
    ),
    (
        "ErdosProblems/WORKING_GUIDE.md",
        "--source-overview",
        "guide_missing_source_overview_route",
    ),
    (
        "ErdosProblems/WORKING_GUIDE.md",
        "corpus_computation_routes.py --problem",
        "guide_missing_corpus_computation_route",
    ),
    (
        "ErdosProblems/WORKING_GUIDE.md",
        "corpus_navigation.py --frontier-summary",
        "guide_missing_packet_frontier_route",
    ),
    (
        "ErdosProblems/WORKING_GUIDE.md",
        "--frontier-overview",
        "guide_missing_corpus_frontier_overview_route",
    ),
    (
        "ErdosProblems/WORKING_GUIDE.md",
        "evidence_neighborhood",
        "guide_missing_evidence_neighborhood_route",
    ),
    (
        "ErdosProblems/WORKING_GUIDE.md",
        "problem_choices",
        "guide_missing_live_problem_choice_index",
    ),
    (
        "ErdosProblems/WORKING_GUIDE.md",
        "global_mathematical_connection_index",
        "guide_missing_connection_index_route",
    ),
    (
        "ErdosProblems/WORKING_GUIDE.md",
        "problem_navigation_routes",
        "guide_missing_selected_problem_control_panel",
    ),
    (
        "ErdosProblems/WORKING_GUIDE.md",
        "check_problem_corpus_index.py --json",
        "guide_missing_live_corpus_structure_check",
    ),
    (
        "ErdosProblems/WORKING_GUIDE.md",
        "aggregate axiom-audit plan",
        "guide_missing_layered_validation_boundary",
    ),
    (
        "ErdosProblems/WORKING_GUIDE.md",
        "computation_surface_routes",
        "guide_missing_computation_surface_join",
    ),
    (
        "ErdosProblems/WORKING_GUIDE.md",
        "--unclassified-role",
        "guide_missing_bounded_unclassified_script_route",
    ),
    (
        "ErdosProblems/WORKING_GUIDE.md",
        "formal_math_corpus_registry.json",
        "guide_missing_comparator_identity_registry",
    ),
    (
        "ErdosProblems/WORKING_GUIDE.md",
        "system.lib.formal_math_corpus_registry",
        "guide_missing_bounded_comparator_registry_route",
    ),
    (
        "ErdosProblems/WORKING_GUIDE.md",
        "--problem erdos_<N>",
        "guide_missing_problem_filtered_comparator_route",
    ),
    (
        "ErdosProblems/AGENTS.md",
        "corpus_navigation.py --entry --json",
        "problem_adapter_missing_corpus_entry_card_route",
    ),
    (
        "ErdosProblems/AGENTS.md",
        "recommended_routes",
        "problem_adapter_missing_corpus_entry_decision_map",
    ),
    (
        "ErdosProblems/AGENTS.md",
        "--source-overview",
        "problem_adapter_missing_corpus_source_overview_route",
    ),
    (
        "ErdosProblems/AGENTS.md",
        "--frontier-overview",
        "problem_adapter_missing_corpus_frontier_overview_route",
    ),
    (
        "ErdosProblems/AGENTS.md",
        "evidence_neighborhood",
        "problem_adapter_missing_evidence_neighborhood_route",
    ),
    (
        "ErdosProblems/AGENTS.md",
        "problem_choices",
        "problem_adapter_missing_live_problem_choice_index",
    ),
    (
        "ErdosProblems/AGENTS.md",
        "global_mathematical_connection_index",
        "problem_adapter_missing_connection_index_route",
    ),
    (
        "ErdosProblems/AGENTS.md",
        "problem_navigation_routes",
        "problem_adapter_missing_selected_problem_control_panel",
    ),
    (
        "ErdosProblems/AGENTS.md",
        "formal_math_corpus_registry.json",
        "problem_adapter_missing_comparator_identity_registry",
    ),
    (
        "ErdosProblems/AGENTS.md",
        "system.lib.formal_math_corpus_registry",
        "problem_adapter_missing_bounded_comparator_registry_route",
    ),
    (
        "ErdosProblems/AGENTS.md",
        "--problem erdos_<number>",
        "problem_adapter_missing_problem_filtered_comparator_route",
    ),
    (
        "scripts/AGENTS.md",
        "../../repo-python scripts/script_catalog.py --json",
        "script_adapter_missing_catalog_route",
    ),
    (
        "scripts/AGENTS.md",
        "../../repo-python scripts/corpus_navigation.py",
        "script_adapter_missing_corpus_navigation_route",
    ),
    (
        "scripts/AGENTS.md",
        "--role",
        "script_adapter_missing_role_filter_route",
    ),
    (
        "scripts/AGENTS.md",
        "computation_surface_routes",
        "script_adapter_missing_computation_surface_join",
    ),
    (
        "scripts/AGENTS.md",
        "--unclassified-role",
        "script_adapter_missing_bounded_unclassified_script_route",
    ),
    (
        "scripts/corpus_navigation.py",
        '"problem_choices"',
        "corpus_navigation_missing_live_problem_choice_index",
    ),
    (
        "scripts/corpus_navigation.py",
        '"global_mathematical_connection_index"',
        "corpus_navigation_missing_connection_index_route",
    ),
    (
        "scripts/corpus_navigation.py",
        '"problem_navigation_routes"',
        "corpus_navigation_missing_selected_problem_control_panel",
    ),
    (
        "scripts/corpus_navigation.py",
        '"aggregate_axiom_audit_plan"',
        "corpus_navigation_missing_layered_validation_route",
    ),
    (
        "scripts/script_catalog.py",
        "SCRIPT_ROLES",
        "script_catalog_missing_role_classification",
    ),
    (
        "scripts/script_catalog.py",
        '"--role"',
        "script_catalog_missing_role_filter",
    ),
    (
        "scripts/corpus_computation_routes.py",
        '"computation_surface_routes"',
        "corpus_computation_routes_missing_surface_join",
    ),
    (
        "scripts/corpus_computation_routes.py",
        '"classification_boundary"',
        "corpus_computation_routes_missing_classification_boundary",
    ),
    (
        "scripts/corpus_computation_routes.py",
        '"unclassified_role_choices"',
        "corpus_computation_routes_missing_unclassified_role_index",
    ),
)


def _read_json(path: Path) -> dict[str, Any]:
    payload = json.loads(path.read_text(encoding="utf-8"))
    if not isinstance(payload, dict):
        raise ValueError(f"expected a JSON object: {path}")
    return payload


def _module_path(project_root: Path, module: str) -> Path:
    return project_root.joinpath(*module.split(".")).with_suffix(".lean")


def _imports(path: Path) -> set[str]:
    imports: set[str] = set()
    for line in path.read_text(encoding="utf-8").splitlines():
        match = IMPORT_RE.match(line)
        if match:
            imports.add(match.group(1))
    return imports


def _issue(issues: list[dict[str, str]], kind: str, detail: str) -> None:
    issues.append({"kind": kind, "detail": detail})


def _strings(value: Any) -> Iterable[str]:
    return value if isinstance(value, list) and all(isinstance(item, str) for item in value) else ()


def _problem_local_adapter_markers(problem_id: str, lean_module: str) -> tuple[str, ...]:
    problem_number = problem_id.removeprefix("erdos_")
    return (
        f'--query "Erdos #{problem_number}"',
        f"--problem {problem_id} --json",
        "problem_navigation_routes",
        "research_packet.json",
        "lean_fast_build.py",
        f"--plan {lean_module}",
        f"system.lib.formal_math_corpus_registry --problem {problem_id} --json",
        "same public applicability posture",
        "not proof authority",
    )


def check(project_root: Path) -> dict[str, Any]:
    project_adapter_path = project_root / "AGENTS.md"
    manifest_path = project_root / "ErdosProblems" / "assimilation_manifest.json"
    guide_path = project_root / "ErdosProblems" / "WORKING_GUIDE.md"
    problem_adapter_path = project_root / "ErdosProblems" / "AGENTS.md"
    root_path = project_root / "ErdosProblems" / "Root.lean"
    axiom_audit_path = project_root / "ErdosProblems" / "AxiomAudit.lean"
    aggregate_path = project_root / "ErdosProblems.lean"
    script_adapter_path = project_root / "scripts" / "AGENTS.md"
    script_catalog_path = project_root / "scripts" / "script_catalog.py"
    corpus_navigation_path = project_root / "scripts" / "corpus_navigation.py"
    computation_routes_path = project_root / "scripts" / "corpus_computation_routes.py"
    issues: list[dict[str, str]] = []

    for required in (
        project_adapter_path,
        manifest_path,
        guide_path,
        problem_adapter_path,
        root_path,
        axiom_audit_path,
        aggregate_path,
        script_adapter_path,
        script_catalog_path,
        corpus_navigation_path,
        computation_routes_path,
    ):
        if not required.is_file():
            _issue(issues, "missing_required_surface", str(required.relative_to(project_root)))
    if issues:
        return {
            "kind": "problem_corpus_index_check",
            "schema_version": "problem_corpus_index_check_v0",
            "status": "FAIL",
            "summary": {"problem_count": 0, "issue_count": len(issues)},
            "issues": issues,
        }

    for relative_path, marker, issue_kind in ENTRY_ROUTE_MARKERS:
        path = project_root / relative_path
        try:
            content = path.read_text(encoding="utf-8")
        except OSError as error:
            _issue(issues, "unreadable_entry_route_surface", f"{relative_path}: {error}")
            continue
        if marker not in content:
            _issue(issues, issue_kind, f"{relative_path}: missing {marker!r}")

    try:
        manifest = _read_json(manifest_path)
    except (OSError, ValueError, json.JSONDecodeError) as error:
        _issue(issues, "invalid_manifest", str(error))
        manifest = {}

    problems = manifest.get("problems")
    if not isinstance(problems, list):
        _issue(issues, "invalid_manifest", "problems must be a list")
        problems = []
    if manifest.get("root") != "ErdosProblems.lean":
        _issue(issues, "unexpected_manifest_root", repr(manifest.get("root")))

    root_imports = _imports(root_path)
    aggregate_imports = _imports(aggregate_path)
    if "ErdosProblems.Root" not in aggregate_imports:
        _issue(issues, "aggregate_missing_root_import", "ErdosProblems.lean")
    if "ErdosProblems.AxiomAudit" not in aggregate_imports:
        _issue(issues, "aggregate_missing_axiom_audit_import", "ErdosProblems.lean")

    seen_ids: set[str] = set()
    seen_directories: set[str] = set()
    seen_modules: set[str] = set()
    checked_module_count = 0
    problem_local_adapter_count = 0

    for row_index, row in enumerate(problems):
        label = f"problems[{row_index}]"
        if not isinstance(row, dict):
            _issue(issues, "invalid_problem_row", label)
            continue

        problem_id = row.get("id")
        directory = row.get("directory")
        packet_ref = row.get("packet")
        lean_module = row.get("lean_module")
        if not all(isinstance(value, str) and value for value in (problem_id, directory, packet_ref, lean_module)):
            _issue(issues, "missing_problem_identity", label)
            continue

        for value, seen, kind in (
            (problem_id, seen_ids, "duplicate_problem_id"),
            (directory, seen_directories, "duplicate_problem_directory"),
            (lean_module, seen_modules, "duplicate_problem_module"),
        ):
            if value in seen:
                _issue(issues, kind, value)
            seen.add(value)

        directory_path = project_root / directory
        packet_path = project_root / packet_ref
        if not directory_path.is_dir():
            _issue(issues, "missing_problem_directory", directory)
        adapter_path = directory_path / "AGENTS.md"
        adapter_ref = str(adapter_path.relative_to(project_root))
        if not adapter_path.is_file():
            _issue(issues, "missing_problem_local_adapter", adapter_ref)
        else:
            try:
                adapter_content = adapter_path.read_text(encoding="utf-8")
            except OSError as error:
                _issue(issues, "unreadable_problem_local_adapter", f"{adapter_ref}: {error}")
            else:
                problem_local_adapter_count += 1
                for marker in _problem_local_adapter_markers(problem_id, lean_module):
                    if marker not in adapter_content:
                        _issue(
                            issues,
                            "problem_local_adapter_missing_marker",
                            f"{adapter_ref}: missing {marker!r}",
                        )
        if packet_path.parent != directory_path:
            _issue(
                issues,
                "research_packet_outside_problem_directory",
                f"{packet_ref}: expected under {directory}",
            )
        if not packet_path.is_file():
            _issue(issues, "missing_research_packet", packet_ref)
        else:
            try:
                packet = _read_json(packet_path)
            except (OSError, ValueError, json.JSONDecodeError) as error:
                _issue(issues, "invalid_research_packet", f"{packet_ref}: {error}")
            else:
                packet_problem_id = packet.get("problem_id")
                if packet_problem_id != problem_id:
                    _issue(
                        issues,
                        "packet_problem_id_mismatch",
                        f"{packet_ref}: expected {problem_id!r}, found {packet_problem_id!r}",
                    )

        declared_modules = (lean_module, *_strings(row.get("companion_modules")))
        for module in declared_modules:
            module_path = _module_path(project_root, module)
            checked_module_count += 1
            if not module_path.is_file():
                _issue(issues, "missing_declared_module", f"{module} ({module_path.relative_to(project_root)})")
        if lean_module not in root_imports:
            _issue(issues, "entry_module_missing_from_root", lean_module)

    problem_root = project_root / "ErdosProblems"
    discovered_problem_directories = {
        f"ErdosProblems/{path.name}"
        for path in problem_root.glob("Erdos[0-9]*")
        if path.is_dir()
    }
    for directory in sorted(discovered_problem_directories - seen_directories):
        _issue(issues, "unregistered_problem_directory", directory)

    status = "PASS" if not issues else "FAIL"
    return {
        "kind": "problem_corpus_index_check",
        "schema_version": "problem_corpus_index_check_v0",
        "status": status,
        "summary": {
            "problem_count": len(problems),
            "declared_module_count": checked_module_count,
            "root_import_count": len(root_imports),
            "entry_route_marker_count": len(ENTRY_ROUTE_MARKERS),
            "problem_local_adapter_count": problem_local_adapter_count,
            "issue_count": len(issues),
        },
        "issues": issues,
    }


def main(argv: list[str] | None = None) -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--project-root", type=Path, default=DEFAULT_PROJECT_ROOT)
    parser.add_argument("--json", action="store_true", help="emit the structured receipt")
    args = parser.parse_args(argv)

    receipt = check(args.project_root.resolve())
    if args.json:
        print(json.dumps(receipt, indent=2, sort_keys=True))
    else:
        summary = receipt["summary"]
        print(
            "problem-corpus-index: "
            f"{receipt['status']} — {summary['problem_count']} problems, "
            f"{summary['declared_module_count']} declared modules, "
            f"{summary['issue_count']} issue(s)"
        )
        for issue in receipt["issues"]:
            print(f"  {issue['kind']}: {issue['detail']}")
    return 0 if receipt["status"] == "PASS" else 1


if __name__ == "__main__":
    raise SystemExit(main())
