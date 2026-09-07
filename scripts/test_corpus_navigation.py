#!/usr/bin/env python3
"""Self-contained fixture coverage for corpus_navigation.py."""

from __future__ import annotations

import json
import tempfile
from pathlib import Path

from corpus_navigation import entry_card, navigation_map


def _write(path: Path, text: str) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(text, encoding="utf-8")


def main() -> int:
    with tempfile.TemporaryDirectory() as temporary_directory:
        root = Path(temporary_directory)
        _write(
            root / "ErdosProblems" / "assimilation_manifest.json",
            json.dumps(
                {
                    "problems": [
                        {
                            "id": "erdos_1",
                            "directory": "ErdosProblems/Erdos1",
                            "packet": "ErdosProblems/Erdos1/research_packet.json",
                            "lean_module": "ErdosProblems.Erdos1.Entry",
                            "companion_modules": [
                                "ErdosProblems.Erdos1.Helper",
                                "Erdos257PeriodNoncollapse.Compatibility",
                                "Erdos257PeriodNoncollapse.Missing",
                            ],
                        },
                        {
                            "id": "erdos_2",
                            "directory": "ErdosProblems/Erdos2",
                            "packet": "ErdosProblems/Erdos2/research_packet.json",
                            "lean_module": "ErdosProblems.Erdos2.Entry",
                        },
                    ]
                }
            ),
        )
        _write(
            root / "ErdosProblems" / "Erdos1" / "research_packet.json",
            json.dumps(
                {
                    "problem_id": "erdos_1",
                    "title": "Fixture one",
                    "target": {"statement": "Fixture target one", "status": "open"},
                    "claim_ceiling": "Fixture claim ceiling one",
                    "open_producers": [
                        {"id": "producer_one"},
                        {"id": "producer_two"},
                        {"id": "producer_three"},
                        {"id": "producer_four"},
                        {"id": "producer_five"},
                    ],
                    "exact_results": [
                        {"id": "exact_one"},
                        {"id": "exact_two"},
                        {"id": "exact_three"},
                        {"id": "exact_four"},
                        {"id": "exact_five"},
                    ],
                    "negative_results": [
                        {"id": "negative_one"},
                        {"id": "negative_two"},
                        {"id": "negative_three"},
                        {"id": "negative_four"},
                        {"id": "negative_five"},
                    ],
                    "source_returns": [{}],
                    "landed_formal_source": {"module": "ErdosProblems.Erdos1.Entry"},
                }
            ),
        )
        _write(
            root / "ErdosProblems" / "Erdos2" / "research_packet.json",
            json.dumps(
                {
                    "problem_id": "erdos_2",
                    "title": "Fixture two",
                    "target": {"statement": "Fixture target two", "status": "open"},
                    "claim_ceiling": "Fixture claim ceiling two",
                    "open_producers": [],
                    "exact_results": [{"id": "exact_six"}],
                    "negative_results": [{"id": "negative_six"}],
                    "source_returns": [],
                }
            ),
        )
        _write(root / "scripts" / "corpus_helper.py", "# fixture\n")
        _write(root / "ErdosProblems" / "papers" / "erdos-1-navigation-note.tex", "% fixture\n")
        _write(root / "ErdosProblems" / "papers" / "erdos-2-published-copy.pdf", "% fixture\n")
        _write(root / "ErdosProblems" / "Erdos1" / "Entry.lean", "-- fixture\n")
        _write(root / "ErdosProblems" / "Erdos1" / "Helper.lean", "-- fixture\n")
        _write(root / "Erdos257PeriodNoncollapse" / "Compatibility.lean", "-- fixture\n")
        _write(root / "ErdosProblems" / "Erdos1" / "prior_attempt.md", "# fixture\n")
        _write(root / "ErdosProblems" / "Erdos1" / "scripts" / "check_first.py", "# fixture\n")
        _write(root / "ErdosProblems" / "Erdos1" / "scripts" / "verify_second.py", "# fixture\n")
        _write(root / "ErdosProblems" / "Erdos2" / "scripts" / "search.cpp", "// fixture\n")

        payload = navigation_map(root)
        entry = entry_card(root)
        selected = navigation_map(root, problem="Erdos1")
        source_selected = navigation_map(root, problem="Erdos1", include_source_paths=True)
        bounded_markdown_inventory = navigation_map(
            root,
            problem="Erdos1",
            include_source_paths=True,
            source_kind="markdown",
            source_path_limit=1,
        )
        source_summary_selected = navigation_map(
            root, problem="Erdos1", include_source_summary=True
        )
        source_overview = navigation_map(root, include_source_overview=True)
        frontier_payload = navigation_map(root, include_frontier_summary=True)
        frontier_overview = navigation_map(root, include_frontier_overview=True)
        selected_frontier = navigation_map(root, problem="Erdos1", include_frontier_summary=True)
        try:
            navigation_map(root, include_source_paths=True)
        except ValueError as error:
            assert "source-path inventory requires --problem" in str(error)
        else:
            raise AssertionError("all-problem source inventory should fail")
        try:
            navigation_map(root, include_source_summary=True)
        except ValueError as error:
            assert "source summary requires --problem" in str(error)
        else:
            raise AssertionError("all-problem source summary should fail")
        try:
            navigation_map(root, problem="Erdos1", source_kind="markdown")
        except ValueError as error:
            assert "source-kind requires --source-paths" in str(error)
        else:
            raise AssertionError("source-kind without source paths should fail")
        try:
            navigation_map(
                root,
                problem="Erdos1",
                include_source_paths=True,
                source_path_limit=1,
            )
        except ValueError as error:
            assert "source-path-limit requires --source-kind" in str(error)
        else:
            raise AssertionError("source-path-limit without source kind should fail")
        try:
            navigation_map(
                root,
                problem="Erdos1",
                include_source_paths=True,
                source_kind="markdown",
                source_path_limit=0,
            )
        except ValueError as error:
            assert "source-path-limit must be positive" in str(error)
        else:
            raise AssertionError("nonpositive source-path limit should fail")
        try:
            navigation_map(
                root,
                include_frontier_summary=True,
                include_frontier_overview=True,
            )
        except ValueError as error:
            assert "alternative views" in str(error)
        else:
            raise AssertionError("frontier views should be mutually exclusive")
        try:
            navigation_map(root, problem="999")
        except ValueError as error:
            assert "unknown manifest problem id" in str(error)
        else:
            raise AssertionError("unknown problem should fail")

    assert payload["summary"] == {
        "problem_count": 2,
        "problem_owned_script_count": 3,
        "companion_module_count": 3,
        "owner_namespace_companion_module_count": 1,
        "outside_problem_namespace_companion_module_count": 2,
        "staged_paper_tex_source_count": 1,
    }
    assert entry == {
        "schema_version": "lean_corpus_entry_v0",
        "kind": "lean_corpus_entry",
        "boundary": (
            "First-contact routing only; no research packet is opened, no computation "
            "is run, and no mathematical status is inferred."
        ),
        "summary": {"problem_count": 2, "problem_ids": ["erdos_1", "erdos_2"]},
        "problem_choices": [
            {
                "problem_id": "erdos_1",
                "owner_directory": "ErdosProblems/Erdos1",
                "research_packet": "ErdosProblems/Erdos1/research_packet.json",
                "supported_lean_module": "ErdosProblems.Erdos1.Entry",
                "focused_lean_build_plan": (
                    "./repo-python formal_math/erdos257_period_noncollapse/scripts/"
                    "lean_fast_build.py --plan ErdosProblems.Erdos1.Entry"
                ),
            },
            {
                "problem_id": "erdos_2",
                "owner_directory": "ErdosProblems/Erdos2",
                "research_packet": "ErdosProblems/Erdos2/research_packet.json",
                "supported_lean_module": "ErdosProblems.Erdos2.Entry",
                "focused_lean_build_plan": (
                    "./repo-python formal_math/erdos257_period_noncollapse/scripts/"
                    "lean_fast_build.py --plan ErdosProblems.Erdos2.Entry"
                ),
            },
        ],
        "recommended_routes": {
            "choose_problem_from_compact_packet_metadata": "all_problem_frontier_overview",
            "map_corpus_source_shape_before_opening_a_problem": "all_problem_source_topology",
            "locate_cross_problem_computation_families": "cross_problem_computation_overview",
            "inspect_cross_problem_mathematical_connections": (
                "global_mathematical_connection_index"
            ),
            "inspect_corpus_structure_before_mutation": "corpus_structure_check",
            "inspect_supported_aggregate_assumptions": "aggregate_axiom_audit_plan",
            "plan_selected_problem_lean_validation": (
                "problem_choices[].focused_lean_build_plan"
            ),
            "inspect_declared_corpus_scripts_for_a_selected_problem": (
                "explicit_corpus_computation_routes_template"
            ),
            "inspect_papers_comparators_or_research_for_a_selected_problem": (
                "problem_cockpit_template"
            ),
            "route_an_incoming_research_return_for_a_selected_problem": (
                "assimilation_surface_template"
            ),
            "inspect_one_large_source_kind_without_dumping_all_paths": (
                "bounded_source_inventory_template"
            ),
        },
        "routes": {
            "problem_cockpit_template": (
                "./repo-python -m system.lib.mathematical_working_memory "
                "--query 'Erdos #<number>' --problem-cockpit --context-budget 12000"
            ),
            "assimilation_surface_template": (
                "./repo-python formal_math/erdos257_period_noncollapse/scripts/"
                "assimilation_surface.py --problem <number>"
            ),
            "all_problem_frontier": (
                "./repo-python formal_math/erdos257_period_noncollapse/scripts/"
                "corpus_navigation.py --frontier-summary --json"
            ),
            "all_problem_frontier_overview": (
                "./repo-python formal_math/erdos257_period_noncollapse/scripts/"
                "corpus_navigation.py --frontier-overview --json"
            ),
            "selected_problem_frontier_template": (
                "./repo-python formal_math/erdos257_period_noncollapse/scripts/"
                "corpus_navigation.py --problem erdos_<number> --frontier-summary --json"
            ),
            "cross_problem_computation_overview": (
                "./repo-python -m system.lib.formal_math_probe_registry --overview"
            ),
            "global_mathematical_connection_index": (
                "./repo-python -m system.lib.mathematical_working_memory --mode global "
                "--query 'Lean corpus connection index' --context-budget 12000"
            ),
            "corpus_structure_check": (
                "./repo-python formal_math/erdos257_period_noncollapse/scripts/"
                "check_problem_corpus_index.py --json"
            ),
            "release_aggregate_build_plan": (
                "./repo-python formal_math/erdos257_period_noncollapse/scripts/"
                "lean_fast_build.py --plan ErdosProblems.Root"
            ),
            "aggregate_axiom_audit_plan": (
                "./repo-python formal_math/erdos257_period_noncollapse/scripts/"
                "lean_fast_build.py --plan ErdosProblems.AxiomAudit"
            ),
            "explicit_corpus_computation_routes_template": (
                "./repo-python formal_math/erdos257_period_noncollapse/scripts/"
                "corpus_computation_routes.py --problem erdos_<number> --json"
            ),
            "source_topology_template": (
                "./repo-python formal_math/erdos257_period_noncollapse/scripts/"
                "corpus_navigation.py --problem erdos_<number> --source-summary --json"
            ),
            "bounded_source_inventory_template": (
                "./repo-python formal_math/erdos257_period_noncollapse/scripts/"
                "corpus_navigation.py --problem erdos_<number> --source-paths "
                "--source-kind markdown --source-path-limit 40 --json"
            ),
            "all_problem_source_topology": (
                "./repo-python formal_math/erdos257_period_noncollapse/scripts/"
                "corpus_navigation.py --source-overview --json"
            ),
        },
        "first_action": (
            "Choose one listed problem id, then replace <number> in "
            "problem_cockpit_template before reading a packet or source tree. For Lean "
            "validation, use that choice's focused_lean_build_plan first; reserve "
            "release_aggregate_build_plan for the separate integration gate."
        ),
    }
    assert selected["filters"] == {
        "problem_id": "erdos_1",
        "source_paths": False,
        "source_summary": False,
        "source_overview": False,
    }
    assert len(selected["problems"]) == 1
    selected_problem = dict(selected["problems"][0])
    selected_problem_navigation_routes = selected_problem.pop("problem_navigation_routes")
    assert selected_problem == {
            "id": "erdos_1",
            "directory": "ErdosProblems/Erdos1",
            "packet": "ErdosProblems/Erdos1/research_packet.json",
            "lean_module": "ErdosProblems.Erdos1.Entry",
            "companion_module_count": 3,
            "owner_namespace_companion_module_count": 1,
            "outside_problem_namespace_companion_module_count": 2,
            "problem_owned_script_count": 2,
            "staged_paper_tex_paths": ["ErdosProblems/papers/erdos-1-navigation-note.tex"],
    }
    assert source_selected["filters"] == {
        "problem_id": "erdos_1",
        "source_paths": True,
        "source_summary": False,
        "source_overview": False,
    }
    assert source_selected["problems"][0]["lean_source_paths"] == [
        "ErdosProblems/Erdos1/Entry.lean",
        "ErdosProblems/Erdos1/Helper.lean",
    ]
    assert source_selected["problems"][0]["markdown_note_paths"] == ["ErdosProblems/Erdos1/prior_attempt.md"]
    assert source_selected["problems"][0]["problem_script_paths"] == [
        "ErdosProblems/Erdos1/scripts/check_first.py",
        "ErdosProblems/Erdos1/scripts/verify_second.py",
    ]
    assert bounded_markdown_inventory["filters"] == {
        "problem_id": "erdos_1",
        "source_paths": True,
        "source_summary": False,
        "source_overview": False,
        "source_kind": "markdown",
        "source_path_limit": 1,
    }
    assert bounded_markdown_inventory["problems"][0]["source_inventory"] == {
        "kind": "markdown",
        "paths": ["ErdosProblems/Erdos1/prior_attempt.md"],
        "total_path_count": 1,
        "omitted_path_count": 0,
    }
    assert source_summary_selected["filters"] == {
        "problem_id": "erdos_1",
        "source_paths": False,
        "source_summary": True,
        "source_overview": False,
    }
    assert source_summary_selected["problems"][0]["source_summary"] == {
        "owner_directory_source_counts": {
            "lean_source_count": 2,
            "markdown_note_count": 1,
            "problem_script_count": 2,
        },
        "supported_entry_source": {
            "module": "ErdosProblems.Erdos1.Entry",
            "path": "ErdosProblems/Erdos1/Entry.lean",
        },
        "manifest_companion_lean_sources": [
            {
                "module": "ErdosProblems.Erdos1.Helper",
                "path": "ErdosProblems/Erdos1/Helper.lean",
                "relative_to_problem_owner": "within_problem_directory",
            },
            {
                "module": "Erdos257PeriodNoncollapse.Compatibility",
                "path": "Erdos257PeriodNoncollapse/Compatibility.lean",
                "relative_to_problem_owner": "outside_problem_directory",
            },
            {
                "module": "Erdos257PeriodNoncollapse.Missing",
                "path": None,
                "relative_to_problem_owner": "missing_source",
            },
        ],
        "boundary": (
            "Filesystem and manifest routing only; source presence and location do "
            "not imply proof status, mathematical relevance, or publication state."
        ),
    }
    assert source_summary_selected["problems"][0]["problem_cockpit_command"] == (
        "./repo-python -m system.lib.mathematical_working_memory "
        "--query 'Erdos #1' --problem-cockpit --context-budget 12000"
    )
    assert source_summary_selected["problems"][0]["source_inventory_command"] == (
        "./repo-python formal_math/erdos257_period_noncollapse/"
        "scripts/corpus_navigation.py --problem erdos_1 --source-paths --json"
    )
    assert source_summary_selected["problems"][0]["bounded_source_inventory_commands"] == {
        kind: (
            "./repo-python formal_math/erdos257_period_noncollapse/"
            f"scripts/corpus_navigation.py --problem erdos_1 --source-paths "
            f"--source-kind {kind} --source-path-limit 40 --json"
        )
        for kind in ("lean", "markdown", "script")
    }
    assert source_overview["filters"] == {
        "problem_id": None,
        "source_paths": False,
        "source_summary": False,
        "source_overview": True,
    }
    assert source_overview["summary"]["source_overview"] == {
        "owner_directory_source_counts": {
            "lean_source_count": 2,
            "markdown_note_count": 1,
            "problem_script_count": 3,
        },
        "supported_entry_source_count": 1,
        "manifest_companion_source_location_counts": {
            "missing_source": 1,
            "outside_problem_directory": 1,
            "within_problem_directory": 1,
        },
    }
    assert source_overview["problems"][0]["source_overview"] == {
        "owner_directory_source_counts": {
            "lean_source_count": 2,
            "markdown_note_count": 1,
            "problem_script_count": 2,
        },
        "supported_entry_source": {
            "module": "ErdosProblems.Erdos1.Entry",
            "path": "ErdosProblems/Erdos1/Entry.lean",
        },
        "manifest_companion_source_location_counts": {
            "missing_source": 1,
            "outside_problem_directory": 1,
            "within_problem_directory": 1,
        },
    }
    assert source_overview["problems"][0]["source_topology_command"] == (
        "./repo-python formal_math/erdos257_period_noncollapse/"
        "scripts/corpus_navigation.py --problem erdos_1 --source-summary --json"
    )
    assert frontier_payload["summary"] == {
        "problem_count": 2,
        "problem_owned_script_count": 3,
        "companion_module_count": 3,
        "owner_namespace_companion_module_count": 1,
        "outside_problem_namespace_companion_module_count": 2,
        "staged_paper_tex_source_count": 1,
        "frontier_packet_count": 2,
        "open_producer_count": 5,
        "exact_result_id_count": 6,
        "negative_result_id_count": 6,
        "packet_record_totals": {
            "source_returns": 1,
            "landed_formal_source": 1,
        },
        "packet_record_field_presence_counts": {
            "exact_results": 2,
            "negative_results": 2,
            "source_returns": 2,
            "landed_formal_source": 1,
        },
    }
    assert frontier_payload["problems"][0]["packet_frontier"] == {
        "packet_title": "Fixture one",
        "target": {"statement": "Fixture target one", "status": "open"},
        "canonical_frontier": {"kind": "declared_target", "producer_ids": []},
        "producer_relations": {},
        "open_producer_semantics": "candidate_route_inventory_not_frontier_authority",
        "claim_ceiling_source": "ErdosProblems/Erdos1/research_packet.json::claim_ceiling",
        "claim_ceiling_character_count": len("Fixture claim ceiling one"),
        "open_producer_count": 5,
        "exact_result_id_count": 5,
        "negative_result_id_count": 5,
        "negative_result_record_count": 5,
        "negative_result_identifier_status": "all_records_identified",
        "representative_open_producer_ids": [
            "producer_one",
            "producer_two",
            "producer_three",
            "producer_four",
        ],
        "omitted_open_producer_count": 1,
        "representative_exact_result_ids": [
            "exact_one",
            "exact_two",
            "exact_three",
            "exact_four",
        ],
        "omitted_exact_result_id_count": 1,
        "representative_negative_result_ids": [
            "negative_one",
            "negative_two",
            "negative_three",
            "negative_four",
        ],
        "omitted_negative_result_id_count": 1,
        "packet_record_counts": {
            "exact_results": 5,
            "negative_results": 5,
            "source_returns": 1,
            "landed_formal_source": 1,
        },
    }
    assert frontier_overview["filters"] == {
        "problem_id": None,
        "source_paths": False,
        "source_summary": False,
        "source_overview": False,
        "frontier_overview": True,
    }
    assert frontier_overview["summary"] == {
        "problem_count": 2,
        "frontier_packet_count": 2,
        "open_producer_count": 5,
        "exact_result_id_count": 6,
        "negative_result_id_count": 6,
        "packet_record_totals": {
            "exact_results": 6,
            "negative_results": 6,
            "source_returns": 1,
            "landed_formal_source": 1,
        },
        "packet_record_field_presence_counts": {
            "exact_results": 2,
            "negative_results": 2,
            "source_returns": 2,
            "landed_formal_source": 1,
        },
    }
    assert frontier_overview["problems"][0] == {
        "id": "erdos_1",
        "packet_title": "Fixture one",
        "packet_declared_target_status": "open",
        "problem_cockpit_command": (
            "./repo-python -m system.lib.mathematical_working_memory "
            "--query 'Erdos #1' --problem-cockpit --context-budget 12000"
        ),
        "frontier_record_counts": {
            "candidate_routes_not_frontier": 5,
            "exact_result_ids": 5,
            "negative_result_ids": 5,
            "packet_records": {
                "exact_results": 5,
                "negative_results": 5,
                "source_returns": 1,
                "landed_formal_source": 1,
            },
        },
        "canonical_frontier": {"kind": "declared_target", "producer_ids": []},
        "frontier_detail_command": (
            "./repo-python formal_math/erdos257_period_noncollapse/"
            "scripts/corpus_navigation.py --problem erdos_1 --frontier-summary --json"
        ),
        "source_topology_command": (
            "./repo-python formal_math/erdos257_period_noncollapse/"
            "scripts/corpus_navigation.py --problem erdos_1 --source-summary --json"
        ),
        "bounded_source_inventory_command": (
            "./repo-python formal_math/erdos257_period_noncollapse/"
            "scripts/corpus_navigation.py --problem erdos_1 --source-paths "
            "--source-kind markdown --source-path-limit 40 --json"
        ),
        "explicit_corpus_computation_routes_command": (
            "./repo-python formal_math/erdos257_period_noncollapse/"
            "scripts/corpus_computation_routes.py --problem erdos_1 --json"
        ),
    }
    assert selected_frontier["filters"] == {
        "problem_id": "erdos_1",
        "source_paths": False,
        "source_summary": False,
        "source_overview": False,
        "frontier_summary": True,
    }
    assert selected_frontier["problems"][0]["packet_frontier"]["open_producer_ids"] == [
        "producer_one",
        "producer_two",
        "producer_three",
        "producer_four",
        "producer_five",
    ]
    assert selected_frontier["problems"][0]["packet_frontier"]["exact_result_ids"] == [
        "exact_one",
        "exact_two",
        "exact_three",
        "exact_four",
        "exact_five",
    ]
    assert selected_frontier["problems"][0]["packet_frontier"]["negative_result_ids"] == [
        "negative_one",
        "negative_two",
        "negative_three",
        "negative_four",
        "negative_five",
    ]
    assert selected_frontier["problems"][0]["frontier_drilldown_command"] == (
        "./repo-python -m system.lib.mathematical_working_memory "
        "--query 'Erdos #1' --problem-cockpit --context-budget 12000"
    )
    assert selected_problem_navigation_routes == {
        "problem_cockpit": (
            "./repo-python -m system.lib.mathematical_working_memory "
            "--query 'Erdos #1' --problem-cockpit --context-budget 12000"
        ),
        "assimilation_surface": (
            "./repo-python formal_math/erdos257_period_noncollapse/scripts/"
            "assimilation_surface.py --problem 1"
        ),
        "packet_frontier": (
            "./repo-python formal_math/erdos257_period_noncollapse/"
            "scripts/corpus_navigation.py --problem erdos_1 --frontier-summary --json"
        ),
        "source_topology": (
            "./repo-python formal_math/erdos257_period_noncollapse/"
            "scripts/corpus_navigation.py --problem erdos_1 --source-summary --json"
        ),
        "source_inventory": (
            "./repo-python formal_math/erdos257_period_noncollapse/"
            "scripts/corpus_navigation.py --problem erdos_1 --source-paths --json"
        ),
        "bounded_source_inventory": (
            "./repo-python formal_math/erdos257_period_noncollapse/"
            "scripts/corpus_navigation.py --problem erdos_1 --source-paths "
            "--source-kind markdown --source-path-limit 40 --json"
        ),
        "packet_bound_computation_coverage": (
            "./repo-python -m system.lib.formal_math_probe_registry "
            "--problem erdos_1 --coverage"
        ),
        "explicit_corpus_computation_routes": (
            "./repo-python formal_math/erdos257_period_noncollapse/"
            "scripts/corpus_computation_routes.py --problem erdos_1 --json"
        ),
        "corpus_structure_check": (
            "./repo-python formal_math/erdos257_period_noncollapse/scripts/"
            "check_problem_corpus_index.py --json"
        ),
        "aggregate_axiom_audit_plan": (
            "./repo-python formal_math/erdos257_period_noncollapse/scripts/"
            "lean_fast_build.py --plan ErdosProblems.AxiomAudit"
        ),
        "focused_lean_build_plan": (
            "./repo-python formal_math/erdos257_period_noncollapse/"
            "scripts/lean_fast_build.py --plan ErdosProblems.Erdos1.Entry"
        ),
        "release_aggregate_build_plan": (
            "./repo-python formal_math/erdos257_period_noncollapse/scripts/"
            "lean_fast_build.py --plan ErdosProblems.Root"
        ),
    }
    assert (
        selected_frontier["problems"][0]["frontier_navigation_routes"]
        == selected_problem_navigation_routes
    )
    print("corpus navigation fixtures: PASS")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
