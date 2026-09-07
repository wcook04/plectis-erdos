#!/usr/bin/env python3
"""Fixture coverage for corpus_computation_routes.py."""

from __future__ import annotations

import json
import tempfile
from pathlib import Path

from corpus_computation_routes import computation_routes


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
                        {"id": "erdos_1"},
                        {"id": "erdos_2"},
                    ]
                }
            ),
        )
        _write(root / "scripts" / "one.py", 'problem_id = "erdos_1"\n')
        _write(root / "scripts" / "two.cpp", '{"problem_id": "erdos-2"}\n')
        _write(root / "scripts" / "unknown.py", 'problem_id = "erdos_9"\n')
        _write(root / "scripts" / "untagged.py", "print('fixture')\n")
        _write(root / "scripts" / "untagged_two.py", "print('second fixture')\n")
        _write(
            root / "scripts" / "embedded_fixture.py",
            'text = \'problem_id = "erdos_9"\'\n# problem_id = "erdos_9"\n',
        )
        _write(
            root / "ErdosProblems" / "Erdos1" / "scripts" / "owned.py",
            'problem_id = "erdos_1"\n',
        )

        overview = computation_routes(root)
        selected = computation_routes(root, problem="Erdos2")
        unclassified = computation_routes(
            root, unclassified_role="experiment_or_helper", path_limit=1
        )
        try:
            computation_routes(root, problem="999")
        except ValueError as error:
            assert "unknown manifest problem id" in str(error)
        else:
            raise AssertionError("unknown manifest problem should fail")
        try:
            computation_routes(root, unclassified_role="not_a_role")
        except ValueError as error:
            assert "unknown unclassified role" in str(error)
        else:
            raise AssertionError("unknown unclassified role should fail")
        try:
            computation_routes(
                root,
                problem="erdos_1",
                unclassified_role="experiment_or_helper",
            )
        except ValueError as error:
            assert "mutually exclusive" in str(error)
        else:
            raise AssertionError("problem and unclassified role should not compose")
        try:
            computation_routes(
                root,
                unclassified_role="experiment_or_helper",
                path_limit=0,
            )
        except ValueError as error:
            assert "path_limit must be positive" in str(error)
        else:
            raise AssertionError("non-positive path limit should fail")

    assert overview["summary"] == {
        "corpus_script_count": 6,
        "corpus_script_with_explicit_problem_id_count": 3,
        "corpus_script_without_explicit_problem_id_count": 3,
        "manifest_problem_with_explicit_corpus_script_count": 2,
        "manifest_problem_without_explicit_corpus_script_count": 0,
        "corpus_script_role_counts_by_problem_id_metadata": {
            "with_literal_problem_id": {"experiment_or_helper": 3},
            "without_literal_problem_id": {"experiment_or_helper": 3},
        },
        "unknown_declared_problem_id_count": 1,
        "unknown_declared_problem_id_role_counts": {"experiment_or_helper": 1},
        "unknown_declared_problem_id_links_preview": [
            {
                "path": "scripts/unknown.py",
                "declared_problem_id": "erdos_9",
                "role": "experiment_or_helper",
            }
        ],
        "omitted_unknown_declared_problem_id_link_count": 0,
        "unclassified_role_choices": [
            {
                "role": "experiment_or_helper",
                "script_count": 3,
                "representative_paths": [
                    "scripts/embedded_fixture.py",
                    "scripts/untagged.py",
                    "scripts/untagged_two.py",
                ],
                "omitted_path_count": 0,
                "bounded_drilldown_command": (
                    "./repo-python formal_math/erdos257_period_noncollapse/scripts/"
                    "corpus_computation_routes.py --unclassified-role "
                    "experiment_or_helper --path-limit 40 --json"
                ),
            }
        ],
    }
    assert overview["problems"] == [
        {
            "problem_id": "erdos_1",
            "explicit_corpus_script_count": 1,
            "explicit_corpus_script_role_counts": {"experiment_or_helper": 1},
            "representative_paths": ["scripts/one.py"],
            "omitted_path_count": 0,
            "drilldown_command": (
                "./repo-python formal_math/erdos257_period_noncollapse/scripts/"
                "corpus_computation_routes.py "
                "--problem erdos_1 --json"
            ),
            "problem_cockpit_command": (
                "./repo-python -m system.lib.mathematical_working_memory "
                "--query 'Erdos #1' --problem-cockpit --context-budget 12000"
            ),
            "source_topology_command": (
                "./repo-python formal_math/erdos257_period_noncollapse/scripts/"
                "corpus_navigation.py --problem erdos_1 --source-summary --json"
            ),
            "bounded_source_inventory_command": (
                "./repo-python formal_math/erdos257_period_noncollapse/scripts/"
                "corpus_navigation.py --problem erdos_1 --source-paths "
                "--source-kind markdown --source-path-limit 40 --json"
            ),
            "computation_surface_routes": {
                "physically_problem_owned_scripts": (
                    "./repo-python formal_math/erdos257_period_noncollapse/scripts/"
                    "script_catalog.py --problem erdos_1 --json"
                ),
                "literal_corpus_script_metadata": (
                    "./repo-python formal_math/erdos257_period_noncollapse/scripts/"
                    "corpus_computation_routes.py --problem erdos_1 --json"
                ),
                "packet_bound_probe_receipts": (
                    "./repo-python -m system.lib.formal_math_probe_registry "
                    "--problem erdos_1 --coverage"
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
        },
        {
            "problem_id": "erdos_2",
            "explicit_corpus_script_count": 1,
            "explicit_corpus_script_role_counts": {"experiment_or_helper": 1},
            "representative_paths": ["scripts/two.cpp"],
            "omitted_path_count": 0,
            "drilldown_command": (
                "./repo-python formal_math/erdos257_period_noncollapse/scripts/"
                "corpus_computation_routes.py "
                "--problem erdos_2 --json"
            ),
            "problem_cockpit_command": (
                "./repo-python -m system.lib.mathematical_working_memory "
                "--query 'Erdos #2' --problem-cockpit --context-budget 12000"
            ),
            "source_topology_command": (
                "./repo-python formal_math/erdos257_period_noncollapse/scripts/"
                "corpus_navigation.py --problem erdos_2 --source-summary --json"
            ),
            "bounded_source_inventory_command": (
                "./repo-python formal_math/erdos257_period_noncollapse/scripts/"
                "corpus_navigation.py --problem erdos_2 --source-paths "
                "--source-kind markdown --source-path-limit 40 --json"
            ),
            "computation_surface_routes": {
                "physically_problem_owned_scripts": (
                    "./repo-python formal_math/erdos257_period_noncollapse/scripts/"
                    "script_catalog.py --problem erdos_2 --json"
                ),
                "literal_corpus_script_metadata": (
                    "./repo-python formal_math/erdos257_period_noncollapse/scripts/"
                    "corpus_computation_routes.py --problem erdos_2 --json"
                ),
                "packet_bound_probe_receipts": (
                    "./repo-python -m system.lib.formal_math_probe_registry "
                    "--problem erdos_2 --coverage"
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
        },
    ]
    assert selected["filters"] == {
        "problem_id": "erdos_2",
        "unclassified_role": None,
        "path_limit": None,
    }
    assert selected["problems"][0]["explicit_corpus_script_role_counts"] == {
        "experiment_or_helper": 1
    }
    assert selected["problems"][0]["corpus_scripts"] == [
        {
            "path": "scripts/two.cpp",
            "role": "experiment_or_helper",
            "language": "cpp",
            "declared_problem_ids": ["erdos_2"],
            "route_reason": "literal_problem_id_metadata",
        }
    ]
    assert unclassified["filters"] == {
        "problem_id": None,
        "unclassified_role": "experiment_or_helper",
        "path_limit": 1,
    }
    assert unclassified["problems"] == []
    assert unclassified["unclassified_corpus_scripts"] == [
        {
            "path": "scripts/embedded_fixture.py",
            "role": "experiment_or_helper",
            "language": "py",
            "classification_state": "no_literal_problem_id_metadata",
        }
    ]
    assert unclassified["omitted_unclassified_corpus_script_count"] == 2
    print("corpus computation routes fixtures: PASS")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
