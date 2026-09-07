#!/usr/bin/env python3
"""Focused fixtures for ``check_problem_corpus_index.py``.

Run directly from the repository root:
``./repo-python formal_math/erdos257_period_noncollapse/scripts/test_check_problem_corpus_index.py``.
"""

from __future__ import annotations

import json
import sys
import tempfile
from pathlib import Path

from check_problem_corpus_index import ENTRY_ROUTE_MARKERS, check


def _write(path: Path, text: str) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(text, encoding="utf-8")


def _entry_route_fixture_text(relative_path: str) -> str:
    markers = [
        marker
        for route_path, marker, _ in ENTRY_ROUTE_MARKERS
        if route_path == relative_path
    ]
    return "\n".join(markers) + "\n"


def _problem_local_adapter_fixture_text() -> str:
    return "\n".join(
        (
            '--query "Erdos #1"',
            "--problem erdos_1 --json",
            "problem_navigation_routes",
            "research_packet.json",
            "lean_fast_build.py",
            "--plan ErdosProblems.Erdos1.Entry",
            "system.lib.formal_math_corpus_registry --problem erdos_1 --json",
            "same public applicability posture",
            "not proof authority",
        )
    ) + "\n"


def _fixture(root: Path) -> Path:
    project = root / "project"
    payload = {
        "schema": "aiw-problem-centric-formal-math-root/1",
        "root": "ErdosProblems.lean",
        "problems": [
            {
                "id": "erdos_1",
                "directory": "ErdosProblems/Erdos1",
                "packet": "ErdosProblems/Erdos1/research_packet.json",
                "lean_module": "ErdosProblems.Erdos1.Entry",
                "companion_modules": ["ErdosProblems.Erdos1.Helper"],
            }
        ],
    }
    _write(project / "AGENTS.md", _entry_route_fixture_text("AGENTS.md"))
    _write(project / "ErdosProblems" / "assimilation_manifest.json", json.dumps(payload))
    _write(
        project / "ErdosProblems" / "WORKING_GUIDE.md",
        _entry_route_fixture_text("ErdosProblems/WORKING_GUIDE.md"),
    )
    _write(
        project / "ErdosProblems" / "AGENTS.md",
        _entry_route_fixture_text("ErdosProblems/AGENTS.md"),
    )
    _write(project / "ErdosProblems" / "Erdos1" / "research_packet.json", '{"problem_id": "erdos_1"}')
    _write(
        project / "ErdosProblems" / "Erdos1" / "AGENTS.md",
        _problem_local_adapter_fixture_text(),
    )
    _write(project / "ErdosProblems" / "Erdos1" / "Entry.lean", "")
    _write(project / "ErdosProblems" / "Erdos1" / "Helper.lean", "")
    _write(project / "ErdosProblems" / "Root.lean", "import ErdosProblems.Erdos1.Entry\n")
    _write(project / "ErdosProblems" / "AxiomAudit.lean", "")
    _write(project / "ErdosProblems.lean", "import ErdosProblems.Root\nimport ErdosProblems.AxiomAudit\n")
    _write(
        project / "scripts" / "AGENTS.md",
        _entry_route_fixture_text("scripts/AGENTS.md"),
    )
    _write(
        project / "scripts" / "script_catalog.py",
        _entry_route_fixture_text("scripts/script_catalog.py"),
    )
    _write(
        project / "scripts" / "corpus_navigation.py",
        _entry_route_fixture_text("scripts/corpus_navigation.py"),
    )
    _write(
        project / "scripts" / "corpus_computation_routes.py",
        _entry_route_fixture_text("scripts/corpus_computation_routes.py"),
    )
    return project


def main() -> int:
    with tempfile.TemporaryDirectory() as temporary:
        project = _fixture(Path(temporary))
        valid = check(project)
        assert valid["status"] == "PASS", valid
        assert valid["summary"]["entry_route_marker_count"] == len(ENTRY_ROUTE_MARKERS)
        assert valid["summary"]["problem_local_adapter_count"] == 1

        local_adapter_path = project / "ErdosProblems" / "Erdos1" / "AGENTS.md"
        local_adapter_path.unlink()
        missing_local_adapter = check(project)
        assert missing_local_adapter["status"] == "FAIL", missing_local_adapter
        assert any(
            issue
            == {
                "kind": "missing_problem_local_adapter",
                "detail": "ErdosProblems/Erdos1/AGENTS.md",
            }
            for issue in missing_local_adapter["issues"]
        ), missing_local_adapter
        _write(local_adapter_path, _problem_local_adapter_fixture_text())

        _write(local_adapter_path, _problem_local_adapter_fixture_text().replace(
            "problem_navigation_routes\n", ""
        ))
        drifting_local_adapter = check(project)
        assert drifting_local_adapter["status"] == "FAIL", drifting_local_adapter
        assert any(
            issue
            == {
                "kind": "problem_local_adapter_missing_marker",
                "detail": (
                    "ErdosProblems/Erdos1/AGENTS.md: missing "
                    "'problem_navigation_routes'"
                ),
            }
            for issue in drifting_local_adapter["issues"]
        ), drifting_local_adapter
        _write(local_adapter_path, _problem_local_adapter_fixture_text())

        project_adapter_path = project / "AGENTS.md"
        _write(project_adapter_path, "project adapter fixture\n")
        project_adapter_drift = check(project)
        assert project_adapter_drift["status"] == "FAIL", project_adapter_drift
        assert any(
            issue
            == {
                "kind": "project_adapter_missing_corpus_entry_card_route",
                "detail": "AGENTS.md: missing 'corpus_navigation.py --entry --json'",
            }
            for issue in project_adapter_drift["issues"]
        ), project_adapter_drift
        assert any(
            issue
            == {
                "kind": "project_adapter_missing_corpus_source_overview_route",
                "detail": "AGENTS.md: missing '--source-overview'",
            }
            for issue in project_adapter_drift["issues"]
        ), project_adapter_drift
        assert any(
            issue
            == {
                "kind": "project_adapter_missing_corpus_frontier_overview_route",
                "detail": "AGENTS.md: missing '--frontier-overview'",
            }
            for issue in project_adapter_drift["issues"]
        ), project_adapter_drift
        _write(project_adapter_path, _entry_route_fixture_text("AGENTS.md"))

        guide_path = project / "ErdosProblems" / "WORKING_GUIDE.md"
        _write(guide_path, "--problem-cockpit\n")
        route_drift = check(project)
        assert route_drift["status"] == "FAIL", route_drift
        assert any(
            issue == {
                "kind": "guide_missing_source_summary_route",
                "detail": "ErdosProblems/WORKING_GUIDE.md: missing '--source-summary'",
            }
            for issue in route_drift["issues"]
        ), route_drift
        assert any(
            issue
            == {
                "kind": "guide_missing_corpus_computation_route",
                "detail": (
                    "ErdosProblems/WORKING_GUIDE.md: missing "
                    "'corpus_computation_routes.py --problem'"
                ),
            }
            for issue in route_drift["issues"]
        ), route_drift
        assert any(
            issue
            == {
                "kind": "guide_missing_source_overview_route",
                "detail": "ErdosProblems/WORKING_GUIDE.md: missing '--source-overview'",
            }
            for issue in route_drift["issues"]
        ), route_drift
        assert any(
            issue
            == {
                "kind": "guide_missing_corpus_entry_card_route",
                "detail": (
                    "ErdosProblems/WORKING_GUIDE.md: missing "
                    "'corpus_navigation.py --entry --json'"
                ),
            }
            for issue in route_drift["issues"]
        ), route_drift
        assert any(
            issue
            == {
                "kind": "guide_missing_packet_frontier_route",
                "detail": (
                    "ErdosProblems/WORKING_GUIDE.md: missing "
                    "'corpus_navigation.py --frontier-summary'"
                ),
            }
            for issue in route_drift["issues"]
        ), route_drift
        assert any(
            issue
            == {
                "kind": "guide_missing_corpus_frontier_overview_route",
                "detail": "ErdosProblems/WORKING_GUIDE.md: missing '--frontier-overview'",
            }
            for issue in route_drift["issues"]
        ), route_drift
        _write(guide_path, _entry_route_fixture_text("ErdosProblems/WORKING_GUIDE.md"))

        adapter_path = project / "ErdosProblems" / "AGENTS.md"
        _write(adapter_path, "evidence_neighborhood\n")
        adapter_drift = check(project)
        assert adapter_drift["status"] == "FAIL", adapter_drift
        assert any(
            issue
            == {
                "kind": "problem_adapter_missing_corpus_entry_card_route",
                "detail": (
                    "ErdosProblems/AGENTS.md: missing "
                    "'corpus_navigation.py --entry --json'"
                ),
            }
            for issue in adapter_drift["issues"]
        ), adapter_drift
        assert any(
            issue
            == {
                "kind": "problem_adapter_missing_corpus_source_overview_route",
                "detail": "ErdosProblems/AGENTS.md: missing '--source-overview'",
            }
            for issue in adapter_drift["issues"]
        ), adapter_drift
        assert any(
            issue
            == {
                "kind": "problem_adapter_missing_corpus_frontier_overview_route",
                "detail": "ErdosProblems/AGENTS.md: missing '--frontier-overview'",
            }
            for issue in adapter_drift["issues"]
        ), adapter_drift
        _write(adapter_path, _entry_route_fixture_text("ErdosProblems/AGENTS.md"))

        script_adapter_path = project / "scripts" / "AGENTS.md"
        _write(script_adapter_path, "script adapter fixture\n")
        script_adapter_drift = check(project)
        assert script_adapter_drift["status"] == "FAIL", script_adapter_drift
        assert any(
            issue
            == {
                "kind": "script_adapter_missing_catalog_route",
                "detail": (
                    "scripts/AGENTS.md: missing "
                    "'../../repo-python scripts/script_catalog.py --json'"
                ),
            }
            for issue in script_adapter_drift["issues"]
        ), script_adapter_drift
        assert any(
            issue
            == {
                "kind": "script_adapter_missing_corpus_navigation_route",
                "detail": (
                    "scripts/AGENTS.md: missing "
                    "'../../repo-python scripts/corpus_navigation.py'"
                ),
            }
            for issue in script_adapter_drift["issues"]
        ), script_adapter_drift
        _write(script_adapter_path, _entry_route_fixture_text("scripts/AGENTS.md"))

        corpus_navigation_path = project / "scripts" / "corpus_navigation.py"
        _write(corpus_navigation_path, '"problem_choices"\n')
        navigation_contract_drift = check(project)
        assert navigation_contract_drift["status"] == "FAIL", navigation_contract_drift
        assert any(
            issue
            == {
                "kind": "corpus_navigation_missing_selected_problem_control_panel",
                "detail": (
                    "scripts/corpus_navigation.py: missing "
                    "'\"problem_navigation_routes\"'"
                ),
            }
            for issue in navigation_contract_drift["issues"]
        ), navigation_contract_drift
        _write(
            corpus_navigation_path,
            _entry_route_fixture_text("scripts/corpus_navigation.py"),
        )

        (project / "ErdosProblems" / "Erdos1" / "Helper.lean").unlink()
        invalid = check(project)
        assert invalid["status"] == "FAIL", invalid
        assert any(issue["kind"] == "missing_declared_module" for issue in invalid["issues"]), invalid

        _write(project / "ErdosProblems" / "Erdos1" / "Helper.lean", "")
        (project / "scripts" / "script_catalog.py").unlink()
        missing_entry = check(project)
        assert missing_entry["status"] == "FAIL", missing_entry
        assert any(
            issue == {"kind": "missing_required_surface", "detail": "scripts/script_catalog.py"}
            for issue in missing_entry["issues"]
        ), missing_entry

        _write(
            project / "scripts" / "script_catalog.py",
            _entry_route_fixture_text("scripts/script_catalog.py"),
        )
        (project / "scripts" / "corpus_navigation.py").unlink()
        missing_navigation = check(project)
        assert missing_navigation["status"] == "FAIL", missing_navigation
        assert any(
            issue == {"kind": "missing_required_surface", "detail": "scripts/corpus_navigation.py"}
            for issue in missing_navigation["issues"]
        ), missing_navigation

        _write(
            project / "scripts" / "corpus_navigation.py",
            _entry_route_fixture_text("scripts/corpus_navigation.py"),
        )
        (project / "scripts" / "corpus_computation_routes.py").unlink()
        missing_computation_routes = check(project)
        assert missing_computation_routes["status"] == "FAIL", missing_computation_routes
        assert any(
            issue
            == {
                "kind": "missing_required_surface",
                "detail": "scripts/corpus_computation_routes.py",
            }
            for issue in missing_computation_routes["issues"]
        ), missing_computation_routes

        _write(
            project / "scripts" / "corpus_computation_routes.py",
            _entry_route_fixture_text("scripts/corpus_computation_routes.py"),
        )
        manifest_path = project / "ErdosProblems" / "assimilation_manifest.json"
        manifest = json.loads(manifest_path.read_text(encoding="utf-8"))
        manifest["problems"][0]["packet"] = "ErdosProblems/Elsewhere/research_packet.json"
        _write(manifest_path, json.dumps(manifest))
        _write(project / "ErdosProblems" / "Elsewhere" / "research_packet.json", '{"problem_id": "erdos_1"}')
        foreign_packet = check(project)
        assert foreign_packet["status"] == "FAIL", foreign_packet
        assert any(
            issue == {
                "kind": "research_packet_outside_problem_directory",
                "detail": "ErdosProblems/Elsewhere/research_packet.json: expected under ErdosProblems/Erdos1",
            }
            for issue in foreign_packet["issues"]
        ), foreign_packet

        manifest["problems"][0]["packet"] = "ErdosProblems/Erdos1/research_packet.json"
        _write(manifest_path, json.dumps(manifest))
        (project / "ErdosProblems" / "Erdos2").mkdir()
        orphan_directory = check(project)
        assert orphan_directory["status"] == "FAIL", orphan_directory
        assert any(
            issue == {"kind": "unregistered_problem_directory", "detail": "ErdosProblems/Erdos2"}
            for issue in orphan_directory["issues"]
        ), orphan_directory

    print("problem corpus index fixtures: PASS")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
