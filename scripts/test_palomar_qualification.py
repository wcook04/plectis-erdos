#!/usr/bin/env python3
"""Focused contract tests for the local Palomar qualification product."""

from __future__ import annotations

import copy
import json
import os
import subprocess
import sys
import tempfile
from pathlib import Path

import check_palomar_qualification as checker


ROOT = Path(__file__).resolve().parents[1]
CHECKER = ROOT / "scripts" / "check_palomar_qualification.py"


def expect_unsafe(path: Path, root: Path, label: str) -> None:
    try:
        checker.safe_text(path, root=root)
    except checker.UnsafeQualificationInput:
        return
    raise AssertionError(f"qualification input escaped safe boundary: {label}")


def test_safe_input_boundary() -> None:
    with tempfile.TemporaryDirectory(prefix="palomar-input-") as raw_workspace:
        workspace = Path(raw_workspace)
        regular = workspace / "regular.txt"
        regular.write_text("qualification input\n", encoding="utf-8")
        if checker.safe_text(regular, root=workspace) != "qualification input\n":
            raise AssertionError("qualification regular-file input was not read")

        directory = workspace / "directory"
        directory.mkdir()
        expect_unsafe(directory, workspace, "directory")

        symlink = workspace / "symlink.txt"
        symlink.symlink_to(regular)
        expect_unsafe(symlink, workspace, "symlink")

        if hasattr(os, "mkfifo"):
            fifo = workspace / "fifo"
            os.mkfifo(fifo)
            expect_unsafe(fifo, workspace, "FIFO")


def run_checker(*extra: str) -> dict:
    result = subprocess.run(
        [sys.executable, str(CHECKER), "--json", *extra],
        cwd=ROOT,
        check=False,
        stdout=subprocess.PIPE,
        stderr=subprocess.PIPE,
        text=True,
    )
    assert result.returncode == 0, result.stdout + result.stderr
    return json.loads(result.stdout)


def test_normal_and_optimised_checker_agree() -> None:
    normal = run_checker()
    optimised = subprocess.run(
        [sys.executable, "-O", str(CHECKER), "--json"],
        cwd=ROOT,
        check=False,
        stdout=subprocess.PIPE,
        stderr=subprocess.PIPE,
        text=True,
    )
    assert optimised.returncode == 0, optimised.stdout + optimised.stderr
    assert json.loads(optimised.stdout) == normal
    assert normal["ok"] is True
    assert normal["decision"] == "NOT_READY"
    assert normal["structural_deficits"] == [
        "classification_metadata",
        "formalization_v04_metadata",
        "project_description",
        "responsible_maintainers",
        "source_origin_consistency",
        "source_relationship_metadata",
        "v04_source_relationship_vocabulary",
    ]


def test_v04_profile_rejects_missing_source_relationship() -> None:
    valid_shape = """version: \"v0.4\"
project:
  description: \"A checked mathematical project.\"
  responsible_maintainers:
    - \"Will Cook\"
sources:
  - title: \"A source\"
    type: \"other\"
    relationship: \"formalizes\"
classification:
  arxiv: [math.NT]
  msc2020: []
automation:
  methods:
    - method: \"manual\"
review:
  status: \"unchecked\"
"""
    assert checker.formalization_metadata_deficits(valid_shape) == []
    damaged = valid_shape.replace('    relationship: "formalizes"\n', "")
    deficits = checker.formalization_metadata_deficits(damaged)
    assert "source_relationship_metadata" in deficits
    assert "source_origin_consistency" in deficits


def test_generated_formalization_reads_committed_head_only() -> None:
    committed = checker.committed_text(ROOT, "formalization.yaml")
    worktree = (ROOT / "formalization.yaml").read_text(encoding="utf-8")
    expected = subprocess.check_output(
        ["git", "show", "HEAD:formalization.yaml"], cwd=ROOT
    ).decode("utf-8")
    assert committed == expected
    if worktree != committed:
        assert checker.committed_text(ROOT, "formalization.yaml") != worktree


def test_structural_qualification_ignores_mutable_source_reads() -> None:
    showcase = json.loads((ROOT / "docs/PALOMAR_RESULT_SHOWCASE.json").read_text())
    reconciliation = json.loads(
        (ROOT / "docs/PALOMAR_POLICY_RECONCILIATION.json").read_text()
    )
    original_safe_text = checker.safe_text

    def poisoned_worktree(path: Path, *, root: Path) -> str:
        value = original_safe_text(path, root=root)
        if path.name == "CertificateKernel.lean":
            return value.replace("irrational_erdosSum_full_support", "poisoned_source_name")
        return value

    checker.safe_text = poisoned_worktree
    try:
        errors, _ = checker.static_requirement_errors(ROOT, reconciliation, showcase)
    finally:
        checker.safe_text = original_safe_text
    assert not any("selected candidate" in error for error in errors)


def test_pinned_classification_authorities_are_required() -> None:
    reconciliation = json.loads(
        (ROOT / "docs/PALOMAR_POLICY_RECONCILIATION.json").read_text()
    )
    damaged = copy.deepcopy(reconciliation)
    damaged["official_authorities"] = [
        row
        for row in damaged["official_authorities"]
        if row["path"] != "taxonomies/arxiv-categories.json"
    ]
    errors = checker.authority_errors(damaged)
    assert any("arxiv-categories.json" in error for error in errors)


def test_full_current_roster_and_eight_problem_crosswalk() -> None:
    showcase = json.loads((ROOT / "docs/PALOMAR_RESULT_SHOWCASE.json").read_text())
    comparator = json.loads(
        subprocess.check_output(["git", "show", "HEAD:verification/comparator.json"], cwd=ROOT)
    )
    names = [
        name
        for row in showcase["frontier_by_problem"]
        for name in row["comparator_declarations"]
    ]
    assert len(names) == 32
    assert len(names) == len(set(names))
    assert [row["problem"] for row in showcase["frontier_by_problem"]] == [68, 243, 249, 251, 257, 269, 1041, 1049]
    assert showcase["candidate_selection"]["declaration"] in names
    assert showcase["candidate_selection"]["declaration"] == (
        "Erdos249257.ExternalVerification.irrational_erdosSum_full_support"
    )
    assert showcase["candidate_selection"]["family_id"] == "known_irrational_supports"
    assert showcase["candidate_selection"]["exact_hypotheses"] == ["2 <= b"]
    assert showcase["candidate_selection"]["open_boundary"]
    assert showcase["candidate_selection"]["limitations"]
    assert showcase["candidate_universe"]["declarations"] == comparator["theorem_names"]
    assert set(showcase["candidate_universe"]["declarations"]) == set(names)
    universe = showcase["candidate_universe"]
    assert universe["authority"] == (
        "HEAD:docs/claims.json::external_verification_packet.review_matrix"
    )
    assert universe["source_review_family_count"] == 62
    assert universe["source_review_family_count_at_dispatch"] == 60
    assert len(universe["source_review_family_ids"]) == 62
    assert set(universe["source_family_dispositions"]) == set(
        universe["source_review_family_ids"]
    )
    source_contract = universe["source_family_disposition_contract"]
    assert set(source_contract["required_fields"]) == {
        "disposition",
        "support_evidence",
        "contrary_evidence",
        "cheapest_probe",
        "stop_evidence",
        "hard_mechanism",
        "attribution",
        "limitations",
        "open_boundary",
    }
    assert universe["comparator_screen"]["partition"] == (
        "candidate_value_dispositions.eligible_groups"
    )
    assert set(row["candidate_id"] for row in universe["targeted_theorem_forest_discoveries"]) == {
        "first_harmonic_pivot",
        "actual_lcm_positive_corridor_top_edge",
        "certificate_completeness",
        "erdos1049_four_jet_pade_obstruction",
        "erdos251_integral_tail_classification",
        "weighted_phase_carry_observer",
    }
    assert [row["rank"] for row in showcase["candidate_ranking"]] == list(
        range(1, len(showcase["candidate_ranking"]) + 1)
    )
    ranked = {row["declaration"] for row in showcase["candidate_ranking"]}
    screened = {row["declaration"] for row in showcase["candidate_screening"]}
    assert ranked.isdisjoint(screened)
    assert ranked | screened == set(comparator["theorem_names"])
    assert showcase["candidate_ranking"][0]["declaration"] == showcase["candidate_selection"]["declaration"]
    assert {
        row["axis"] for row in showcase["selection_contract"]["ranking_axes"]
    } == checker.SELECTION_AXES
    disposition = showcase["candidate_value_dispositions"]
    groups = disposition["eligible_groups"]
    grouped_names = [name for group in groups for name in group["declarations"]]
    assert len(grouped_names) == len(set(grouped_names)) == len(comparator["theorem_names"])
    assert set(grouped_names) == set(comparator["theorem_names"])
    assert {group["disposition"] for group in groups} == {
        "selected",
        "represented",
        "subordinate",
        "rejected",
        "long_tail",
    }
    landscape = disposition["source_landscape_candidates"]
    assert len(landscape) == 7
    landscape_by_id = {row["candidate_id"]: row for row in landscape}
    assert landscape_by_id["actual_lcm_orbit_separation"]["disposition"] == "represented"
    assert landscape_by_id["actual_lcm_orbit_separation"]["prior_disposition"] == "deferred"
    assert landscape_by_id["actual_lcm_orbit_separation"]["comparator_eligibility"] == (
        "committed_source_faithful_transport"
    )
    assert landscape_by_id["actual_lcm_orbit_separation"]["comparator_declaration"] in comparator["theorem_names"]
    hypotheses = " ".join(landscape_by_id["actual_lcm_orbit_separation"]["exact_hypotheses"])
    assert "oddGuardedCanonicalAdjacentSuffixDepth" in hypotheses
    assert "actualLcmRawErrorRadius" in hypotheses
    assert "actualLcmTailOrbit" in hypotheses
    assert "Irrational" in landscape_by_id["actual_lcm_orbit_separation"]["conclusion"]
    for candidate_id in (
        "first_harmonic_pivot",
        "actual_lcm_positive_corridor_top_edge",
        "certificate_completeness",
        "erdos1049_four_jet_pade_obstruction",
        "erdos251_integral_tail_classification",
        "weighted_phase_carry_observer",
    ):
        row = landscape_by_id[candidate_id]
        assert row["disposition"] in {"deferred", "subordinate"}
        assert row["comparator_eligibility"] == (
            "source_landed_but_not_comparator_configured"
        )
        assert row["queue_role"] == "source_landscape_review_not_comparator_evidence"
        assert "comparator_declaration" not in row
    weighted = landscape_by_id["weighted_phase_carry_observer"]
    assert "carry_eq_residueDigit_add_coboundary" in weighted["source_declaration"]
    assert "carryResidue_mem_interval" in weighted["source_declaration"]
    assert "residueDigit_mem_interval" in weighted["source_declaration"]
    assert "finite_realisedSpan_of_factorisation" in weighted["source_declaration"]
    assert "uncontrolled integral coboundary" in weighted["conclusion"]
    assert any("scalar-evaluation" in item for item in weighted["limitations"])


def test_adversarial_candidate_universe_drop_is_not_silently_accepted() -> None:
    showcase = json.loads((ROOT / "docs/PALOMAR_RESULT_SHOWCASE.json").read_text())
    comparator = json.loads(
        subprocess.check_output(["git", "show", "HEAD:verification/comparator.json"], cwd=ROOT)
    )
    damaged = copy.deepcopy(showcase)
    damaged["candidate_universe"]["declarations"].pop()
    errors = checker.candidate_selection_errors(comparator, damaged)
    assert errors
    assert any(
        "nested Comparator screen roster" in error
        or "candidate universe" in error
        for error in errors
    )


def test_adversarial_selection_semantics_drop_is_not_silently_accepted() -> None:
    showcase = json.loads((ROOT / "docs/PALOMAR_RESULT_SHOWCASE.json").read_text())
    comparator = json.loads(
        subprocess.check_output(["git", "show", "HEAD:verification/comparator.json"], cwd=ROOT)
    )
    damaged = copy.deepcopy(showcase)
    damaged["candidate_selection"].pop("open_boundary")
    errors = checker.candidate_selection_errors(comparator, damaged)
    assert errors
    assert any("open_boundary" in error for error in errors)

    damaged = copy.deepcopy(showcase)
    damaged["selection_comparison"][0].pop("reason")
    errors = checker.candidate_selection_errors(comparator, damaged)
    assert errors
    assert any("selection comparison" in error for error in errors)

    damaged = copy.deepcopy(showcase)
    damaged["candidate_screening"].pop()
    errors = checker.candidate_selection_errors(comparator, damaged)
    assert errors
    assert any("partition Comparator" in error for error in errors)


def test_adversarial_value_disposition_drift_is_not_silently_accepted() -> None:
    showcase = json.loads((ROOT / "docs/PALOMAR_RESULT_SHOWCASE.json").read_text())
    comparator = json.loads(
        subprocess.check_output(["git", "show", "HEAD:verification/comparator.json"], cwd=ROOT)
    )
    damaged = copy.deepcopy(showcase)
    damaged["candidate_value_dispositions"]["eligible_groups"][2]["declarations"] = []
    errors = checker.candidate_selection_errors(comparator, damaged)
    assert any("candidate value-disposition" in error for error in errors)

    damaged = copy.deepcopy(showcase)
    damaged["candidate_value_dispositions"]["source_landscape_candidates"][0][
        "comparator_declaration"
    ] = "Erdos249257.ExternalVerification.not_a_committed_row"
    errors = checker.candidate_selection_errors(comparator, damaged)
    assert any("non-Comparator declaration" in error for error in errors)

    damaged = copy.deepcopy(showcase)
    deferred = next(
        row
        for row in damaged["candidate_value_dispositions"]["source_landscape_candidates"]
        if row["candidate_id"] == "first_harmonic_pivot"
    )
    deferred["comparator_declaration"] = comparator["theorem_names"][0]
    errors = checker.candidate_selection_errors(comparator, damaged)
    assert any("must not name Comparator evidence" in error for error in errors)

    damaged = copy.deepcopy(showcase)
    damaged["candidate_universe"]["authority"] = "HEAD:verification/comparator.json"
    errors = checker.candidate_selection_errors(comparator, damaged)
    assert any("claims review matrix" in error for error in errors)


def test_adversarial_source_declaration_drift_is_not_silently_accepted() -> None:
    showcase = json.loads((ROOT / "docs/PALOMAR_RESULT_SHOWCASE.json").read_text())
    damaged = copy.deepcopy(showcase)
    damaged["candidate_selection"]["source_declaration"] = (
        "Erdos249257.not_the_selected_source_theorem"
    )
    reconciliation = json.loads(
        (ROOT / "docs/PALOMAR_POLICY_RECONCILIATION.json").read_text()
    )
    errors, _ = checker.static_requirement_errors(ROOT, reconciliation, damaged)
    assert any("source_declaration" in error for error in errors)


def test_adversarial_roster_drop_is_not_silently_accepted() -> None:
    showcase = json.loads((ROOT / "docs/PALOMAR_RESULT_SHOWCASE.json").read_text())
    comparator = json.loads(
        subprocess.check_output(["git", "show", "HEAD:verification/comparator.json"], cwd=ROOT)
    )
    reconciliation = json.loads((ROOT / "docs/PALOMAR_POLICY_RECONCILIATION.json").read_text())
    damaged = copy.deepcopy(showcase)
    damaged["frontier_by_problem"][0]["comparator_declarations"].pop()
    source = CHECKER.read_text()
    namespace: dict = {}
    exec(compile(source, str(CHECKER), "exec"), namespace)
    errors = namespace["roster_errors"](ROOT, comparator, damaged, reconciliation)
    assert errors
    assert any("crosswalk" in error for error in errors)


if __name__ == "__main__":
    test_safe_input_boundary()
    test_normal_and_optimised_checker_agree()
    test_generated_formalization_reads_committed_head_only()
    test_structural_qualification_ignores_mutable_source_reads()
    test_full_current_roster_and_eight_problem_crosswalk()
    test_adversarial_candidate_universe_drop_is_not_silently_accepted()
    test_adversarial_selection_semantics_drop_is_not_silently_accepted()
    test_adversarial_value_disposition_drift_is_not_silently_accepted()
    test_adversarial_roster_drop_is_not_silently_accepted()
    print("palomar qualification tests: ok")
