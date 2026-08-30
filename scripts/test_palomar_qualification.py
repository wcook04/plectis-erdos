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
  authors:
    - \"Will Cook\"
  license: \"Apache-2.0\"
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
    assert set(names) == set(comparator["theorem_names"])
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
    assert universe["source_review_family_count"] == len(
        universe["source_review_family_ids"]
    )
    assert universe["source_review_family_count"] > universe[
        "source_review_family_count_at_dispatch"
    ]
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
        "erdos243_centered_state_recovery",
        "weighted_phase_carry_observer",
        "erdos249_carry_anti_compression",
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
    assert landscape
    assert len({row["candidate_id"] for row in landscape}) == len(landscape)
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
    for candidate_id in ("certificate_completeness",):
        row = landscape_by_id[candidate_id]
        assert row["disposition"] in {"deferred", "subordinate"}
        assert row["comparator_eligibility"] == (
            "source_landed_but_not_comparator_configured"
        )
        assert row["queue_role"] == "source_landscape_review_not_comparator_evidence"
        assert "comparator_declaration" not in row
    pade = landscape_by_id["erdos1049_four_jet_pade_obstruction"]
    assert pade["family_id"] == "height_and_pade_arithmetic"
    assert pade["disposition"] == "represented"
    assert pade["prior_disposition"] == "deferred"
    assert pade["canonical_family_binding"] == "height_and_pade_arithmetic"
    assert pade["comparator_eligibility"] == "committed_source_faithful_transport"
    assert pade["queue_role"] == "source_landscape_review_with_committed_comparator_evidence"
    assert pade["comparator_declaration"] == (
        "Erdos249257.ExternalVerification.rectangular_hp_threshold_eq_classical_iff"
    )
    assert pade["comparator_declaration"] in comparator["theorem_names"]
    assert pade["source_transport_commit"] == "f52f903a6f5b564644b19b89b66d65f97990c5b6"
    assert pade["source_transport_files"] == [
        "ExternalVerification/Challenge.lean",
        "ExternalVerification/Solution.lean",
        "ExternalVerification/Statements.lean",
    ]
    assert pade["transport_declarations"] == [
        "Erdos249257.ExternalVerification.hpClearedGap_nonpos",
        "Erdos249257.ExternalVerification.hpClearedGap_eq_zero_iff",
        "Erdos249257.ExternalVerification.rectangular_hp_threshold_le_classical",
        "Erdos249257.ExternalVerification.rectangular_hp_threshold_eq_classical_iff",
    ]
    assert "HermitePadeNoGo.lean" in pade["source_file"]
    assert "rectangular two-function exponent model" in pade["statement"]
    assert any("universal Padé" in item for item in pade["limitations"])
    centered = landscape_by_id["erdos243_centered_state_recovery"]
    assert centered["family_id"] == "centered_state_dynamics"
    assert centered["disposition"] == "represented"
    assert centered["prior_disposition"] == "deferred"
    assert centered["canonical_family_binding"] == "centered_state_dynamics"
    assert centered["comparator_eligibility"] == "committed_source_faithful_transport"
    assert centered["source_transport_commit"] == "ea12f041307bfea8ca423d8f76f6fe2d38c35055"
    assert centered["source_transport_files"] == [
        "ExternalVerification/Challenge.lean",
        "ExternalVerification/Solution.lean",
        "ExternalVerification/Statements.lean",
    ]
    assert centered["transport_declarations"] == [
        "Erdos249257.ExternalVerification.sylvesterNext_eventually_of_centered_zero",
        "Erdos249257.ExternalVerification.centeredState_eventually_zero",
        "Erdos249257.ExternalVerification.boundedNegativePart_eventually_zero",
    ]
    assert centered["comparator_declaration"] == (
        "Erdos249257.ExternalVerification.boundedNegativePart_eventually_zero"
    )
    assert centered["supporting_comparator_declarations"] == []
    assert centered["subordinate_source_declarations"] == [
        "Erdos249257.ExternalVerification.centeredState_eventually_zero",
        "Erdos249257.ExternalVerification.sylvesterNext_eventually_of_centered_zero",
    ]
    assert centered["canonical_claim_commit"] == (
        "717ba73e587ee0be9ae388d352f24ad9f22cb55d"
    )
    assert "boundedNegativePart_eventually_zero" in centered["source_declaration"]
    assert "mixed-sign branch" in " ".join(centered["limitations"])
    committed = {
        row["candidate_id"]: row
        for row in landscape
        if row["comparator_eligibility"]
        == "committed_source_faithful_transport"
    }
    assert set(committed) == {
        "actual_lcm_orbit_separation",
        "first_harmonic_pivot",
        "actual_lcm_positive_corridor_top_edge",
        "erdos251_integral_tail_classification",
        "erdos1049_four_jet_pade_obstruction",
        "erdos257_boolean_mobius_carry",
        "erdos249_carry_anti_compression",
        "erdos243_centered_state_recovery",
        "weighted_phase_carry_observer",
    }
    assert committed["first_harmonic_pivot"]["family_id"] == "first_harmonic_pivot_decomposition"
    assert committed["actual_lcm_positive_corridor_top_edge"]["family_id"] == "actual_lcm_orbit_separation"
    assert committed["first_harmonic_pivot"]["comparator_declaration"] in comparator["theorem_names"]
    assert committed["actual_lcm_positive_corridor_top_edge"]["comparator_declaration"] in comparator["theorem_names"]
    assert set(committed["first_harmonic_pivot"]["supporting_comparator_declarations"]) <= set(comparator["theorem_names"])
    assert set(committed["actual_lcm_positive_corridor_top_edge"]["supporting_comparator_declarations"]) <= set(comparator["theorem_names"])
    for row in (
        committed["first_harmonic_pivot"],
        committed["actual_lcm_positive_corridor_top_edge"],
    ):
        assert row["source_transport_commit"] == "bc0fee48e14719391a77e90ea98205400b98993b"
        assert row["source_transport_files"] == [
            "ExternalVerification/Challenge.lean",
            "ExternalVerification/Solution.lean",
            "ExternalVerification/Statements.lean",
        ]
        assert row["transport_declarations"]
        assert "verification/comparator.json" in row["transport_admission_boundary"]
        assert "review matrix" in row["transport_admission_boundary"]
    pending = {
        row["candidate_id"]: row
        for row in landscape
        if row["comparator_eligibility"]
        == "committed_source_transport_pending_comparator_registration"
    }
    assert set(pending) == set()
    row = landscape_by_id["erdos251_integral_tail_classification"]
    assert row["family_id"] == "dyadic_tail_integrality_classification"
    assert row["disposition"] == "represented"
    assert row["prior_disposition"] == "deferred"
    assert row["comparator_eligibility"] == "committed_source_faithful_transport"
    assert row["queue_role"] == "source_landscape_review_with_committed_comparator_evidence"
    assert row["comparator_declaration"] == (
        "Erdos249257.ExternalVerification.irrational_initial_iff_all_positive_tailShifts_nonintegral"
    )
    assert row["comparator_declaration"] in comparator["theorem_names"]
    assert row["source_transport_commit"] == "e10b161abd964381e0e8e6830e6f48e7629ca8ad"
    assert row["source_transport_files"] == [
        "ExternalVerification/Challenge.lean",
        "ExternalVerification/Solution.lean",
        "ExternalVerification/Statements.lean",
    ]
    assert row["transport_declarations"] == [
        "Erdos249257.ExternalVerification.tailShift_integral_iff_den_dvd_mersenne",
        "Erdos249257.ExternalVerification.tailShift_integral_iff_two_pow_modEq_one",
        "Erdos249257.ExternalVerification.not_irrational_initial_iff_exists_eventually_integral_positive_tailShift",
        "Erdos249257.ExternalVerification.irrational_initial_iff_all_positive_tailShifts_nonintegral",
    ]
    assert "verification/comparator.json" in row["transport_admission_boundary"]
    assert "review matrix" in row["transport_admission_boundary"]
    assert "prime-tail cofinal mismatch" in row["limitations"][0]
    assert "verification/comparator.json" in row["transport_admission_boundary"]
    assert "review matrix" in row["transport_admission_boundary"]
    weighted = landscape_by_id["weighted_phase_carry_observer"]
    assert "carry_eq_residueDigit_add_coboundary" in weighted["source_declaration"]
    assert "carryResidue_mem_interval" in weighted["source_declaration"]
    assert "residueDigit_mem_interval" in weighted["source_declaration"]
    assert "finite_realisedSpan_of_factorisation" in weighted["source_declaration"]
    assert "uncontrolled integral coboundary" in weighted["conclusion"]
    assert any("scalar-evaluation" in item for item in weighted["limitations"])
    assert weighted["disposition"] == "represented"
    assert weighted["comparator_eligibility"] == "committed_source_faithful_transport"
    assert weighted["queue_role"] == "source_landscape_review_with_committed_comparator_evidence"
    assert weighted["comparator_declaration"] == (
        "Erdos249257.ExternalVerification.carry_eq_residueDigit_add_coboundary"
    )
    assert weighted["comparator_declaration"] in comparator["theorem_names"]
    assert weighted["supporting_comparator_declarations"] == []
    assert weighted["source_transport_commit"] == (
        "cec8ee43219b3f2059902be78ee0fc54df3dd6e9"
    )
    assert weighted["canonical_claim_commit"] == (
        "97d96fb5307061dfe79035c19212572c07cc9055"
    )
    boolean = landscape_by_id["erdos257_boolean_mobius_carry"]
    assert boolean["family_id"] == "boolean_mobius_carry"
    assert boolean["disposition"] == "represented"
    assert boolean["prior_disposition"] == "deferred"
    assert boolean["comparator_eligibility"] == "committed_source_faithful_transport"
    assert boolean["queue_role"] == "source_landscape_review_with_committed_comparator_evidence"
    assert boolean["comparator_declaration"] == (
        "Erdos249257.ExternalVerification.exists_normalized_support_fraction_iff_exists_booleanMobiusCarry"
    )
    assert boolean["comparator_declaration"] in comparator["theorem_names"]
    assert boolean["supporting_comparator_declarations"] == []
    assert "exists_normalized_support_fraction_iff_exists_booleanMobiusCarry" in boolean["source_declaration"]
    assert boolean["source_transport_commit"] == "712bc4c3928fef394a6fe96142e593ddc95c1ded"
    assert boolean["transport_declarations"] == [
        "Erdos249257.ExternalVerification.exists_normalized_support_fraction_iff_exists_booleanMobiusCarry",
        "Erdos249257.ExternalVerification.BooleanMobiusCarryCertificate",
        "Erdos249257.ExternalVerification.binaryCoeffSeries_rational_iff_exists_temperedBinaryOrbit",
        "Erdos249257.ExternalVerification.one_div_oddOrder_le_reciprocalMass_of_support_fraction",
        "Erdos249257.ExternalVerification.exists_unbounded_shifted_odd_tail_nat_state_of_support_fraction",
        "Erdos249257.ExternalVerification.supportCoeffZeroWindow_length_le_eps_logb_add",
    ]
    assert "no universal Erdős #257 irrationality" in " ".join(boolean["limitations"])
    anti = landscape_by_id["erdos249_carry_anti_compression"]
    assert anti["family_id"] == "totient_carry_anti_compression"
    assert anti["disposition"] == "represented"
    assert anti["comparator_eligibility"] == "committed_source_faithful_transport"
    assert anti["queue_role"] == "source_landscape_review_with_committed_comparator_evidence"
    assert anti["comparator_declaration"] == (
        "Erdos249257.ExternalVerification.not_irrational_totientSeries_implies_mod_period_and_unbounded_rank"
    )
    assert anti["comparator_declaration"] in comparator["theorem_names"]
    assert anti["supporting_comparator_declarations"] == []
    assert anti["source_transport_commit"] == "4932144ada05d6c617f43a372ede18a56900df7b"
    assert anti["transport_declarations"] == [
        "Erdos249257.ExternalVerification.not_irrational_totientSeries_implies_mod_period_and_unbounded_rank"
    ]
    assert "finite-Q-rank upper bound" in " ".join(anti["limitations"])
    assert "Canonical source-landscape family" in anti["ranking_status"]


def test_adversarial_source_transport_family_merge_is_not_silently_accepted() -> None:
    showcase = json.loads((ROOT / "docs/PALOMAR_RESULT_SHOWCASE.json").read_text())
    comparator = json.loads(
        subprocess.check_output(["git", "show", "HEAD:verification/comparator.json"], cwd=ROOT)
    )
    damaged = copy.deepcopy(showcase)
    damaged_row = next(
        row
        for row in damaged["candidate_value_dispositions"]["source_landscape_candidates"]
        if row["candidate_id"] == "actual_lcm_positive_corridor_top_edge"
    )
    damaged_row["family_id"] = "actual_lcm_positive_corridor_top_edge"
    errors = checker.candidate_selection_errors(comparator, damaged, ROOT)
    assert any("merges or misnames" in error for error in errors)


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
    source_only = next(
        row
        for row in damaged["candidate_value_dispositions"]["source_landscape_candidates"]
        if row["candidate_id"] == "certificate_completeness"
    )
    source_only["comparator_declaration"] = comparator["theorem_names"][0]
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
