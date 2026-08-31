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
    assert normal["decision"] == "READY"
    assert normal["structural_deficits"] == []
    assert "operator_only_gates" not in normal
    assert "withheld_terminal_gates" not in normal
    assert normal["external_follow_on"]["performed"] == []
    assert "publication" in normal["external_follow_on"]["not_local_readiness_criteria"]


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

    damaged = copy.deepcopy(reconciliation)
    damaged["official_authorities"] = [
        row
        for row in damaged["official_authorities"]
        if row["path"] != "schema/formalization.schema.json"
    ]
    errors = checker.authority_errors(damaged)
    assert any("schema/formalization.schema.json" in error for error in errors)


def test_repository_intake_contract() -> None:
    facts = checker.repository_intake_evidence(ROOT)
    assert checker.repository_intake_errors(facts) == []
    assert facts["repository_size_bytes"] < facts["repository_size_limit_bytes"]
    assert facts["git_submodules"] == []
    assert facts["git_lfs_pointers"] == []
    assert facts["compiled_artifacts"] == []
    assert facts["challenge_path"] == "ExternalVerification/Challenge.lean"
    committed_challenge = checker.committed_bytes(ROOT, facts["challenge_path"])
    assert facts["challenge_bytes"] == len(committed_challenge)
    assert facts["challenge_lines"] == len(committed_challenge.splitlines())
    assert facts["challenge_bytes"] < facts["challenge_size_limit_bytes"]
    assert facts["challenge_lines"] < facts["challenge_line_limit"]
    assert facts["warnings"] == [
        "Challenge exceeds Palomar's 32 KiB or 300-line auditability warning threshold"
    ]
    assert facts["formalization_bytes"] < facts["formalization_size_limit_bytes"]
    assert facts["formalization_utf8"] is True
    assert facts["license_paths"] == ["LICENSE"]
    assert facts["license_regular"] is True
    assert facts["license_utf8"] is True
    assert 0 < facts["license_bytes"] < facts["license_size_limit_bytes"]
    assert facts["git_dependency_count"] == 9
    assert facts["invalid_git_dependencies"] == []

    damaged = copy.deepcopy(facts)
    damaged["repository_size_bytes"] = damaged["repository_size_limit_bytes"] + 1
    assert any("500 MiB" in error for error in checker.repository_intake_errors(damaged))

    damaged = copy.deepcopy(facts)
    damaged["git_submodules"] = ["vendor/example"]
    assert any("submodules" in error for error in checker.repository_intake_errors(damaged))

    damaged = copy.deepcopy(facts)
    damaged["challenge_lines"] = damaged["challenge_line_limit"] + 1
    assert any("1,000-line" in error for error in checker.repository_intake_errors(damaged))

    reconciliation = json.loads(
        (ROOT / "docs/PALOMAR_POLICY_RECONCILIATION.json").read_text()
    )
    damaged_reconciliation = copy.deepcopy(reconciliation)
    damaged_reconciliation["requirements"] = [
        row
        for row in damaged_reconciliation["requirements"]
        if row["id"] != "repository_source_envelope"
    ]
    assert any(
        "repository_source_envelope" in error
        for error in checker.authority_errors(damaged_reconciliation)
    )


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
        "strict_prime_tail_orbit_gap",
        "erdos249_carry_anti_compression",
        "erdos68_channel_projection_rigidity",
        "erdos1041_ray_separation",
        "erdos243_bounded_rise_coprimality",
        "erdos1041_newton_value_decay",
    }
    assert [row["rank"] for row in showcase["candidate_ranking"]] == list(
        range(1, len(showcase["candidate_ranking"]) + 1)
    )
    ranked = {row["declaration"] for row in showcase["candidate_ranking"]}
    screened = {row["declaration"] for row in showcase["candidate_screening"]}
    assert ranked.isdisjoint(screened)
    assert ranked | screened == set(comparator["theorem_names"])
    ranked_by_declaration = {
        row["declaration"]: row for row in showcase["candidate_ranking"]
    }
    assert ranked_by_declaration[
        "Erdos249257.ExternalVerification.irrational_factorialGapSeries_iff_cofinal_nonunit_carries"
    ]["family_id"] == "factorial_carry_characterisation"
    assert ranked_by_declaration[
        "Erdos249257.ExternalVerification.irrational_tsum_primeDyadicTerm_iff_primeGap"
    ]["family_id"] == "prime_gap_reformulation"
    assert ranked_by_declaration[
        "Erdos249257.ExternalVerification.sylvesterNext_eventually_of_summable_negativeRelativeMass"
    ]["rank"] == 12
    assert (
        "Erdos249257.ExternalVerification.sylvesterNext_eventually_of_summable_negativeRelativeMass"
        not in screened
    )
    assert all(
        row["family_id"] in universe["source_review_family_ids"]
        for row in showcase["candidate_ranking"]
    )
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
    factorial_channel = landscape_by_id["erdos68_channel_projection_rigidity"]
    assert factorial_channel["family_id"] == "factorial_channel_and_projection_rigidity"
    assert factorial_channel["disposition"] == "represented"
    assert factorial_channel["comparator_eligibility"] == (
        "source_landed_but_not_comparator_configured"
    )
    assert factorial_channel["queue_role"] == "source_landscape_review_not_comparator_evidence"
    assert factorial_channel["canonical_claim_commit"] == (
        "06198c0ab3969c625e1022eaebfb46208ff0b5e4"
    )
    for declaration in (
        "factorialMoment_eq_factorial_pow_mul_channelNumerator_band",
        "exists_index_ge_two_mul_of_factorialMoment_ne_zero_of_channel_eq_zero",
        "channelNumerator_mod_factorialMoment",
        "primeTranslator_channelResidual_eq_one",
        "projection_disagreement_excludes_bounded_endpoint",
    ):
        assert declaration in factorial_channel["source_declaration"]
    assert "factorial_carry_characterisation" in factorial_channel["ranked_below"]
    assert "factorial_finite_certificates" in factorial_channel["ranked_above"]
    assert "cofinal" in " ".join(factorial_channel["limitations"]).lower()
    ray_separation = landscape_by_id["erdos1041_ray_separation"]
    assert ray_separation["family_id"] == "ray_separation"
    assert ray_separation["disposition"] == "represented"
    assert ray_separation["comparator_eligibility"] == (
        "source_landed_but_not_comparator_configured"
    )
    assert ray_separation["queue_role"] == "source_landscape_review_not_comparator_evidence"
    assert ray_separation["canonical_claim_commit"] == (
        "06198c0ab3969c625e1022eaebfb46208ff0b5e4"
    )
    assert "samePositiveRay_of_real_exp_decay" in ray_separation["source_declaration"]
    assert "no_newtonConnection_of_not_samePositiveRay" in ray_separation[
        "source_declaration"
    ]
    assert "newton_value_decay" in ray_separation["ranked_below"]
    assert "lemniscate_finite_search" in ray_separation["ranked_above"]
    assert "global" in " ".join(ray_separation["limitations"]).lower()
    bounded_rise = landscape_by_id["erdos243_bounded_rise_coprimality"]
    assert bounded_rise["family_id"] == "bounded_rise_coprimality"
    assert bounded_rise["disposition"] == "represented"
    assert bounded_rise["comparator_eligibility"] == (
        "source_landed_but_not_comparator_configured"
    )
    assert bounded_rise["canonical_claim_commit"] == (
        "06198c0ab3969c625e1022eaebfb46208ff0b5e4"
    )
    assert "reducedTail_pairwiseCoprime" in bounded_rise["source_declaration"]
    assert "no_eventuallyBoundedRise_reducedTail" in bounded_rise[
        "source_declaration"
    ]
    assert "centered_state_dynamics" in bounded_rise["ranked_below"]
    assert "negative_mass_recovery" in bounded_rise["ranked_below"]
    assert "rise bound" in " ".join(bounded_rise["limitations"]).lower()
    value_decay = landscape_by_id["erdos1041_newton_value_decay"]
    assert value_decay["family_id"] == "newton_value_decay"
    assert value_decay["disposition"] == "represented"
    assert value_decay["comparator_eligibility"] == (
        "source_landed_but_not_comparator_configured"
    )
    assert value_decay["canonical_claim_commit"] == (
        "06198c0ab3969c625e1022eaebfb46208ff0b5e4"
    )
    assert "newtonFlow_value_hasDerivAt" in value_decay["source_declaration"]
    assert "newtonFlow_scaledValue_hasDerivAt_zero" in value_decay[
        "source_declaration"
    ]
    assert "ray_separation" in value_decay["ranked_above"]
    assert "translation_avoidance" in value_decay["ranked_above"]
    assert "root_retention" in value_decay["ranked_above"]
    assert "topology" in " ".join(value_decay["limitations"]).lower()
    assert landscape_by_id["actual_lcm_orbit_separation"]["disposition"] == "represented"
    assert landscape_by_id["actual_lcm_orbit_separation"]["prior_disposition"] == "deferred"
    negative_mass = landscape_by_id["erdos243_negative_mass_recovery"]
    assert "rank 12" in negative_mass["source_landscape_rank_relative_to"].lower()
    assert "centered_state_dynamics" in negative_mass["ranked_below"]
    assert "weighted_phase_carry_observer" in negative_mass["ranked_above"]
    strict_prime = landscape_by_id["strict_prime_tail_orbit_gap"]
    assert strict_prime["canonical_claim_commit"] == "ddbe2870877d0b3abcb7d7e3e9b00d00eb91f021"
    assert strict_prime["source_anchor"].endswith("349; 367; 389; 414; 445; 471")
    for declaration in (
        "tailOrbitFirstExp_zero_eq_scaled_angle",
        "tailOrbitFirstExp_eq_one_iff_tail_diff_mem_int",
        "exists_tailOrbitFirstExp_zero_pow_two_eq_one_iff_dyadic",
        "tailOrbitFirstExp_zero_pow_two_ne_one_upto_sixteen",
        "cofinally_tailOrbitFirstExp_re_nonpos_of_not_dyadic",
        "naturalPrimeTailOrbitStrictGap_of_cofinal_nonpositive_prime_shift",
    ):
        assert declaration in strict_prime["source_declaration"]
    strict_rank = next(
        row for row in showcase["candidate_ranking"]
        if row["family_id"] == "strict_prime_tail_orbit_gap"
    )
    assert "Claims ddbe2870" in strict_rank["evidence_certainty"]
    assert "cofinal nonpositive-prime-shift" in strict_rank["overclaim_risk"]
    small_mismatch = landscape_by_id["erdos251_small_mismatch_criterion"]
    assert "conditional-endpoint leverage" in small_mismatch["source_landscape_rank_relative_to"].lower()
    assert "prime_gap_reformulation" in small_mismatch["ranked_below"]
    assert "dyadic_tail_integrality_classification" in small_mismatch["ranked_above"]
    assert landscape_by_id["actual_lcm_orbit_separation"]["comparator_eligibility"] == (
        "committed_source_faithful_transport"
    )
    assert landscape_by_id["actual_lcm_orbit_separation"]["comparator_declaration"] in comparator["theorem_names"]
    hypotheses = " ".join(landscape_by_id["actual_lcm_orbit_separation"]["exact_hypotheses"])
    assert "oddGuardedCanonicalAdjacentSuffixDepth" in hypotheses
    assert "actualLcmRawErrorRadius" in hypotheses
    assert "actualLcmTailOrbit" in hypotheses
    assert "Irrational" in landscape_by_id["actual_lcm_orbit_separation"]["conclusion"]
    foreign = landscape_by_id["actual_foreign_residue_projection"]
    assert foreign["family_id"] == "actual_foreign_residue_projection"
    assert foreign["disposition"] == "represented"
    assert foreign["prior_disposition"] == "deferred"
    assert foreign["comparator_eligibility"] == "committed_source_faithful_transport"
    assert foreign["queue_role"] == "source_landscape_review_with_committed_comparator_evidence"
    assert foreign["comparator_declaration"] == (
        "Erdos249257.ExternalVerification.scaleFullTarget_miss_of_projected_separation"
    )
    assert foreign["comparator_declaration"] in comparator["theorem_names"]
    assert foreign["source_transport_commit"] == "8a08768f3758f11e9640535523232b0300316a4b"
    assert "ControlledForeignProjection" in " ".join(foreign["exact_hypotheses"])
    assert "unbounded" in " ".join(foreign["limitations"])
    assert "not an irrationality theorem" in foreign["conclusion"]
    foreign_screen = next(
        row
        for row in showcase["candidate_screening"]
        if row["declaration"] == foreign["comparator_declaration"]
    )
    assert foreign_screen["family_id"] == "actual_foreign_residue_projection"
    assert foreign_screen["disposition"] == "supporting_conditional_reduction"
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
    small_mismatch = landscape_by_id["erdos251_small_mismatch_criterion"]
    assert small_mismatch["family_id"] == "small_mismatch_criterion"
    assert small_mismatch["disposition"] == "represented"
    assert small_mismatch["prior_disposition"] == "deferred"
    assert small_mismatch["canonical_family_binding"] == "small_mismatch_criterion"
    assert small_mismatch["canonical_claim_commit"] == (
        "96b2dc35cb1a73ad63ce4e01565aeb88cd477c12"
    )
    assert small_mismatch["comparator_eligibility"] == "committed_source_faithful_transport"
    assert small_mismatch["queue_role"] == "source_landscape_review_with_committed_comparator_evidence"
    assert small_mismatch["comparator_declaration"] == (
        "Erdos249257.ExternalVerification.primeGapTailShift_not_eventuallyIntegral_of_cofinal_small_mismatch"
    )
    assert small_mismatch["comparator_declaration"] in comparator["theorem_names"]
    assert small_mismatch["source_transport_commit"] == (
        "750e4d3218248bea5785b16e6f271bb3ab76ff7e"
    )
    assert "cofinal" in " ".join(small_mismatch["exact_hypotheses"]).lower()
    assert "No theorem supplies cofinally many adjacent small mismatches" in " ".join(
        small_mismatch["limitations"]
    )
    assert "not a #251 irrationality" in small_mismatch["conclusion"]
    carry_escape = landscape_by_id["erdos269_conditional_carry_escape"]
    assert carry_escape["family_id"] == "conditional_carry_escape"
    assert carry_escape["disposition"] == "subordinate"
    assert carry_escape["prior_disposition"] == "deferred"
    assert carry_escape["comparator_eligibility"] == "committed_source_faithful_transport"
    assert carry_escape["queue_role"] == "source_landscape_review_with_committed_comparator_evidence"
    assert carry_escape["comparator_declaration"] == (
        "Erdos249257.ExternalVerification.no_positive_reducedCarry_of_cofinalLocalWindowEscape"
    )
    assert carry_escape["canonical_claim_commit"] == (
        "68b4b2bfa2ebdfff7dd31a355b04e5e41df99a69"
    )
    assert "no_positive_absorbedCarry_of_cofinalLocalWindowEscape" in carry_escape[
        "source_declaration"
    ]
    assert carry_escape["source_anchor"] == "629-650; 689"
    assert "smoothFactor" in " ".join(carry_escape["exact_hypotheses"])
    assert "cancellation" in carry_escape["hard_mechanism"]
    assert carry_escape["comparator_declaration"] in comparator["theorem_names"]
    assert carry_escape["source_transport_commit"] == (
        "069245dfa77c55565611f04f9269707e0c31ce24"
    )
    assert "CofinalLocalWindowEscape" in " ".join(carry_escape["exact_hypotheses"])
    assert "rationality-to-carry" in " ".join(carry_escape["limitations"])
    assert "not an Erdős #269 endpoint" in carry_escape["conclusion"]
    committed = {
        row["candidate_id"]: row
        for row in landscape
        if row["comparator_eligibility"]
        == "committed_source_faithful_transport"
    }
    assert set(committed) == {
        "actual_lcm_orbit_separation",
        "actual_foreign_residue_projection",
        "first_harmonic_pivot",
        "strict_prime_tail_orbit_gap",
        "erdos269_conditional_carry_escape",
        "erdos251_integral_tail_classification",
        "erdos1049_four_jet_pade_obstruction",
        "erdos257_boolean_mobius_carry",
        "erdos249_carry_anti_compression",
        "erdos249_fixed_precision_transport_no_go",
        "erdos243_centered_state_recovery",
        "erdos243_negative_mass_recovery",
        "weighted_phase_carry_observer",
        "erdos257_boolean_mobius_exact_row_dynamics",
        "erdos257_half_membership_seam_classification",
        "erdos251_coefficient_only_no_go",
        "erdos251_small_mismatch_criterion",
    }
    assert committed["first_harmonic_pivot"]["family_id"] == "first_harmonic_pivot_decomposition"
    assert committed["erdos269_conditional_carry_escape"]["family_id"] == "conditional_carry_escape"
    assert committed["first_harmonic_pivot"]["comparator_declaration"] in comparator["theorem_names"]
    assert committed["erdos269_conditional_carry_escape"]["comparator_declaration"] in comparator["theorem_names"]
    assert set(committed["first_harmonic_pivot"]["supporting_comparator_declarations"]) <= set(comparator["theorem_names"])
    for row in (committed["first_harmonic_pivot"],):
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
    assert set(pending) == {"actual_lcm_positive_corridor_top_edge"}
    assert pending["actual_lcm_positive_corridor_top_edge"]["family_id"] == "actual_lcm_orbit_separation"
    assert "comparator_declaration" not in pending["actual_lcm_positive_corridor_top_edge"]
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
    strict_prime = landscape_by_id["strict_prime_tail_orbit_gap"]
    assert strict_prime["family_id"] == "strict_prime_tail_orbit_gap"
    assert strict_prime["disposition"] == "represented"
    assert strict_prime["comparator_eligibility"] == "committed_source_faithful_transport"
    assert strict_prime["queue_role"] == "source_landscape_review_with_committed_comparator_evidence"
    assert strict_prime["comparator_declaration"] == (
        "Erdos249257.ExternalVerification."
        "irrational_totient_series_of_naturalPrimeTailOrbitStrictGap"
    )
    assert "TotientTailOrbitNonpositiveBlockDensity" in strict_prime["source_declaration"]
    assert "DTWNaturalPrimeTailOrbitStrictGap" in strict_prime["source_declaration"]
    assert "tailOrbitFirstExp_succ" in strict_prime["source_declaration"]
    assert "tailOrbitFirstExp_eq_initial_pow_two" in strict_prime["source_declaration"]
    assert "tailOrbitFirstExp_eq_one_of_le" in strict_prime["source_declaration"]
    assert "not_naturalPrimeTailOrbitStrictGap_of_phase_one" in strict_prime["source_declaration"]
    assert "not_naturalPrimeTailOrbitStrictGap_of_dyadic_root" in strict_prime["source_declaration"]
    assert strict_prime["canonical_claim_commit"] == (
        "ddbe2870877d0b3abcb7d7e3e9b00d00eb91f021"
    )
    assert "repeated-squaring" in " ".join(strict_prime["support_evidence"])
    assert "dyadic root" in " ".join(strict_prime["contrary_evidence"])
    assert "11/100" in " ".join(strict_prime["exact_hypotheses"])
    assert "9/10" in strict_prime["statement"]
    assert "cofinal prime" in " ".join(strict_prime["limitations"])
    assert "no unconditional" in " ".join(strict_prime["limitations"])
    assert "actual_lcm_orbit_separation" in strict_prime[
        "source_landscape_rank_relative_to"
    ]
    assert "totient_certificate_equivalences" in strict_prime[
        "source_landscape_rank_relative_to"
    ]
    assert "nonintegrality" in " ".join(strict_prime["contrary_evidence"])
    qualification_text = (ROOT / "docs" / "PALOMAR_QUALIFICATION.md").read_text(
        encoding="utf-8"
    )
    qualification_text_compact = " ".join(qualification_text.split())
    assert "nine targeted theorem-forest discoveries" in qualification_text_compact
    assert "strict_prime_tail_orbit_gap" in qualification_text_compact
    assert "11/100" in qualification_text_compact
    assert "no unconditional #249 irrationality or endpoint" in qualification_text_compact
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
    exact_row = landscape_by_id["erdos257_boolean_mobius_exact_row_dynamics"]
    assert exact_row["family_id"] == "boolean_mobius_exact_row_dynamics"
    assert exact_row["disposition"] == "represented"
    assert exact_row["prior_disposition"] == "deferred"
    assert exact_row["comparator_eligibility"] == "committed_source_faithful_transport"
    assert exact_row["queue_role"] == "source_landscape_review_with_committed_comparator_evidence"
    assert exact_row["comparator_declaration"] == (
        "Erdos249257.ExternalVerification.half_mem_mersenneAchievementSet_of_positiveHalfGreedySkips"
    )
    assert exact_row["comparator_declaration"] in comparator["theorem_names"]
    assert exact_row["supporting_comparator_declarations"] == []
    assert exact_row["source_transport_commit"] == (
        "0502b7ebe8d3d8a14808eecc5bbc663feef711a3"
    )
    assert exact_row["canonical_claim_commit"] == (
        "33c4c32ea71d67afcd550af8c1fb81b380188f12"
    )
    assert exact_row["source_transport_files"] == [
        "ExternalVerification/Challenge.lean",
        "ExternalVerification/Solution.lean",
        "ExternalVerification/Statements.lean",
    ]
    assert exact_row["transport_declarations"] == [
        "Erdos249257.ExternalVerification.half_mem_mersenneAchievementSet_of_positiveHalfGreedySkips"
    ]
    assert "CofinalPositiveHalfGreedySkips" in exact_row["source_declaration"]
    assert "cofinal" in " ".join(exact_row["exact_hypotheses"]).lower()
    assert "finite exact rows" in " ".join(exact_row["limitations"])
    assert "unconditional" in exact_row["conclusion"]
    assert "verification/comparator.json" in exact_row["transport_admission_boundary"]
    assert "review matrix" in exact_row["transport_admission_boundary"]
    seam = landscape_by_id["erdos257_half_membership_seam_classification"]
    assert seam["family_id"] == "half_membership_seam_classification"
    assert seam["disposition"] == "represented"
    assert seam["prior_disposition"] == "deferred"
    assert seam["canonical_family_binding"] == "half_membership_seam_classification"
    assert seam["comparator_eligibility"] == "committed_source_faithful_transport"
    assert seam["queue_role"] == "source_landscape_review_with_committed_comparator_evidence"
    assert seam["comparator_declaration"] == (
        "Erdos249257.ExternalVerification.half_mem_mersenneAchievementSet_iff_unboundedTerminalFalse"
    )
    assert seam["comparator_declaration"] in comparator["theorem_names"]
    assert seam["source_transport_commit"] == (
        "7511c208c617b6e36fc56b5e0c5f780a3d4df831"
    )
    assert seam["canonical_claim_commit"] == (
        "0c2f4473e80352a7b4bd72a84d4e813978354509"
    )
    assert seam["source_transport_files"] == [
        "ExternalVerification/Challenge.lean",
        "ExternalVerification/Solution.lean",
        "ExternalVerification/Statements.lean",
    ]
    assert seam["transport_declarations"] == [
        "Erdos249257.ExternalVerification.half_mem_mersenneAchievementSet_iff_unboundedTerminalFalse"
    ]
    assert "upper-or-middle" in " ".join(seam["exact_hypotheses"])
    assert "no half-membership witness" in " ".join(seam["limitations"])
    assert "above" in seam["source_landscape_rank_relative_to"]
    assert "positiveHalfGreedySkips" in seam["source_landscape_rank_relative_to"]
    assert "not an unconditional" in seam["conclusion"]
    assert "verification/comparator.json" in seam["transport_admission_boundary"]
    assert "review matrix" in seam["transport_admission_boundary"]
    assert "boolean_mobius_exact_row_dynamics" in " ".join(seam["support_evidence"])
    assert "negative_mass_recovery" in " ".join(seam["conditional_peer_evidence"])
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
    ranked_by_family = {
        row["family_id"]: row for row in showcase["candidate_ranking"]
    }
    assert ranked_by_family["totient_carry_anti_compression"]["rank"] == 10
    assert ranked_by_family["half_membership_seam_classification"]["rank"] == 11
    assert "totient_kernel_rank" not in ranked_by_family
    anti_screen = [
        row for row in showcase["candidate_screening"]
        if row["family_id"] == "totient_carry_anti_compression"
    ]
    assert anti_screen == []
    kernel_screen = next(
        row for row in showcase["candidate_screening"]
        if row["family_id"] == "totient_kernel_rank"
    )
    assert "supports totient_carry_anti_compression" in kernel_screen["reason"]
    fixed = landscape_by_id["erdos249_fixed_precision_transport_no_go"]
    assert fixed["family_id"] == "fixed_precision_transport_no_go"
    assert fixed["disposition"] == "represented"
    assert fixed["prior_disposition"] == "deferred"
    assert fixed["canonical_family_binding"] == "fixed_precision_transport_no_go"
    assert fixed["comparator_eligibility"] == "committed_source_faithful_transport"
    assert fixed["queue_role"] == "source_landscape_review_with_committed_comparator_evidence"
    assert fixed["comparator_declaration"] == (
        "Erdos249257.ExternalVerification.fixedPrecisionTropicalNoGo"
    )
    assert fixed["comparator_declaration"] in comparator["theorem_names"]
    assert fixed["source_transport_commit"] == (
        "0c982671140b1a9a2e4f0e410ce807d0ad5e6363"
    )
    assert fixed["canonical_claim_commit"] == (
        "9d43aa4e4df76f08077bd10f9eb2f855f646028a"
    )
    assert fixed["source_transport_files"] == [
        "ExternalVerification/Challenge.lean",
        "ExternalVerification/Solution.lean",
        "ExternalVerification/Statements.lean",
    ]
    assert fixed["transport_declarations"] == [
        "Erdos249257.ExternalVerification.fixedPrecisionTropicalNoGo",
        "Erdos249257.ExternalVerification.vu_step_has_centred_completion",
        "Erdos249257.ExternalVerification.vu_word_has_prefix_locked_completion",
    ]
    assert "synthetic" in " ".join(fixed["limitations"])
    assert "finite-word" in " ".join(fixed["limitations"])
    assert "no #249 endpoint" in " ".join(fixed["limitations"])
    assert "negative-method" in fixed["reason"]
    coefficient = landscape_by_id["erdos251_coefficient_only_no_go"]
    assert coefficient["family_id"] == "coefficient_only_no_go"
    assert coefficient["disposition"] == "represented"
    assert coefficient["prior_disposition"] == "deferred"
    assert coefficient["canonical_family_binding"] == "coefficient_only_no_go"
    assert coefficient["comparator_eligibility"] == "committed_source_faithful_transport"
    assert coefficient["queue_role"] == "source_landscape_review_with_committed_comparator_evidence"
    assert coefficient["comparator_declaration"] == "Erdos249257.ExternalVerification.coefficientOnlyNoGo"
    assert coefficient["comparator_declaration"] in comparator["theorem_names"]
    assert coefficient["source_transport_commit"] == "c9d3660336d9ef4c9497549b26e29f3f953c138d"
    assert coefficient["canonical_claim_commit"] == "4c4ac3f98352a169d276186c84860e41e7aac731"
    assert coefficient["transport_declarations"] == [
        "Erdos249257.ExternalVerification.coefficientOnlyNoGo"
    ]
    assert "carryPartialSum_natCast_eq" in coefficient["source_declaration"]
    assert "carryCoeff_natCast_not_eventually_periodic" in coefficient["source_declaration"]
    assert "primeGap0_not_eventually_periodic" in coefficient["source_declaration"]
    assert "finite rational carry" in coefficient["hard_mechanism"]
    assert "infinite rational-sum limit" in " ".join(coefficient["limitations"])
    assert "stream-identification" in " ".join(coefficient["limitations"])
    assert "#251 endpoint" in " ".join(coefficient["limitations"])
    assert "routine finite searches" in coefficient["reason"]
    assert "verification/comparator.json" in coefficient["transport_admission_boundary"]
    assert "source-current committed" in coefficient["transport_admission_boundary"]
    small_mismatch = landscape_by_id["erdos251_small_mismatch_criterion"]
    assert small_mismatch["family_id"] == "small_mismatch_criterion"
    assert "conditional-endpoint leverage" in small_mismatch["source_landscape_rank_relative_to"].lower()
    assert small_mismatch["comparator_declaration"] == (
        "Erdos249257.ExternalVerification.primeGapTailShift_not_eventuallyIntegral_of_cofinal_small_mismatch"
    )
    assert small_mismatch["comparator_declaration"] in comparator["theorem_names"]
    assert "cofinally many adjacent small mismatches" in " ".join(small_mismatch["limitations"])
    assert "actual-prime" in small_mismatch["reason"]
    small_mismatch_screen = next(
        row
        for row in showcase["candidate_screening"]
        if row["declaration"] == small_mismatch["comparator_declaration"]
    )
    assert small_mismatch_screen["disposition"] == "supporting_conditional_endpoint"
    negative_mass = landscape_by_id["erdos243_negative_mass_recovery"]
    assert negative_mass["family_id"] == "negative_mass_recovery"
    assert negative_mass["disposition"] == "represented"
    assert negative_mass["prior_disposition"] == "deferred"
    assert negative_mass["canonical_family_binding"] == "negative_mass_recovery"
    assert negative_mass["comparator_eligibility"] == "committed_source_faithful_transport"
    assert negative_mass["queue_role"] == "source_landscape_review_with_committed_comparator_evidence"
    assert negative_mass["canonical_claim_commit"] == (
        "6bedcde3554f5d00ce58bd9921d54be4f19ff34c"
    )
    assert negative_mass["comparator_declaration"] == (
        "Erdos249257.ExternalVerification.sylvesterNext_eventually_of_summable_negativeRelativeMass"
    )
    assert negative_mass["comparator_declaration"] in comparator["theorem_names"]
    assert negative_mass["source_transport_commit"] == (
        "39d0c4bd6cb7e7c5322d4e21e65e7cba982700f5"
    )
    assert negative_mass["transport_declarations"] == [
        "Erdos249257.ExternalVerification.sylvesterNext_eventually_of_summable_negativeRelativeMass"
    ]
    assert "Summable" in " ".join(negative_mass["exact_hypotheses"])
    assert "negativeRelativeMass" in negative_mass["hard_mechanism"]
    assert "prime-specific producer" in " ".join(negative_mass["limitations"])
    assert "unconditional #243 endpoint" in " ".join(negative_mass["limitations"])
    assert "source-current committed" in negative_mass["transport_admission_boundary"]


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
    comparator_backed = next(
        row
        for row in damaged["candidate_value_dispositions"]["source_landscape_candidates"]
        if row["comparator_eligibility"] == "committed_source_faithful_transport"
    )
    comparator_backed["comparator_declaration"] = (
        "Erdos249257.ExternalVerification.not_a_committed_row"
    )
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
    test_v04_profile_rejects_missing_source_relationship()
    test_generated_formalization_reads_committed_head_only()
    test_structural_qualification_ignores_mutable_source_reads()
    test_pinned_classification_authorities_are_required()
    test_repository_intake_contract()
    test_full_current_roster_and_eight_problem_crosswalk()
    test_adversarial_candidate_universe_drop_is_not_silently_accepted()
    test_adversarial_selection_semantics_drop_is_not_silently_accepted()
    test_adversarial_value_disposition_drift_is_not_silently_accepted()
    test_adversarial_roster_drop_is_not_silently_accepted()
    print("palomar qualification tests: ok")
