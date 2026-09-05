#!/usr/bin/env python3
# SPDX-FileCopyrightText: 2026 Will Cook
# SPDX-License-Identifier: Apache-2.0
"""Adversarial fixtures for the cross-domain expert-handoff contract."""

from __future__ import annotations

from copy import deepcopy
from pathlib import Path
from unittest.mock import patch

import query_expert_handoffs as handoffs


def valid_response() -> dict:
    return {
        "question_id": "XQSYS-ten-minute-hostile-reader",
        "reviewer_identity": "independent-reviewer-1",
        "reviewed_at": "2026-07-26",
        "clone_revision": "1" * 40,
        "prior_project_context": False,
        "elapsed_seconds": 537,
        "problem_249_status": "OPEN",
        "problem_257_status": "OPEN",
        "farey_bound_provenance": "classical_farey_mediant",
        "farey_numerical_delta": 0,
        "equivalent_antecedents": 17,
        "substantial_antecedents": 23,
        "nonrestatement_results_249": [
            "Exact finite-level independence of the dyadic totient sections.",
            "A finite-rank shift countermodel that rules out a proof-strategy class.",
        ],
        "nonrestatement_results_257": [
            "Exact noncollapse of the reduced-denominator period for finite sums.",
            "Irrationality for every eventually periodic support.",
        ],
        "verdict_summary": (
            "The project contains checked results and barriers while openly "
            "identifying many equivalent reformulations; neither problem is closed."
        ),
        "source_paths_used": ["README.md", "docs/RESULTS.md"],
        "first_confusing_surface": "",
    }


def valid_review(response: dict) -> dict:
    question = handoffs.systems_questions()[0]
    criteria = {key: True for key in question["manual_review_rubric"]}
    return {
        "question_id": response["question_id"],
        "response_sha256": handoffs.object_digest(response),
        "evaluator_identity": "independent-evaluator-1",
        "evaluated_at": "2026-07-26",
        "reviewer_provenance_verified": True,
        "timing_provenance_verified": True,
        "criteria": criteria,
        "review_notes": "",
        "final_outcome": "accepted",
    }


def test_mathematical_handoff_exposes_selector_without_route_invention() -> None:
    question = next(
        row
        for row in handoffs.mathematical_questions()
        if row["id"] == "XQ249-lcm-diagonal-supply"
    )
    # Derived navigation depends only on the question's problem selector, so a
    # per-row copy repeated each block once per handoff.  It is packet-level.
    assert "route_memory" not in handoffs.compact_respondent_view(question)
    assert "problem_route" not in handoffs.respondent_view(question)
    index = handoffs.question_packet(None)
    detail = handoffs.question_packet(None, question["id"])
    for packet in (index, detail):
        entry = packet["problem_navigation"]["problems"]["249"]
        route_memory = entry["route_memory"]
        assert route_memory["status"] == "unbound"
        assert route_memory["problem_number"] == 249
        assert route_memory["bindings"] == []
        assert route_memory["command"] == (
            "python3 scripts/query_route_memory.py --problem 249"
        )
        problem_route = entry["problem_route"]
        assert problem_route["status"] == "bound"
        assert problem_route["problem_number"] == 249
        assert problem_route["command"] == (
            "python3 scripts/query_corpus.py --route erdos_249"
        )

    # The per-question packet still states the complete contracts ...
    detail_entry = detail["problem_navigation"]["problems"]["249"]
    assert "current source digests" in detail_entry["route_memory"][
        "identity_contract"
    ]
    assert "no resume route was invented" in detail_entry["route_memory"][
        "unbound_reason"
    ]
    assert "every review-matrix result family" in detail_entry["problem_route"][
        "identity_contract"
    ]
    # ... and the bounded index names them instead of dropping them silently.
    navigation_receipt = index["problem_navigation"][
        "bounded_navigation_omission_receipt"
    ]
    for field in (
        "route_memory.identity_contract",
        "route_memory.unbound_reason",
        "route_memory.boundary",
        "problem_route.identity_contract",
        "problem_route.boundary",
        "problem_route.paper_source.identity_contract",
    ):
        assert field in navigation_receipt["omitted_fields"], field
    assert "--question" in navigation_receipt["question_drilldown"]

    invalid = handoffs.route_memory_handoff(
        {"domain": handoffs.MATH_DOMAIN, "problem": "249/257"}
    )
    assert invalid["status"] == "unbound"
    assert invalid["bindings"] == []
    assert "command" not in invalid
    assert "frozen public problem selectors" in invalid["unbound_reason"]
    invalid_problem_route = handoffs.problem_route_handoff(
        {"domain": handoffs.MATH_DOMAIN, "problem": "249/257"}
    )
    assert invalid_problem_route["status"] == "unbound"
    assert "command" not in invalid_problem_route


def test_semantic_endpoint_handoff_uses_canonical_claims_and_palomar() -> None:
    route = handoffs.semantic_endpoint_handoff_route()
    assert route["command"] == (
        "python3 scripts/query_expert_handoffs.py --semantic-handoff"
    )
    assert route["root_family_ids"] == [
        "small_mismatch_criterion",
        "conditional_carry_escape",
    ]

    packet = handoffs.semantic_endpoint_handoff_packet()
    assert packet["root_family_ids"] == route["root_family_ids"]
    assert "no second rank store" in route["authority_posture"]
    assert "all-eight-problem semantic registry" in packet["coverage_boundary"]
    assert route["source_current_candidate_ids"] == [
        "critical_pair_metric_scale"
    ]

    candidate = packet["source_current_candidates"][0]
    candidate_family = candidate["family"]
    assert candidate_family["family_id"] == "critical_pair_metric_scale"
    assert candidate_family["problem"] == 1041
    assert candidate_family["canonicalization_status"] == (
        "pending_claims_palomar_registration"
    )
    assert candidate_family["authority_rank"] is None
    assert "deep_mechanism" in candidate_family["proposed_reader_tier"]
    assert "ordinary proof-level global Euclidean budget" in candidate_family[
        "proof_status"
    ]
    assert "containment" in candidate_family["open_boundary"]
    assert "reciprocal critical balance" in candidate["hard_mechanism"]
    assert "sharp constant-2" in candidate["hard_mechanism"]
    declarations = {
        row["name"]: row for row in candidate["source_declarations"]
    }
    assert set(declarations) == {
        "two_add_le_two_of_bernoulli",
        "two_add_le_two_of_disk_inverse_balance",
        "two_add_lt_two_of_disk_inverse_balance_of_strict_diameter",
        "exists_two_roots_dist_sum_le_two_mul_geomMean",
        "spoke_escapes_lemniscate_exact",
        "nearestSpoke_reciprocal_balance",
        "nearestSpoke_unique_nearest_normSq",
        "nearestSpoke_unique_nearest_spoke_escapes",
        "allStraightCubic_roots_in_unitDisk",
        "allStraightCubic_roots",
        "allStraightCubic_every_pair_midpoint_escapes",
    }
    assert all(
        row["module"] == "ErdosProblems/Erdos1041/CriticalTwoRootProximity.lean"
        and isinstance(row["line"], int)
        and row["coordinate_authority"] == "direct Lean source declaration"
        for row in declarations.values()
    )
    assert candidate["source_provenance"] == {
        "promoted_module": "ErdosProblems/Erdos1041/CriticalTwoRootProximity.lean",
        "public_research_module": "research_corpus/Erdos1041/CriticalTwoRootProximity.lean",
        "byte_identical": True,
        "promotion_commit": "678ddff10a5e6811dd2d991f52cfa775b6424c3e",
        "boundary": (
            "The promoted module is the buildable source authority; the "
            "research-corpus copy remains the public provenance anchor."
        ),
    }
    assert candidate["comparator_representative"]["declaration"] == (
        "Erdos249257.ExternalVerification.exists_two_roots_dist_sum_le_two_mul_geomMean"
    )
    assert candidate["comparator_representative"]["config"] == (
        "verification/comparator.json"
    )
    assert candidate["public_reuse"] == {
        "module": "examples/ExternalVerificationPortfolio/Problem1041.lean",
        "declaration": "critical_balance_selects_two_roots_at_geomMean_scale",
        "reuses": (
            "Erdos249257.ExternalVerification.exists_two_roots_dist_sum_le_two_mul_geomMean"
        ),
        "commit": "b8c69ae0a5d90c32fb60b73d57fb88308a1f0514",
        "validation": "#check plus focused canonical Lean build passed",
        "boundary": (
            "This example reuses the Euclidean metric budget only; it does "
            "not supply a lemniscate-contained path."
        ),
    }
    assert any(
        row["declaration"] == "nearestSpoke_unique_nearest_spoke_escapes"
        for row in candidate["natural_friction_evidence"]
    )
    assert any(
        row["declaration"] == "allStraightCubic_every_pair_midpoint_escapes"
        for row in candidate["natural_friction_evidence"]
    )
    assert len(candidate["canonical_context"]) == 4
    assert [
        row["family"]["family_id"] for row in candidate["canonical_context"]
    ] == ["newton_value_decay", "ray_separation", "translation_avoidance", "root_retention"]
    assert "No Palomar programme position" in candidate_family["rank_authority"]

    small_mismatch, carry_escape = packet["roots"]
    assert small_mismatch["family"]["family_id"] == "small_mismatch_criterion"
    assert small_mismatch["family"]["proof_status"] == (
        "conditional actual-prime-gap endpoint reduction; novelty and significance "
        "unassessed"
    )
    assert small_mismatch["family"]["source_declaration"].endswith(
        "rationalPrimeGapTail_has_positive_shift_not_eventually_small"
    )
    assert any(
        row["peer"]["family_id"] == "coefficient_only_no_go"
        and row["relation_class"] == "natural_friction"
        for row in small_mismatch["relations"]
    )
    assert "does not prove the supply or actual smallness" in small_mismatch[
        "family"
    ]["open_boundary"]

    assert carry_escape["family"]["family_id"] == "conditional_carry_escape"
    assert carry_escape["family"]["proof_status"] == (
        "conditional actual-series reduction with a formalised finite consumer; novelty unassessed"
    )
    weighted = next(
        row for row in carry_escape["relations"]
        if row["peer"]["family_id"] == "weighted_phase_carry_observer"
    )
    assert weighted["relation"] == "mechanism_support_for"
    assert weighted["peer"]["source_declaration"].endswith(
        "finite_realisedSpan_of_factorisation"
    )
    boundary = carry_escape["family"]["open_boundary"]
    assert "CofinalLocalWindowEscape" in boundary
    assert "This cofinal escape is unproved" in boundary
    assert "ordinary mathematical arguments" in boundary
    assert "not new Comparator evidence or completed Lean formalizations" in boundary

    # Relation-array order is not a hierarchy: canonical programme positions
    # determine the emitted peer order even when the input array is reversed.
    palomar = handoffs.load_json(handoffs.PALOMAR)
    claims = handoffs._claim_family_rows(handoffs.load_json(handoffs.CLAIMS))
    ranks = handoffs._canonical_family_ranks(palomar)
    reversed_palomar = deepcopy(palomar)
    reversed_palomar["selection_contract"]["family_relations"].reverse()
    assert handoffs._family_hierarchy(
        "conditional_carry_escape", ranks, palomar, claims
    ) == handoffs._family_hierarchy(
        "conditional_carry_escape", ranks, reversed_palomar, claims
    )
    assert handoffs.critical_pair_metric_scale_candidate_handoff(
        reversed_palomar, handoffs.load_json(handoffs.CLAIMS)
    ) == candidate


def test_three_prime_lcm_cells_handoff_exposes_source_mechanism_and_boundaries() -> None:
    packet = handoffs.semantic_endpoint_handoff_packet()
    supporting = {
        row["family"]["family_id"]: row
        for row in packet["supporting_families"]
    }
    assert set(supporting) == {
        "actual_lcm_orbit_separation",
        "first_harmonic_pivot_decomposition",
        "rank_two_kernel_no_go",
        "height_fibre_and_shell",
        "dyadic_block_alphabet",
        "three_prime_lcm_cells",
    }
    assert [
        row["family"]["family_id"] for row in packet["supporting_families"]
    ] == [
        "actual_lcm_orbit_separation",
        "first_harmonic_pivot_decomposition",
        "rank_two_kernel_no_go",
        "height_fibre_and_shell",
        "dyadic_block_alphabet",
        "three_prime_lcm_cells",
    ]
    handoff = supporting["three_prime_lcm_cells"]
    family = handoff["family"]
    assert family["family_id"] == "three_prime_lcm_cells"
    assert family["problem"] == 269
    assert family["authority_rank"]["programme_position"] == 6
    assert family["palomar_disposition"] == "supporting_exact_identity"
    assert family["proof_status"] == "locally proved result; novelty unassessed"
    assert family["claim_id"] == "three_prime_running_lcm"
    assert "smoothPrefixLcm_eq_threePrimeHeight" in handoff["hard_mechanism"]
    assert "SameThreePrimeLogCell" in handoff["hard_mechanism"]
    assert "3*count+1" in handoff["hard_mechanism"]

    source = {row["name"]: row for row in handoff["source_declarations"]}
    expected_names = {
        "smoothPrefixLcm_eq_threePrimeHeight",
        "SameThreePrimeLogCell",
        "threePrimeHeight_eq_of_sameLogCell",
        "smoothPrefixLcm_eq_of_sameLogCell",
        "threePrimeKernelQ_eq_of_sameLogCell",
        "threePrimeHeight_firstLogStep",
        "threePrimeHeight_secondLogStep",
        "threePrimeHeight_thirdLogStep",
        "smoothPrefixLcm_firstLogStep",
        "smoothPrefixLcm_secondLogStep",
        "smoothPrefixLcm_thirdLogStep",
        "threePrimePositiveJumpSet_card",
        "threePrimeJumpSetWithOrigin_card",
    }
    assert set(source) == expected_names
    assert all(
        row["module"] == "ErdosProblems/Erdos269/ThreePrimeRunningLcm.lean"
        and isinstance(row["line"], int)
        and row["signature"]
        for row in source.values()
    )
    assert handoff["wrapper"]["declaration"] == (
        "Erdos249257.ExternalVerification.smoothPrefixLcm_eq_threePrimeHeight"
    )
    assert handoff["wrapper"]["module"] == "ExternalVerification/Solution.lean"
    assert isinstance(handoff["wrapper"]["line"], int)

    cards = {row["id"]: row for row in handoff["mechanism_cards"]}
    assert cards["running_lcm_identity"]["wrapper_declaration"] == handoff[
        "wrapper"
    ]["declaration"]
    assert "smoothPrefixLcm_eq_of_sameLogCell" in cards[
        "log_cell_constancy"
    ]["declaration_names"]
    assert "smoothPrefixLcm_firstLogStep" in cards[
        "coordinate_jumps_and_counts"
    ]["declaration_names"]

    boundaries = handoff["open_producer_boundaries"]
    assert "actual three-prime running-LCM series" in boundaries[
        "actual_series_bridge"
    ]
    assert "CofinalLocalWindowEscape" in boundaries["cofinal_escape_producer"]
    assert boundaries["endpoint"] == "Cell structure alone does not prove irrationality."
    related = {
        row["family"]["family_id"]: row for row in handoff["related_families"]
    }
    assert related["conditional_carry_escape"]["relation_class"] == (
        "boundary_context_not_palomar_edge"
    )
    assert related["weighted_phase_carry_observer"]["relation_class"] == (
        "boundary_context_not_palomar_edge"
    )
    assert "actual-series bridge" in related["conditional_carry_escape"]["reason"]
    assert "quotient coboundary" in related["weighted_phase_carry_observer"]["reason"]
    assert "not an insertion-ordered relation store" in handoff[
        "relation_authority"
    ]
    assert handoff["follow"]["family"] == (
        "python3 scripts/query_semantic.py family-relations three_prime_lcm_cells"
    )

    rank_two = supporting["rank_two_kernel_no_go"]
    assert rank_two["family"]["authority_rank"]["programme_position"] == 3
    assert rank_two["family"]["palomar_disposition"] == "supporting_finite_no_go"
    assert rank_two["family"]["proof_status"] == "no-go result"
    assert rank_two["family"]["claim_id"] == "three_prime_kernel_minor"
    assert "nonzero (exactly -1/15)" in rank_two["hard_mechanism"]
    assert {
        row["name"] for row in rank_two["source_declarations"]
    } == {
        "kernel_235_origin",
        "kernel_235_two",
        "kernel_235_three",
        "kernel_235_six",
        "kernel_235_not_rankOne",
        "kernel_235_minor_eq_neg_one_fifteen",
    }
    assert rank_two["wrapper"]["declaration"] == (
        "Erdos249257.ExternalVerification.kernel_235_minor_eq_neg_one_fifteen"
    )
    assert rank_two["related_families"][0]["family"]["family_id"] == (
        "conditional_carry_escape"
    )
    assert rank_two["related_families"][0]["relation_class"] == (
        "canonical_palomar_edge"
    )
    assert rank_two["canonical_relations"][0]["relation"] == (
        "contrary_evidence_for"
    )

    height = supporting["height_fibre_and_shell"]
    assert height["family"]["authority_rank"]["programme_position"] == 4
    assert height["family"]["palomar_tier"] == (
        "deep_mechanism_and_classification"
    )
    assert height["family"]["proof_status"] == (
        "locally proved result; novelty unassessed"
    )
    assert {
        row["name"] for row in height["source_declarations"]
    } == {
        "smoothHeightFiber_kernel_sum",
        "finiteSmoothKernelSum_groupedByHeight",
        "smoothExponentShell_card_quadratic",
    }
    assert "quadratic function" in height["hard_mechanism"]
    assert "divisibility bridge" in height["open_producer_boundaries"][
        "divisibility_bridge"
    ]

    dyadic = supporting["dyadic_block_alphabet"]
    assert dyadic["family"]["authority_rank"]["programme_position"] == 5
    assert dyadic["family"]["palomar_tier"] == "supporting_and_long_tail"
    assert dyadic["family"]["proof_status"] == (
        "locally proved result; novelty unassessed"
    )
    assert {
        row["name"] for row in dyadic["source_declarations"]
    } == {
        "dyadicBlockBase235",
        "dyadicBlockBase235_cases",
        "dyadicBlockBase235_mem_interval",
    }
    assert "four-symbol alphabet" in dyadic["hard_mechanism"]
    assert "cofinal residue" in dyadic["open_producer_boundaries"][
        "cofinal_escape"
    ]

    actual = supporting["actual_lcm_orbit_separation"]
    assert actual["family"]["problem"] == 249
    assert actual["family"]["authority_rank"]["programme_position"] == 1
    assert actual["family"]["palomar_selection_status"] == "represented"
    assert actual["family"]["claim_id"] == (
        "actual_lcm_orbit_nonintegrality_frontier"
    )
    assert "explicit error radius" in actual["hard_mechanism"]
    assert "1/32" in actual["hard_mechanism"]
    assert {
        row["name"] for row in actual["source_declarations"]
    } == {
        "irrational_totientSeries_iff_actualLcmOrbitNonintegralitySupply",
        "irrational_totientSeries_of_actualLcmOrbitNonintegralitySupply",
        "actualLcmTailOrbit_eq_scaled_totientSeries_sub_prefix",
        "actualLcmTailOrbit_sub_rawApprox_eq",
        "abs_actualLcmTailOrbit_sub_rawApprox_lt",
        "PowerTwoActualLcmOrbitSeparationSupply",
        "powerTwoActualPenultimateSignedMarginSupply_of_actualLcmOrbitSeparation",
        "irrational_totientSeries_of_actualLcmOrbitSeparationSupply",
        "actualLcmTailDiff_shift_pos",
        "actualLcm_trueEndpointSurvivor_neg",
        "actualLcm_integral_forces_topEdgeResidue",
    }
    assert isinstance(actual["wrapper"]["line"], int)
    assert {
        row["family"]["family_id"] for row in actual["related_families"]
    } == {"strict_prime_tail_orbit_gap", "first_harmonic_pivot_decomposition"}
    assert all(
        row["relation_class"] == "canonical_palomar_edge"
        for row in actual["related_families"]
    )
    assert "cofinal separation supply" in actual[
        "open_producer_boundaries"
    ]["cofinal_separation_supply"]

    pivot = supporting["first_harmonic_pivot_decomposition"]
    assert pivot["family"]["problem"] == 249
    assert pivot["family"]["authority_rank"]["programme_position"] == 2
    assert pivot["family"]["palomar_selection_status"] == "represented"
    assert pivot["family"]["claim_id"] == "first_harmonic_pivot_decomposition"
    assert "four-term first-harmonic decomposition" in pivot["hard_mechanism"]
    assert "9X/10" in pivot["hard_mechanism"]
    assert len(pivot["source_declarations"]) == 9
    assert all(
        row["module"] == "Erdos249257/FirstHarmonicPivot.lean"
        and isinstance(row["line"], int)
        and row["signature"]
        for row in pivot["source_declarations"]
    )
    assert isinstance(pivot["wrapper"]["line"], int)
    assert {
        row["family_id"] for row in pivot["related_families"]
    } == {"actual_lcm_orbit_separation"}
    assert pivot["related_families"][0]["relation"] == (
        "independent_conditional_endpoint_peer"
    )
    assert "cofinal decorrelation" in pivot["open_producer_boundaries"][
        "cofinal_decorrelation"
    ]


def test_strict_prime_successor_is_support_only() -> None:
    question = next(
        row
        for row in handoffs.mathematical_questions()
        if row["id"] == "XQ249-adjacent-phase-separation"
    )
    supports = handoffs.source_current_supports(question)
    assert [support["source_declaration"] for support in supports] == [
        "ErdosProblems.Erdos249.tailOrbitFirstExp_succ",
        "ErdosProblems.Erdos249.tailOrbitFirstExp_add",
        "ErdosProblems.Erdos249.naturalPrimeTailOrbitStrictGap_iff_initial_phase",
        "ErdosProblems.Erdos249.not_naturalPrimeTailOrbitStrictGap_of_dyadic_root",
        "ErdosProblems.Erdos249.tailOrbitFirstExp_zero_eq_scaled_angle",
        "ErdosProblems.Erdos249.tailOrbitFirstExp_eq_one_iff_tail_diff_mem_int",
        "ErdosProblems.Erdos249.exists_tailOrbitFirstExp_zero_pow_two_eq_one_iff_dyadic",
        "ErdosProblems.Erdos249.tailOrbitFirstExp_zero_pow_two_ne_one_upto_sixteen",
        "ErdosProblems.Erdos249.cofinally_tailOrbitFirstExp_re_nonpos_of_not_dyadic",
        "ErdosProblems.Erdos249.naturalPrimeTailOrbitStrictGap_of_cofinal_nonpositive_prime_shift",
    ]
    assert [support["evidence_kind"] for support in supports] == [
        "one_step_squaring",
        "all_times_squaring_orbit",
        "initial_phase_equivalence",
        "dyadic_root_obstruction",
        "scaled_angle_normal_form",
        "integral_tail_phase_equivalence",
        "dyadic_root_characterization",
        "finite_nonroot_prefix",
        "cofinal_nonpositive_phase",
        "prime_shift_bridge",
    ]
    assert [support["relation"] for support in supports] == [
        "support",
        "support",
        "support",
        "contrary_evidence",
        "support",
        "support",
        "support",
        "contrary_evidence",
        "support",
        "support",
    ]
    assert supports[3]["relation_class"] == "existing_family_contrary_evidence"
    assert supports[7]["relation_class"] == "existing_family_contrary_evidence"
    assert all(
        support["relation_class"] == "existing_family_support_only"
        for support in supports
        if support not in (supports[3], supports[7])
    )
    for support in supports:
        assert support["family_id"] == "strict_prime_tail_orbit_gap"
        assert support["proof_status"] == "conditional reduction"
        assert support["source"]["module"] == (
            "ErdosProblems/Erdos249/TotientStrictPrimeEscape.lean"
        )
        assert support["hard_mechanism"]
        assert "cofinal natural-prime strict-gap" in support[
            "natural_friction_evidence"
        ]
        assert support["follow"] == (
            "python3 scripts/query_semantic.py family-relations "
            "strict_prime_tail_orbit_gap"
        )
    # Coordinates are generated navigation data: compare the handoff output
    # with the current atlas instead of pinning historical line numbers.  This
    # keeps the consumer honest when a source-current proof grows above it.
    atlas_lines = {
        row["name"]: row["line"]
        for row in handoffs.load_json(handoffs.ATLAS).get("declarations", [])
    }
    expected_names = (
        "tailOrbitFirstExp_succ",
        "tailOrbitFirstExp_add",
        "naturalPrimeTailOrbitStrictGap_iff_initial_phase",
        "not_naturalPrimeTailOrbitStrictGap_of_dyadic_root",
        "tailOrbitFirstExp_zero_eq_scaled_angle",
        "tailOrbitFirstExp_eq_one_iff_tail_diff_mem_int",
        "exists_tailOrbitFirstExp_zero_pow_two_eq_one_iff_dyadic",
        "tailOrbitFirstExp_zero_pow_two_ne_one_upto_sixteen",
        "cofinally_tailOrbitFirstExp_re_nonpos_of_not_dyadic",
        "naturalPrimeTailOrbitStrictGap_of_cofinal_nonpositive_prime_shift",
    )
    for support, name in zip(supports, expected_names):
        expected_line = atlas_lines.get(name)
        if expected_line is None:
            raise AssertionError(f"atlas lacks current declaration {name}")
        if support["source"]["line"] != expected_line:
            raise AssertionError(
                f"handoff coordinate drift for {name}: "
                f"{support['source']['line']} != {expected_line}"
            )
    assert "does not show that an actual totient phase" in supports[3][
        "evidence_boundary"
    ]
    assert "does not prove that hypothesis" in supports[-1]["evidence_boundary"]

    non_249 = next(
        row for row in handoffs.mathematical_questions() if row["problem"] == "257"
    )
    assert handoffs.source_current_supports(non_249) == []


def test_bounded_support_index_head_and_receipt_agree_with_source() -> None:
    """The emitted head is the top of the source order; the receipt is exact."""
    question = next(
        row
        for row in handoffs.mathematical_questions()
        if row["id"] == "XQ249-lcm-diagonal-supply"
    )
    supports = handoffs.source_current_supports(question)
    index = handoffs.question_packet(None)
    detail = handoffs.question_packet(None, question["id"])

    block = index["source_current_support_index"]
    head = block["ranked_head"]
    receipt = block["bounded_support_omission_receipt"]
    assert len(head) == handoffs.COMPACT_SUPPORT_HEAD
    assert [row["rank"] for row in head] == list(range(1, len(head) + 1))
    assert [row["source_declaration"] for row in head] == [
        row["source_declaration"] for row in supports[: len(head)]
    ]
    assert receipt["support_count"] == len(supports)
    assert receipt["omitted_support_count"] == len(supports) - len(head)
    assert receipt["omitted_source_declarations"] == [
        row["source_declaration"] for row in supports[len(head):]
    ]
    # A contiguous head can hide a relation entirely, so the receipt says which.
    assert receipt["omitted_relation_counts"]["contrary_evidence"] == 2
    assert receipt["question_drilldown"] == (
        "python3 scripts/query_expert_handoffs.py --question "
        "XQ249-lcm-diagonal-supply"
    )
    assert receipt["claim_drilldown"] == handoffs.SUPPORT_CLAIM_DRILLDOWN

    # The family-level fields are carried once, not once per support, and the
    # boundary paragraph the supports repeat under two names is emitted whole.
    for field in receipt["hoisted_family_fields"]:
        assert all(row[field] == supports[0][field] for row in supports)
        assert all(field not in row for row in head)
    for alias in receipt["family_boundary_aliases"]:
        assert all(row[alias] == block["family_boundary"] for row in supports)
    assert block["applies_to_questions"] == [
        "XQ249-lcm-diagonal-supply",
        "XQ249-pivot-decorrelation",
        "XQ249-adjacent-phase-separation",
    ]

    # The drilldown the receipt names really does return the whole list.
    detail_block = detail["source_current_support_index"]
    assert [row["source_declaration"] for row in detail_block["ranked_head"]] == [
        row["source_declaration"] for row in supports
    ]
    assert detail_block["bounded_support_omission_receipt"][
        "omitted_support_count"
    ] == 0

    # A #257 handoff has no strict-prime supports, so it carries no block.
    without = handoffs.question_packet(
        None, "XQ257-second-channel-separation"
    )
    assert "source_current_support_index" not in without


def test_strict_prime_cross_problem_source_route_is_rejected() -> None:
    """A claim row cannot redirect a source-current support to another problem."""
    question = next(
        row
        for row in handoffs.mathematical_questions()
        if row["id"] == "XQ249-adjacent-phase-separation"
    )
    original_load_json = handoffs.load_json

    def hostile_load_json(path: Path) -> dict:
        payload = original_load_json(path)
        if path != handoffs.CLAIMS:
            return payload
        mutated = deepcopy(payload)
        family = next(
            row
            for row in mutated["claims"]
            if row.get("id") == "strict_prime_tail_orbit_gap"
        )
        declaration = next(
            row
            for row in family["declarations"]
            if row.get("name") == "tailOrbitFirstExp_succ"
        )
        declaration["module"] = (
            "ErdosProblems/Erdos257/MersenneSubseriesRigidity.lean"
        )
        return mutated

    with patch.object(handoffs, "load_json", side_effect=hostile_load_json):
        try:
            handoffs.source_current_supports(question)
        except ValueError as error:
            assert "routes source declaration outside" in str(error), (
                f"unexpected cross-problem rejection: {error}"
            )
        else:
            raise AssertionError("cross-problem source route was accepted")


def main() -> int:
    assert handoffs.protocol_errors() == []
    assert handoffs.FROZEN_PROBLEMS == {
        "68", "243", "249", "251", "257", "269", "1041", "1049"
    }
    test_mathematical_handoff_exposes_selector_without_route_invention()
    test_semantic_endpoint_handoff_uses_canonical_claims_and_palomar()
    test_three_prime_lcm_cells_handoff_exposes_source_mechanism_and_boundaries()
    test_strict_prime_successor_is_support_only()
    test_bounded_support_index_head_and_receipt_agree_with_source()
    test_strict_prime_cross_problem_source_route_is_rejected()
    packet = handoffs.question_packet(None)
    assert packet["packet_kind"] == "compact_index"
    assert packet["count"] == 6
    assert packet["domain_counts"] == {"mathematics": 5, "systems": 1}
    for row in packet["results"]:
        assert row["current_hypothesis"]
        assert row["hypothesis_confidence"] == "low"
        assert len(row["plausible_alternatives"]) >= 2
        assert len(row["current_evidence"]) >= 2
        assert len(row["discriminating_evidence"]) >= 2
        assert row["detail_command"].endswith(row["id"])
        assert "problem_route" not in row
        assert "route_memory" not in row
        assert "source_current_supports" not in row
        if row["domain"] == handoffs.MATH_DOMAIN:
            entry = packet["problem_navigation"]["problems"][row["problem"]]
            assert entry["problem_route"]["status"] == "bound"
            assert entry["problem_route"]["command"].startswith(
                "python3 scripts/query_corpus.py --route erdos_"
            )
        else:
            assert row["problem"] not in packet["problem_navigation"]["problems"]

    for question in handoffs.all_questions():
        detail = handoffs.question_packet(None, question["id"])
        assert detail["packet_kind"] == "full_question"
        assert detail["count"] == 1
        assert detail["results"][0]["id"] == question["id"]
        if question["domain"] == handoffs.MATH_DOMAIN:
            entry = detail["problem_navigation"]["problems"][question["problem"]]
            assert entry["problem_route"]["status"] == "bound"

    second_channel = next(
        row
        for row in handoffs.mathematical_questions()
        if row["id"] == "XQ257-second-channel-separation"
    )
    assert second_channel["measured_evidence_artifact"] == (
        "docs/measurements/second_channel_separation_probe.json"
    )
    assert second_channel["measurement_check_command"] == (
        "python3 scripts/probe_second_channel_separation.py --check"
    )

    systems_packet = handoffs.question_packet(handoffs.SYSTEMS_DOMAIN)
    assert systems_packet["packet_kind"] == "full_question"
    assert systems_packet["count"] == 1
    systems_row = systems_packet["results"][0]
    assert "acceptance" not in systems_row
    assert "review_template" not in systems_row

    response = valid_response()
    assert handoffs.validate_response(response) == []
    assert handoffs.validate_response([]) == ["response must be a JSON object"]
    review = valid_review(response)
    assert handoffs.validate_review(response, review) == []

    mutations = []
    too_slow = deepcopy(response)
    too_slow["elapsed_seconds"] = 601
    mutations.append(too_slow)
    wrong_farey = deepcopy(response)
    wrong_farey["farey_numerical_delta"] = 1
    mutations.append(wrong_farey)
    restatement_only = deepcopy(response)
    restatement_only["nonrestatement_results_249"] = []
    mutations.append(restatement_only)
    wrong_endpoint = deepcopy(response)
    wrong_endpoint["problem_257_status"] = "CLOSED"
    mutations.append(wrong_endpoint)
    empty_verdict = deepcopy(response)
    empty_verdict["verdict_summary"] = ""
    mutations.append(empty_verdict)
    duplicate_result = deepcopy(response)
    duplicate_result["nonrestatement_results_257"][1] = (
        duplicate_result["nonrestatement_results_257"][0]
    )
    mutations.append(duplicate_result)
    nonexistent_source = deepcopy(response)
    nonexistent_source["source_paths_used"] = ["docs/does-not-exist.md"]
    mutations.append(nonexistent_source)

    for mutation in mutations:
        assert handoffs.validate_response(mutation), mutation

    bad_digest = deepcopy(review)
    bad_digest["response_sha256"] = "0" * 64
    assert handoffs.validate_review(response, bad_digest)
    unearned_acceptance = deepcopy(review)
    first_criterion = next(iter(unearned_acceptance["criteria"]))
    unearned_acceptance["criteria"][first_criterion] = False
    assert handoffs.validate_review(response, unearned_acceptance)
    unexplained_revision = deepcopy(review)
    unexplained_revision["final_outcome"] = "needs_revision"
    assert handoffs.validate_review(response, unexplained_revision)

    print(
        "expert handoff tests: 7 response and 3 review mutations rejected"
    )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
