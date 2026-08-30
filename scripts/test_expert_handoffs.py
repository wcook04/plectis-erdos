#!/usr/bin/env python3
# SPDX-FileCopyrightText: 2026 Will Cook
# SPDX-License-Identifier: Apache-2.0
"""Adversarial fixtures for the cross-domain expert-handoff contract."""

from __future__ import annotations

from copy import deepcopy

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
    compact = handoffs.compact_respondent_view(question)
    full = handoffs.respondent_view(question)
    for packet in (compact, full):
        route_memory = packet["route_memory"]
        assert route_memory["status"] == "unbound"
        assert route_memory["problem_number"] == 249
        assert route_memory["bindings"] == []
        assert route_memory["command"] == (
            "python3 scripts/query_route_memory.py --problem 249"
        )
        assert "current source digests" in route_memory["identity_contract"]
        assert "no resume route was invented" in route_memory["unbound_reason"]
        problem_route = packet["problem_route"]
        assert problem_route["status"] == "bound"
        assert problem_route["problem_number"] == 249
        assert problem_route["command"] == (
            "python3 scripts/query_corpus.py --route erdos_249"
        )
        assert "every review-matrix result family" in problem_route[
            "identity_contract"
        ]

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
        "conditional no-go consumer; novelty and significance unassessed"
    )
    weighted = next(
        row for row in carry_escape["relations"]
        if row["peer"]["family_id"] == "weighted_phase_carry_observer"
    )
    assert weighted["relation"] == "mechanism_support_for"
    assert weighted["peer"]["source_declaration"].endswith(
        "finite_realisedSpan_of_factorisation"
    )
    assert "actual three-prime running-LCM" in carry_escape["family"]["open_boundary"]
    assert "cofinal local-window escape producer" in carry_escape["family"][
        "open_boundary"
    ]

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


def test_three_prime_lcm_cells_handoff_exposes_source_mechanism_and_boundaries() -> None:
    packet = handoffs.semantic_endpoint_handoff_packet()
    supporting = {
        row["family"]["family_id"]: row
        for row in packet["supporting_families"]
    }
    assert set(supporting) == {
        "rank_two_kernel_no_go",
        "height_fibre_and_shell",
        "three_prime_lcm_cells",
    }
    assert [
        row["family"]["family_id"] for row in packet["supporting_families"]
    ] == [
        "rank_two_kernel_no_go",
        "height_fibre_and_shell",
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
    ]
    assert [support["evidence_kind"] for support in supports] == [
        "one_step_squaring",
        "all_times_squaring_orbit",
        "initial_phase_equivalence",
        "dyadic_root_obstruction",
    ]
    assert [support["relation"] for support in supports] == [
        "support",
        "support",
        "support",
        "contrary_evidence",
    ]
    assert supports[-1]["relation_class"] == "existing_family_contrary_evidence"
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
    assert "does not show that an actual totient phase" in supports[-1][
        "evidence_boundary"
    ]

    non_249 = next(
        row for row in handoffs.mathematical_questions() if row["problem"] == "257"
    )
    assert handoffs.source_current_supports(non_249) == []


def main() -> int:
    assert handoffs.protocol_errors() == []
    assert handoffs.FROZEN_PROBLEMS == {
        "68", "243", "249", "251", "257", "269", "1041", "1049"
    }
    test_mathematical_handoff_exposes_selector_without_route_invention()
    test_semantic_endpoint_handoff_uses_canonical_claims_and_palomar()
    test_three_prime_lcm_cells_handoff_exposes_source_mechanism_and_boundaries()
    test_strict_prime_successor_is_support_only()
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
        if row["domain"] == handoffs.MATH_DOMAIN:
            assert row["problem_route"]["status"] == "bound"
            assert row["problem_route"]["command"].startswith(
                "python3 scripts/query_corpus.py --route erdos_"
            )
        else:
            assert "problem_route" not in row

    for question in handoffs.all_questions():
        detail = handoffs.question_packet(None, question["id"])
        assert detail["packet_kind"] == "full_question"
        assert detail["count"] == 1
        assert detail["results"][0]["id"] == question["id"]
        if question["domain"] == handoffs.MATH_DOMAIN:
            assert detail["results"][0]["problem_route"]["status"] == "bound"

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
