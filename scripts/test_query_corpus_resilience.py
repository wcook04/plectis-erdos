#!/usr/bin/env python3
# SPDX-FileCopyrightText: 2026 Will Cook
# SPDX-License-Identifier: Apache-2.0
"""Focused checks for semantic query translation and partial-artifact resilience."""

from __future__ import annotations

import json
import tempfile
from pathlib import Path

import query_corpus


def check_dictionary_budget_and_shape() -> None:
    packet = query_corpus.semantic_dictionary_packet()
    encoded = json.dumps(packet, ensure_ascii=False, separators=(",", ":")).encode(
        "utf-8"
    )
    assert len(encoded) <= 12_000
    assert {row["id"] for row in packet["operators"]} == {
        "analogy",
        "digest",
        "falsify",
        "frontier",
        "locate",
        "support",
        "trace",
    }
    assert packet["authority_posture"].endswith(
        "not_proof_or_claim_status_authority"
    )
    assert packet["schema_version"] == "erdos249257-semantic-dictionary/2"
    discovery = packet["route_discovery_contract"]
    assert discovery["source"].startswith("docs/claims.json::")
    by_route = {row["route_id"]: row for row in discovery["routes"]}
    assert "which paper proofs lack semantic interpretation" in by_route[
        "agent_native_corpus_navigation"
    ]["discovery_terms"]
    assert any(
        row["id"] == "semantic_population_backlog"
        for row in packet["vocabulary"]
    )


def check_vocabulary_mismatch_queries() -> None:
    assert not query_corpus.SUPPRESSED_DECLARATION_ATLAS_ROWS
    for comment_word in ("makes", "invariant"):
        try:
            query_corpus.declaration_packet(comment_word, 1)
        except KeyError:
            pass
        else:
            raise AssertionError(
                "comment prose must not be queryable as a declaration"
            )
    assert not any(
        row.get("kind") == "declaration" and row.get("name") == "makes"
        for row in query_corpus.search_packet("makes", 20)["results"]
    )
    for wrapped_name in (
        "diagonalAdjacentSuffixResidue_powerTwo_oddDepth_central_iff_halfWordBand",
        "HalfTerminalOnlyScaledVanishingSequence.ofCofinalTerminalOnlyStrip",
    ):
        wrapped = query_corpus.declaration_packet(wrapped_name, 1)
        assert wrapped["matches"][0]["name"] == wrapped_name
    assert query_corpus.search_terms(
        "half_mem_mersenneAchievementSet_of_middleProducerTailEscape"
    ) >= {
        "half",
        "mem",
        "mersenne",
        "achievement",
        "set",
        "middle",
        "producer",
        "tail",
        "escape",
    }
    qualified = query_corpus.declaration_packet(
        "Erdos249257.TotientTailPeriodKiller.fixedPrecisionTropicalNoGo",
        1,
    )
    assert qualified["matches"][0]["name"] == "fixedPrecisionTropicalNoGo"
    assert qualified["matches"][0]["qualified_name"] == (
        "Erdos249257.TotientTailPeriodKiller.fixedPrecisionTropicalNoGo"
    )
    dotted = query_corpus.declaration_packet(
        "BooleanMobiusCarryCertificate.reconstructsSupport",
        1,
    )
    assert dotted["matches"][0]["qualified_name"] == (
        "Erdos249257.BooleanMobiusCarryCertificate.reconstructsSupport"
    )
    private = query_corpus.declaration_packet("mod_six_cases", 1)
    assert not private["matches"][0]["externally_addressable"]
    private_support = query_corpus.semantic_slice_packet(
        "I need the mod_six_cases theorem",
        4,
    )
    assert not any(
        row["qualified_declaration"].endswith(".mod_six_cases")
        for row in private_support["operator_synthesis"].get(
            "lean_application_candidates", []
        )
    )
    rank_two = query_corpus.search_packet("is rank two worth pursuing", 5)
    assert rank_two["query_interpretation"]["operator"]["id"] == "falsify"
    assert rank_two["results"][0]["kind"] == "declaration"
    assert (
        rank_two["results"][0]["name"]
        == "rank2_kill_sound_but_not_shallower_at_cell"
    )

    half_value = query_corpus.search_packet(
        "what should I try next for the half value problem", 5
    )
    assert half_value["query_interpretation"]["operator"]["id"] == "frontier"
    assert [
        (row["kind"], row.get("id"))
        for row in half_value["results"][:2]
    ] == [
        ("reading_route", "erdos257_half_story"),
        ("open_proposition", "remaining_open.half_value_membership"),
    ]


def check_witness_carrying_semantic_slices() -> None:
    rank_two = query_corpus.semantic_slice_packet(
        "is rank two worth pursuing", 5
    )
    assert rank_two["query_interpretation"]["operator"]["id"] == "falsify"
    assert [cell["handle"] for cell in rank_two["semantic_cells"]] == [
        "rank2_kill_sound_but_not_shallower_at_cell"
    ]
    rank_cell = rank_two["semantic_cells"][0]
    assert "NOT shallower" in rank_cell["content"]["authored_digest"]["text"]
    assert rank_cell["content"]["formal_witness"]["source_ref"].endswith(
        "LcmConeFlatness.lean:626"
    )
    assert {
        row["plane"] for row in rank_cell["typed_provenance"]
    } == {"kernel", "status", "digestion", "navigation"}
    assert rank_two["operator_synthesis"]["kind"] == (
        "falsification_synthesis"
    )

    half_value = query_corpus.semantic_slice_packet(
        "what should I try next for the half value problem", 5
    )
    assert [cell["handle"] for cell in half_value["semantic_cells"]] == [
        "erdos257_half_story",
        "remaining_open.half_value_membership",
    ]
    open_cell = half_value["semantic_cells"][1]
    assert (
        open_cell["content"]["open_record"]["statement"]
        == "Decide whether 1/2 lies in the Mersenne achievement set. "
        "Yes refutes universal #257; no closes only this route."
    )
    route_cell = half_value["semantic_cells"][0]
    assert "neither half-membership" in (
        route_cell["content"]["programme"]["claim_ceiling"]
    )
    assert {
        row["id"]
        for row in half_value["operator_synthesis"]["exact_open_records"]
    } >= {"remaining_open.half_value_membership"}

    analogy = query_corpus.semantic_slice_packet(
        "compare half carry compactness with the half achievement set route",
        4,
    )
    assert analogy["operator_synthesis"]["formal_bridge_status"] == (
        "not_inferred"
    )
    assert "remaining_open.half_value_membership" in (
        analogy["operator_synthesis"]["shared_open_proposition_ids"]
    )

    support = query_corpus.semantic_slice_packet(
        "which premises let either sharp curvature or exponent only three "
        "transport prove irrationality of the totient series",
        4,
    )
    consumer_names = {
        row["name"]
        for row in support["operator_synthesis"][
            "checked_consumer_signatures"
        ]
    }
    assert {
        "irrational_totientSeries_of_sharpCurvatureSupply",
        "irrational_totient_series_of_exponentOnlyThreeTransportSupply",
    } <= consumer_names
    assert {
        row["tactic"]
        for row in support["operator_synthesis"][
            "lean_application_candidates"
        ]
    } >= {
        "apply Erdos249257.TotientTailPeriodKiller.irrational_totientSeries_of_sharpCurvatureSupply",
        "apply Erdos249257.ExponentOnlyTransport.irrational_totient_series_of_exponentOnlyThreeTransportSupply",
    }
    assert {
        row["id"]
        for row in support["operator_synthesis"]["unproved_requirements"]
    } == {"remaining_open.unbounded_certificate_supply"}

    trace = query_corpus.semantic_slice_packet(
        "why does fixed precision transport fail", 4
    )
    assert [
        row["name"]
        for row in trace["operator_synthesis"][
            "source_dependency_candidates"
        ]
    ] == ["vu_word_has_prefix_locked_completion"]

    module = query_corpus.semantic_slice_packet(
        "where is the module for a direct dyadic curvature certificate", 4
    )
    assert [
        (cell["kind"], cell["handle"]) for cell in module["semantic_cells"]
    ] == [("module", "Erdos249257.CurvatureCarry")]
    assert "Curvature carry for the totient tail" in (
        module["semantic_cells"][0]["content"]["module"]["authored_synopsis"]
    )


def check_elaborated_dependency_witnesses() -> None:
    neighbourhood = query_corpus.formal_dependency_neighbourhood(
        "Erdos249257.TotientTailPeriodKiller."
        "irrational_totientSeries_of_sharpCurvatureSupply"
    )
    assert neighbourhood["availability"] == "available"
    assert {
        row["handle"] for row in neighbourhood["direct_dependencies"]
    } >= {
        "Erdos249257.TotientTailPeriodKiller.SharpCurvatureSupply",
        "Erdos249257.TotientTailPeriodKiller."
        "curvature_notMem_int_of_sharpCurvatureCert",
        "Erdos249257.TotientTailPeriodKiller."
        "rational_totient_series_forces_lcm_cone_flatness",
    }
    assert any(
        path["via"].endswith(
            ".curvature_notMem_int_of_sharpCurvatureCert"
        )
        for path in neighbourhood["two_hop_theorem_paths"]
    )
    assert neighbourhood["authority_posture"].startswith(
        "direct_constant_references_from_elaborated_Lean"
    )
    problem_neighbourhood = query_corpus.formal_dependency_neighbourhood(
        "ErdosProblems.Erdos243.rawNext_gcd_exact_overlap"
    )
    assert problem_neighbourhood["availability"] == "available"
    assert problem_neighbourhood["source_ref"].startswith(
        "ErdosProblems/Erdos243/DynamicCancellation.lean:"
    )
    declaration = query_corpus.declaration_packet(
        "Erdos249257.integerGreedyRemainder_lt_of_get?_eq_false", 1
    )["matches"][0]
    assert declaration["name"] == (
        "integerGreedyRemainder_lt_of_get?_eq_false"
    )
    assert declaration["qualified_name"] == (
        "Erdos249257.integerGreedyRemainder_lt_of_get?_eq_false"
    )


def check_multihop_formal_dependency_reasoning() -> None:
    source = (
        "Erdos249257.TotientTailPeriodKiller."
        "irrational_totientSeries_of_sharpCurvatureSupply"
    )
    target = (
        "Erdos249257.TotientTailPeriodKiller."
        "tail_diff_int_of_den_dvd"
    )
    path = query_corpus.formal_dependency_path(source, target, 8)
    assert path["availability"] == "available"
    assert path["hop_count"] == 3
    assert [node["name"] for node in path["nodes"]] == [
        "irrational_totientSeries_of_sharpCurvatureSupply",
        "rational_totient_series_forces_lcm_cone_flatness",
        "eventual_period_of_not_irrational",
        "tail_diff_int_of_den_dvd",
    ]
    assert all(
        edge["authority"] == "kernel_elaborated_environment"
        and edge["relation"] == "uses_in_elaborated_value"
        for edge in path["edges"]
    )
    cone = query_corpus.formal_dependency_proof_cone(source, 4, 20)
    assert cone["availability"] == "available"
    cone_depths = {
        node["name"]: node["depth"] for node in cone["nodes"]
    }
    assert cone_depths[
        "rational_totient_series_forces_lcm_cone_flatness"
    ] == 1
    assert cone_depths["eventual_period_of_not_irrational"] == 2
    assert cone_depths["tail_diff_int_of_den_dvd"] == 3
    assert cone["omission_receipt"]["reachable_node_count_within_depth"] > (
        cone["omission_receipt"]["emitted_node_count"]
    )
    natural_query = (
        "trace the formal chain from sharp curvature irrationality "
        "to denominator divisibility"
    )
    assert query_corpus.trace_endpoint_queries(natural_query) == [
        "sharp curvature irrationality",
        "denominator divisibility",
    ]
    assert query_corpus.trace_endpoint_queries(
        "why does sharp curvature irrationality ultimately use "
        "denominator divisibility?"
    ) == [
        "sharp curvature irrationality",
        "denominator divisibility",
    ]
    semantic_slice = query_corpus.semantic_slice_packet(natural_query, 20)
    assert {
        (cell["kind"], cell["handle"])
        for cell in semantic_slice["semantic_cells"]
    } == {
        (
            "declaration",
            "irrational_totientSeries_of_sharpCurvatureSupply",
        ),
        ("declaration", "tail_diff_int_of_den_dvd"),
    }
    assert [
        node["name"]
        for node in semantic_slice["operator_synthesis"][
            "formal_dependency_path"
        ]["nodes"]
    ] == [
        "irrational_totientSeries_of_sharpCurvatureSupply",
        "rational_totient_series_forces_lcm_cone_flatness",
        "eventual_period_of_not_irrational",
        "tail_diff_int_of_den_dvd",
    ]


def check_formal_goal_affordance_support() -> None:
    query = (
        "I need to prove totientTail (N + h) - totientTail N is an "
        "integer from a rational totient series; which theorem applies?"
    )
    request = query_corpus.support_goal_request(query)
    assert request == {
        "goal": (
            "totientTail (N + h) - totientTail N is an integer"
        ),
        "context": "a rational totient series",
        "extraction": "ordinary_language_goal_pattern",
    }
    packet = query_corpus.formal_goal_support_packet(query, 3)
    assert packet["availability"] == "available"
    candidate = packet["candidates"][0]
    assert candidate["qualified_name"] == (
        "Erdos249257.TotientTailPeriodKiller."
        "tail_diff_int_of_den_dvd"
    )
    assert candidate["formal_affordance"]["conclusion_head"] == (
        "Membership.mem"
    )
    assert {"Set.range", "Int.cast"} <= set(
        candidate["formal_affordance"]["conclusion_symbols"]
    )
    assert candidate["match_receipt"]["shape_matches"] == [
        "direct_integer_membership"
    ]
    assert {
        "rational",
        "totient",
    } <= set(
        candidate["match_receipt"]["formal_context_symbol_matches"]
    )
    carry_query = (
        "I need to prove totientTail (N + h) - totientTail N is an "
        "integer from a bounded tail carry; which theorem applies?"
    )
    carry_candidate = query_corpus.formal_goal_support_packet(
        carry_query, 3
    )["candidates"][0]
    assert carry_candidate["qualified_name"] == (
        "Erdos249257.tail_diff_mem_int_of_boundedTailCarry"
    )
    assert {"bounded", "carry", "tail"} <= set(
        carry_candidate["match_receipt"][
            "formal_context_symbol_matches"
        ]
    )
    context_free_query = (
        "I need to prove totientTail (N + h) - totientTail N is an "
        "integer; which theorem applies?"
    )
    context_free_candidate = query_corpus.formal_goal_support_packet(
        context_free_query, 3
    )["candidates"][0]
    assert context_free_candidate["qualified_name"] == (
        "Erdos249257.tail_diff_mem_int_of_boundedTailCarry"
    )
    assert context_free_candidate["match_receipt"][
        "formal_context_symbol_matches"
    ] == []
    assert candidate["lean_application_candidate"] == (
        f"apply {candidate['qualified_name']}"
    )
    semantic_slice = query_corpus.semantic_slice_packet(query, 20)
    assert [
        (cell["handle"], cell["selection_reason"])
        for cell in semantic_slice["semantic_cells"]
    ] == [
        (
            candidate["name"],
            "formal_goal_shape_candidate",
        )
    ]
    assert semantic_slice["operator_synthesis"][
        "formal_goal_support"
    ]["candidates"][0]["qualified_name"] == candidate["qualified_name"]
    application = semantic_slice["operator_synthesis"][
        "formal_goal_support"
    ]["application"]
    assert application["application_status"] == (
        "blocked_by_unmatched_proposition_obligations"
    )
    assert [
        row["name"]
        for row in application["obligations"]
        if row["status"] == "unmatched_proposition_obligation"
    ] == ["hdvd"]
    plan = query_corpus.formal_proof_plan_packet(query, 20, 4)
    assert plan["terminal_candidate"]["name"] == (
        "tail_diff_int_of_den_dvd"
    )
    assert plan["plan_status"] == (
        "blocked_by_unmatched_proposition_obligations"
    )
    assert {
        row["name"]
        for row in plan["exact_dependency_spine"]["steps"]
    } >= {
        "two_pow_mul_totient_series_eq",
        "summable_totient_div_two_pow",
    }
    assert plan["dynamic_transition_expansion"] == {
        "runtime_owner": "scripts/proof_state_compiler.py",
        "pilot_command": (
            "python3 scripts/proof_state_compiler.py --pilot-controls"
        ),
        "request_schema": "erdos249257-proof-state-request/1",
        "packet_schema": "erdos249257-proof-state-compilation/1",
        "boundary": (
            "the static proof plan nominates candidates; only the runtime "
            "owner's pinned Lean application receipt can assert that a "
            "candidate produced particular subgoals or closed"
        ),
    }
    curvature_plan = query_corpus.formal_proof_plan_packet(
        "I need to prove Irrational (∑' n : ℕ, "
        "(Nat.totient n : ℝ) / 2 ^ n) from a SharpCurvatureSupply",
        30,
        4,
    )
    assert curvature_plan["terminal_candidate"]["name"] == (
        "irrational_totientSeries_of_sharpCurvatureSupply"
    )
    assert curvature_plan["plan_status"] == (
        "all_proposition_obligations_have_context_matches"
    )
    assert curvature_plan["application"][
        "unmatched_proposition_count"
    ] == 0
    assert {
        row["name"]
        for row in curvature_plan["exact_dependency_spine"]["steps"]
    } >= {
        "curvature_notMem_int_of_sharpCurvatureCert",
        "periodLcm_pos",
        "rational_totient_series_forces_lcm_cone_flatness",
    }
    negation_affordance = query_corpus.lean_dependency_adjacency()[
        "formal_type_affordances"
    ][
        "Erdos249257.ActualForeignResidueProjection."
        "scaleFullTarget_miss_of_abs_sub_le_of_forall_int"
    ]
    assert negation_affordance["conclusion_head"] == "Not"
    assert negation_affordance["forall_binder_count"] == 4
    assert len(negation_affordance["binders"]) == 4
    assert [row["name"] for row in negation_affordance["binders"]] == [
        "H",
        "D",
        "hcontrol",
        "hseparation",
    ]


def check_missing_registered_artifact_is_typed_not_fatal() -> None:
    old_root = query_corpus.ROOT
    with tempfile.TemporaryDirectory(prefix="query-corpus-resilience-") as tmp:
        root = Path(tmp)
        (root / "docs").mkdir()
        descriptor = {
            "identity": {
                "content": {
                    "technical_companion": {
                        "source_path": "paper/missing.tex",
                        "source_content_digest": "sha256:missing",
                        "artifact_role": "authored_companion",
                    }
                }
            }
        }
        (root / "docs/corpus_descriptor.json").write_text(
            json.dumps(descriptor), encoding="utf-8"
        )
        try:
            query_corpus.ROOT = root
            query_corpus.load.cache_clear()
            query_corpus.artifact_inventory.cache_clear()
            inventory = query_corpus.artifact_inventory()
        finally:
            query_corpus.ROOT = old_root
            query_corpus.load.cache_clear()
            query_corpus.artifact_inventory.cache_clear()

    assert inventory == [
        {
            "artifact_id": "technical_companion",
            "artifact_role": "authored_companion",
            "authority_posture": (
                "registered_navigation_artifact_not_proof_authority"
            ),
            "follow": ["--paper-anchor <TeX_label_or_source_ref>"],
            "validation": "python3 scripts/build_corpus_descriptor.py --check",
            "artifact_kind": "authored_paper_source",
            "artifact_handle": "paper/missing.tex",
            "file_path": "paper/missing.tex",
            "fragment": None,
            "content_digest": "sha256:missing",
            "availability": "missing",
            "size_bytes": None,
        }
    ]


def check_unavailable_paper_coordinate_is_typed_not_fatal() -> None:
    coordinate = query_corpus.paper_coordinate("sec:missing", {})
    assert coordinate is not None
    assert coordinate["label"] == "sec:missing"
    assert coordinate["availability"] == "authored_source_unavailable_in_worktree"
    assert coordinate["source_ref"] is None
    packet = query_corpus.paper_label_packet("res:carrycert")
    assert packet["kind"] == "paper_label"
    assert packet["paper"]["label"] == "res:carrycert"
    assert any(
        claim["id"] == "boolean_mobius_carry"
        for claim in packet["attached_claims"]
    )


def main() -> int:
    check_dictionary_budget_and_shape()
    check_vocabulary_mismatch_queries()
    check_witness_carrying_semantic_slices()
    check_elaborated_dependency_witnesses()
    check_multihop_formal_dependency_reasoning()
    check_formal_goal_affordance_support()
    check_missing_registered_artifact_is_typed_not_fatal()
    check_unavailable_paper_coordinate_is_typed_not_fatal()
    print("query corpus semantic-resilience checks: PASS")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
