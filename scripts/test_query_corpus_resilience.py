#!/usr/bin/env python3
# SPDX-FileCopyrightText: 2026 Will Cook
# SPDX-License-Identifier: Apache-2.0
"""Focused checks for semantic query translation and partial-artifact resilience."""

from __future__ import annotations

import json
import tempfile
from pathlib import Path

import query_corpus


def require(condition: bool, message: str) -> None:
    """Keep resilience checks active when invoked with ``python -O``."""
    if not condition:
        raise AssertionError(message)


def check_dictionary_budget_and_shape() -> None:
    packet = query_corpus.semantic_dictionary_packet()
    encoded = json.dumps(packet, ensure_ascii=False, separators=(",", ":")).encode(
        "utf-8"
    )
    # The dictionary is a first-contact packet, so it stays small enough to read
    # in one pass. The ceiling was 12,000 for a six-problem corpus; #68 and
    # #1041 add their own routes and the packet is now 12.7 KiB. Raised rather
    # than trimmed: dropping routes to fit would make the dictionary silently
    # incomplete, which is the failure the budget exists to prevent.
    require(len(encoded) <= 14_000, "query corpus resilience invariant")
    require({row["id"] for row in packet["operators"]} == {
        "analogy",
        "digest",
        "falsify",
        "frontier",
        "locate",
        "support",
        "trace",
    }, "query corpus resilience invariant")
    require(packet["authority_posture"].endswith(
        "not_proof_or_claim_status_authority"
    ), "query corpus resilience invariant")
    require(packet["schema_version"] == "erdos249257-semantic-dictionary/2", "query corpus resilience invariant")
    discovery = packet["route_discovery_contract"]
    require(discovery["source"].startswith("docs/claims.json::"), "query corpus resilience invariant")
    by_route = {row["route_id"]: row for row in discovery["routes"]}
    require("which paper proofs lack semantic interpretation" in by_route[
        "agent_native_corpus_navigation"
    ]["discovery_terms"], "query corpus resilience invariant")
    require(any(
        row["id"] == "semantic_population_backlog"
        for row in packet["vocabulary"]
    ), "query corpus resilience invariant")


def check_vocabulary_mismatch_queries() -> None:
    require(not query_corpus.SUPPRESSED_DECLARATION_ATLAS_ROWS, "query corpus resilience invariant")
    for comment_word in ("makes", "invariant"):
        try:
            query_corpus.declaration_packet(comment_word, 1)
        except KeyError:
            pass
        else:
            raise AssertionError(
                "comment prose must not be queryable as a declaration"
            )
    require(not any(
        row.get("kind") == "declaration" and row.get("name") == "makes"
        for row in query_corpus.search_packet("makes", 20)["results"]
    ), "query corpus resilience invariant")
    for wrapped_name in (
        "diagonalAdjacentSuffixResidue_powerTwo_oddDepth_central_iff_halfWordBand",
        "HalfTerminalOnlyScaledVanishingSequence.ofCofinalTerminalOnlyStrip",
    ):
        wrapped = query_corpus.declaration_packet(wrapped_name, 1)
        require(wrapped["matches"][0]["name"] == wrapped_name, "query corpus resilience invariant")
    require(query_corpus.search_terms(
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
    }, "query corpus resilience invariant")
    qualified = query_corpus.declaration_packet(
        "Erdos249257.TotientTailPeriodKiller.fixedPrecisionTropicalNoGo",
        1,
    )
    require(qualified["matches"][0]["name"] == "fixedPrecisionTropicalNoGo", "query corpus resilience invariant")
    require(qualified["matches"][0]["qualified_name"] == (
        "Erdos249257.TotientTailPeriodKiller.fixedPrecisionTropicalNoGo"
    ), "query corpus resilience invariant")
    dotted = query_corpus.declaration_packet(
        "BooleanMobiusCarryCertificate.reconstructsSupport",
        1,
    )
    require(dotted["matches"][0]["qualified_name"] == (
        "Erdos249257.BooleanMobiusCarryCertificate.reconstructsSupport"
    ), "query corpus resilience invariant")
    private = query_corpus.declaration_packet("mod_six_cases", 1)
    require(not private["matches"][0]["externally_addressable"], "query corpus resilience invariant")
    private_support = query_corpus.semantic_slice_packet(
        "I need the mod_six_cases theorem",
        4,
    )
    require(not any(
        row["qualified_declaration"].endswith(".mod_six_cases")
        for row in private_support["operator_synthesis"].get(
            "lean_application_candidates", []
        )
    ), "query corpus resilience invariant")
    rank_two = query_corpus.search_packet("is rank two worth pursuing", 5)
    require(rank_two["query_interpretation"]["operator"]["id"] == "falsify", "query corpus resilience invariant")
    require(rank_two["results"][0]["kind"] == "declaration", "query corpus resilience invariant")
    require(rank_two["results"][0]["name"]
        == "rank2_kill_sound_but_not_shallower_at_cell", "query corpus resilience invariant")

    half_value = query_corpus.search_packet(
        "what should I try next for the half value problem", 5
    )
    require(half_value["query_interpretation"]["operator"]["id"] == "frontier", "query corpus resilience invariant")
    require([
        (row["kind"], row.get("id"))
        for row in half_value["results"][:2]
    ] == [
        ("reading_route", "erdos257_half_story"),
        ("open_proposition", "remaining_open.half_value_membership"),
    ], "query corpus resilience invariant")

    one_over_twenty_one = query_corpus.search_packet(
        "what is the exact public status of one over twenty one "
        "and what remains to prove",
        5,
    )
    require(one_over_twenty_one["query_interpretation"]["operator"]["id"] == (
        "frontier"
    ), "query corpus resilience invariant")
    require([
        (row["kind"], row.get("name"))
        for row in one_over_twenty_one["results"][:2]
    ] == [
        ("declaration", "finiteErdosSum_ne_one_div_twenty_one"),
        ("declaration", "exists_two_primitive23_solutions_mul_ten"),
    ], "query corpus resilience invariant")
    require([
        row["node_id"]
        for row in one_over_twenty_one["query_interpretation"][
            "authored_semantic_followups"
        ]
    ] == [
        "Z65::one_over_twenty_one_has_no_finite_support_on_ranks_at_least_two",
        "Z65::primitive_23_cone_has_rank_ten_defect_and_recurrent_multiplicity",
    ], "query corpus resilience invariant")
    fractional_spelling = query_corpus.search_packet(
        "what is the exact public status of 1/21 and what remains to prove",
        5,
    )
    require([
        (row["kind"], row.get("name"))
        for row in fractional_spelling["results"][:2]
    ] == [
        ("declaration", "finiteErdosSum_ne_one_div_twenty_one"),
        ("declaration", "exists_two_primitive23_solutions_mul_ten"),
    ], "query corpus resilience invariant")

    fixed_cut_boundary = query_corpus.semantic_slice_packet(
        "Does the public Erdős 257 release claim that a denominator-21 "
        "saturated transition reduces to a zero-pulse skip followed by a "
        "local pulse at most one, or prove 1/21 membership?",
        4,
    )
    require(fixed_cut_boundary["query_interpretation"]["operator"]["id"] == (
        "frontier"
    ), "query corpus resilience invariant")
    require([
        (cell["kind"], cell["handle"])
        for cell in fixed_cut_boundary["semantic_cells"]
    ] == [
        ("declaration", "finiteErdosSum_ne_one_div_twenty_one"),
        ("declaration", "exists_two_primitive23_solutions_mul_ten"),
        ("claim", "universal_257"),
        (
            "open_proposition",
            "remaining_open.universal_257_all_infinite_supports",
        ),
    ], "query corpus resilience invariant")
    require({
        row["id"]
        for row in fixed_cut_boundary["operator_synthesis"][
            "exact_open_records"
        ]
    } == {"remaining_open.universal_257_all_infinite_supports"}, "query corpus resilience invariant")


def check_witness_carrying_semantic_slices() -> None:
    rank_two = query_corpus.semantic_slice_packet(
        "is rank two worth pursuing", 5
    )
    require(rank_two["query_interpretation"]["operator"]["id"] == "falsify", "query corpus resilience invariant")
    require([cell["handle"] for cell in rank_two["semantic_cells"]] == [
        "rank2_kill_sound_but_not_shallower_at_cell"
    ], "query corpus resilience invariant")
    rank_cell = rank_two["semantic_cells"][0]
    require("NOT shallower" in rank_cell["content"]["authored_digest"]["text"], "query corpus resilience invariant")
    require(rank_cell["content"]["formal_witness"]["source_ref"].endswith(
        "LcmConeFlatness.lean:626"
    ), "query corpus resilience invariant")
    require({
        row["plane"] for row in rank_cell["typed_provenance"]
    } == {"kernel", "status", "digestion", "navigation"}, "query corpus resilience invariant")
    require(rank_two["operator_synthesis"]["kind"] == (
        "falsification_synthesis"
    ), "query corpus resilience invariant")

    half_value = query_corpus.semantic_slice_packet(
        "what should I try next for the half value problem", 5
    )
    require([cell["handle"] for cell in half_value["semantic_cells"]] == [
        "erdos257_half_story",
        "remaining_open.half_value_membership",
    ], "query corpus resilience invariant")
    open_cell = half_value["semantic_cells"][1]
    require(open_cell["content"]["open_record"]["statement"]
        == "Decide whether 1/2 lies in the Mersenne achievement set. "
        "Yes refutes universal #257; no closes only this route.", "query corpus resilience invariant")
    route_cell = half_value["semantic_cells"][0]
    require("neither target membership" in (
        route_cell["content"]["programme"]["claim_ceiling"]
    ), "query corpus resilience invariant")
    require({
        row["id"]
        for row in half_value["operator_synthesis"]["exact_open_records"]
    } >= {"remaining_open.half_value_membership"}, "query corpus resilience invariant")

    one_over_twenty_one = query_corpus.semantic_slice_packet(
        "what is the exact public status of one over twenty one "
        "and what remains to prove",
        5,
    )
    require([
        cell["handle"]
        for cell in one_over_twenty_one["semantic_cells"][:2]
    ] == [
        "finiteErdosSum_ne_one_div_twenty_one",
        "exists_two_primitive23_solutions_mul_ten",
    ], "query corpus resilience invariant")
    finite_obstruction = one_over_twenty_one["semantic_cells"][0]
    # Same consequence, restated by the source-fidelity pass: the theorem rules
    # finite support out rather than asserting infinite support outright.
    require("rules out finite support" in (
        finite_obstruction["content"]["authored_digest"]["text"]
    ), "query corpus resilience invariant")
    multiplicity_obstruction = one_over_twenty_one["semantic_cells"][1]
    require(multiplicity_obstruction["content"]["formal_witness"]["name"] == (
        "exists_two_primitive23_solutions_mul_ten"
    ), "query corpus resilience invariant")

    analogy = query_corpus.semantic_slice_packet(
        "compare half carry compactness with the half achievement set route",
        4,
    )
    require(analogy["operator_synthesis"]["formal_bridge_status"] == (
        "not_inferred"
    ), "query corpus resilience invariant")
    require("remaining_open.half_value_membership" in (
        analogy["operator_synthesis"]["shared_open_proposition_ids"]
    ), "query corpus resilience invariant")

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
    require({
        "irrational_totientSeries_of_sharpCurvatureSupply",
        "irrational_totient_series_of_exponentOnlyThreeTransportSupply",
    } <= consumer_names, "query corpus resilience invariant")
    require({
        row["tactic"]
        for row in support["operator_synthesis"][
            "lean_application_candidates"
        ]
    } >= {
        "apply Erdos249257.TotientTailPeriodKiller.irrational_totientSeries_of_sharpCurvatureSupply",
        "apply Erdos249257.ExponentOnlyTransport.irrational_totient_series_of_exponentOnlyThreeTransportSupply",
    }, "query corpus resilience invariant")
    require({
        row["id"]
        for row in support["operator_synthesis"]["unproved_requirements"]
    } == {"remaining_open.unbounded_certificate_supply"}, "query corpus resilience invariant")

    trace = query_corpus.semantic_slice_packet(
        "why does fixed precision transport fail", 4
    )
    require([
        row["name"]
        for row in trace["operator_synthesis"][
            "source_dependency_candidates"
        ]
    ] == ["vu_word_has_prefix_locked_completion"], "query corpus resilience invariant")

    module = query_corpus.semantic_slice_packet(
        "where is the module for a direct dyadic curvature certificate", 4
    )
    require([
        (cell["kind"], cell["handle"]) for cell in module["semantic_cells"]
    ] == [("module", "Erdos249257.CurvatureCarry")], "query corpus resilience invariant")
    require("Curvature carry for the totient tail" in (
        module["semantic_cells"][0]["content"]["module"]["authored_synopsis"]
    ), "query corpus resilience invariant")


def check_elaborated_dependency_witnesses() -> None:
    # These handles are namespace-qualified, not module-qualified, so they
    # survive a declaration moving between files: the specimen below now lives
    # in Erdos249257/CurvatureCarry.lean rather than TotientTailPeriodKiller
    # .lean, while the Erdos249257.TotientTailPeriodKiller namespace is
    # unchanged. Keep the assertions unconditional -- a committed
    # docs/lean_dependency_index.json older than the Lean tree makes every
    # neighbourhood report itself unavailable, and that is a repository defect
    # the build job fails on, not a state this check should tolerate.
    neighbourhood = query_corpus.formal_dependency_neighbourhood(
        "Erdos249257.TotientTailPeriodKiller."
        "irrational_totientSeries_of_sharpCurvatureSupply"
    )
    require(neighbourhood["availability"] == "available", "query corpus resilience invariant")
    require({
        row["handle"] for row in neighbourhood["direct_dependencies"]
    } >= {
        "Erdos249257.TotientTailPeriodKiller.SharpCurvatureSupply",
        "Erdos249257.TotientTailPeriodKiller."
        "curvature_notMem_int_of_sharpCurvatureCert",
        "Erdos249257.TotientTailPeriodKiller."
        "rational_totient_series_forces_lcm_cone_flatness",
    }, "query corpus resilience invariant")
    require(any(
        path["via"].endswith(
            ".curvature_notMem_int_of_sharpCurvatureCert"
        )
        for path in neighbourhood["two_hop_theorem_paths"]
    ), "query corpus resilience invariant")
    require(neighbourhood["authority_posture"].startswith(
        "direct_constant_references_from_elaborated_Lean"
    ), "query corpus resilience invariant")
    problem_neighbourhood = query_corpus.formal_dependency_neighbourhood(
        "ErdosProblems.Erdos243.rawNext_gcd_exact_overlap"
    )
    require(problem_neighbourhood["availability"] == "available", "query corpus resilience invariant")
    require(problem_neighbourhood["source_ref"].startswith(
        "ErdosProblems/Erdos243/DynamicCancellation.lean:"
    ), "query corpus resilience invariant")
    declaration = query_corpus.declaration_packet(
        "Erdos249257.integerGreedyRemainder_lt_of_get?_eq_false", 1
    )["matches"][0]
    require(declaration["name"] == (
        "integerGreedyRemainder_lt_of_get?_eq_false"
    ), "query corpus resilience invariant")
    require(declaration["qualified_name"] == (
        "Erdos249257.integerGreedyRemainder_lt_of_get?_eq_false"
    ), "query corpus resilience invariant")


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
    require(path["availability"] == "available", "query corpus resilience invariant")
    require(path["hop_count"] == 3, "query corpus resilience invariant")
    require([node["name"] for node in path["nodes"]] == [
        "irrational_totientSeries_of_sharpCurvatureSupply",
        "rational_totient_series_forces_lcm_cone_flatness",
        "eventual_period_of_not_irrational",
        "tail_diff_int_of_den_dvd",
    ], "query corpus resilience invariant")
    require(all(
        edge["authority"] == "kernel_elaborated_environment"
        and edge["relation"] == "uses_in_elaborated_value"
        for edge in path["edges"]
    ), "query corpus resilience invariant")
    cone = query_corpus.formal_dependency_proof_cone(source, 4, 20)
    require(cone["availability"] == "available", "query corpus resilience invariant")
    cone_depths = {
        node["name"]: node["depth"] for node in cone["nodes"]
    }
    require(cone_depths[
        "rational_totient_series_forces_lcm_cone_flatness"
    ] == 1, "query corpus resilience invariant")
    require(cone_depths["eventual_period_of_not_irrational"] == 2, "query corpus resilience invariant")
    require(cone_depths["tail_diff_int_of_den_dvd"] == 3, "query corpus resilience invariant")
    require(cone["omission_receipt"]["reachable_node_count_within_depth"] > (
        cone["omission_receipt"]["emitted_node_count"]
    ), "query corpus resilience invariant")
    natural_query = (
        "trace the formal chain from sharp curvature irrationality "
        "to denominator divisibility"
    )
    require(query_corpus.trace_endpoint_queries(natural_query) == [
        "sharp curvature irrationality",
        "denominator divisibility",
    ], "query corpus resilience invariant")
    require(query_corpus.trace_endpoint_queries(
        "why does sharp curvature irrationality ultimately use "
        "denominator divisibility?"
    ) == [
        "sharp curvature irrationality",
        "denominator divisibility",
    ], "query corpus resilience invariant")
    semantic_slice = query_corpus.semantic_slice_packet(natural_query, 20)
    require({
        (cell["kind"], cell["handle"])
        for cell in semantic_slice["semantic_cells"]
    } == {
        (
            "declaration",
            "irrational_totientSeries_of_sharpCurvatureSupply",
        ),
        ("declaration", "tail_diff_int_of_den_dvd"),
    }, "query corpus resilience invariant")
    require([
        node["name"]
        for node in semantic_slice["operator_synthesis"][
            "formal_dependency_path"
        ]["nodes"]
    ] == [
        "irrational_totientSeries_of_sharpCurvatureSupply",
        "rational_totient_series_forces_lcm_cone_flatness",
        "eventual_period_of_not_irrational",
        "tail_diff_int_of_den_dvd",
    ], "query corpus resilience invariant")


def check_formal_goal_affordance_support() -> None:
    query = (
        "I need to prove totientTail (N + h) - totientTail N is an "
        "integer from a rational totient series; which theorem applies?"
    )
    request = query_corpus.support_goal_request(query)
    require(request == {
        "goal": (
            "totientTail (N + h) - totientTail N is an integer"
        ),
        "context": "a rational totient series",
        "extraction": "ordinary_language_goal_pattern",
    }, "query corpus resilience invariant")
    packet = query_corpus.formal_goal_support_packet(query, 3)
    require(packet["availability"] == "available", "query corpus resilience invariant")
    candidate = packet["candidates"][0]
    require(candidate["qualified_name"] == (
        "Erdos249257.TotientTailPeriodKiller."
        "tail_diff_int_of_den_dvd"
    ), "query corpus resilience invariant")
    require(candidate["formal_affordance"]["conclusion_head"] == (
        "Membership.mem"
    ), "query corpus resilience invariant")
    require({"Set.range", "Int.cast"} <= set(
        candidate["formal_affordance"]["conclusion_symbols"]
    ), "query corpus resilience invariant")
    require(candidate["match_receipt"]["shape_matches"] == [
        "direct_integer_membership"
    ], "query corpus resilience invariant")
    require({
        "rational",
        "totient",
    } <= set(
        candidate["match_receipt"]["formal_context_symbol_matches"]
    ), "query corpus resilience invariant")
    carry_query = (
        "I need to prove totientTail (N + h) - totientTail N is an "
        "integer from a bounded tail carry; which theorem applies?"
    )
    carry_candidate = query_corpus.formal_goal_support_packet(
        carry_query, 3
    )["candidates"][0]
    require(carry_candidate["qualified_name"] == (
        "Erdos249257.tail_diff_mem_int_of_boundedTailCarry"
    ), "query corpus resilience invariant")
    require({"bounded", "carry", "tail"} <= set(
        carry_candidate["match_receipt"][
            "formal_context_symbol_matches"
        ]
    ), "query corpus resilience invariant")
    context_free_query = (
        "I need to prove totientTail (N + h) - totientTail N is an "
        "integer; which theorem applies?"
    )
    context_free_candidate = query_corpus.formal_goal_support_packet(
        context_free_query, 3
    )["candidates"][0]
    require(context_free_candidate["qualified_name"] == (
        "Erdos249257.tail_diff_mem_int_of_boundedTailCarry"
    ), "query corpus resilience invariant")
    require(context_free_candidate["match_receipt"][
        "formal_context_symbol_matches"
    ] == [], "query corpus resilience invariant")
    require(candidate["lean_application_candidate"] == (
        f"apply {candidate['qualified_name']}"
    ), "query corpus resilience invariant")
    semantic_slice = query_corpus.semantic_slice_packet(query, 20)
    require([
        (cell["handle"], cell["selection_reason"])
        for cell in semantic_slice["semantic_cells"]
    ] == [
        (
            candidate["name"],
            "formal_goal_shape_candidate",
        )
    ], "query corpus resilience invariant")
    require(semantic_slice["operator_synthesis"][
        "formal_goal_support"
    ]["candidates"][0]["qualified_name"] == candidate["qualified_name"], "query corpus resilience invariant")
    application = semantic_slice["operator_synthesis"][
        "formal_goal_support"
    ]["application"]
    require(application["application_status"] == (
        "blocked_by_unmatched_proposition_obligations"
    ), "query corpus resilience invariant")
    require([
        row["name"]
        for row in application["obligations"]
        if row["status"] == "unmatched_proposition_obligation"
    ] == ["hdvd"], "query corpus resilience invariant")
    plan = query_corpus.formal_proof_plan_packet(query, 20, 4)
    require(plan["terminal_candidate"]["name"] == (
        "tail_diff_int_of_den_dvd"
    ), "query corpus resilience invariant")
    require(plan["plan_status"] == (
        "blocked_by_unmatched_proposition_obligations"
    ), "query corpus resilience invariant")
    require({
        row["name"]
        for row in plan["exact_dependency_spine"]["steps"]
    } >= {
        "two_pow_mul_totient_series_eq",
        "summable_totient_div_two_pow",
    }, "query corpus resilience invariant")
    require(plan["dynamic_transition_expansion"] == {
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
    }, "query corpus resilience invariant")
    curvature_plan = query_corpus.formal_proof_plan_packet(
        "I need to prove Irrational (∑' n : ℕ, "
        "(Nat.totient n : ℝ) / 2 ^ n) from a SharpCurvatureSupply",
        30,
        4,
    )
    require(curvature_plan["terminal_candidate"]["name"] == (
        "irrational_totientSeries_of_sharpCurvatureSupply"
    ), "query corpus resilience invariant")
    require(curvature_plan["plan_status"] == (
        "all_proposition_obligations_have_context_matches"
    ), "query corpus resilience invariant")
    require(curvature_plan["application"][
        "unmatched_proposition_count"
    ] == 0, "query corpus resilience invariant")
    require({
        row["name"]
        for row in curvature_plan["exact_dependency_spine"]["steps"]
    } >= {
        "curvature_notMem_int_of_sharpCurvatureCert",
        "periodLcm_pos",
        "rational_totient_series_forces_lcm_cone_flatness",
    }, "query corpus resilience invariant")
    negation_affordance = query_corpus.lean_dependency_adjacency()[
        "formal_type_affordances"
    ][
        "Erdos249257.ActualForeignResidueProjection."
        "scaleFullTarget_miss_of_abs_sub_le_of_forall_int"
    ]
    require(negation_affordance["conclusion_head"] == "Not", "query corpus resilience invariant")
    require(negation_affordance["forall_binder_count"] == 4, "query corpus resilience invariant")
    require(len(negation_affordance["binders"]) == 4, "query corpus resilience invariant")
    require([row["name"] for row in negation_affordance["binders"]] == [
        "H",
        "D",
        "hcontrol",
        "hseparation",
    ], "query corpus resilience invariant")


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

    require(inventory == [
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
    ], "query corpus resilience invariant")


def check_unavailable_paper_coordinate_is_typed_not_fatal() -> None:
    coordinate = query_corpus.paper_coordinate("sec:missing", {})
    require(coordinate is not None, "query corpus resilience invariant")
    require(coordinate["label"] == "sec:missing", "query corpus resilience invariant")
    require(coordinate["availability"] == "authored_source_unavailable_in_worktree", "query corpus resilience invariant")
    require(coordinate["source_ref"] is None, "query corpus resilience invariant")
    packet = query_corpus.paper_label_packet("res:carrycert")
    require(packet["kind"] == "paper_label", "query corpus resilience invariant")
    require(packet["paper"]["label"] == "res:carrycert", "query corpus resilience invariant")
    require(any(
        claim["id"] == "boolean_mobius_carry"
        for claim in packet["attached_claims"]
    ), "query corpus resilience invariant")


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
