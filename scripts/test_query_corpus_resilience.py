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


def check_vocabulary_mismatch_queries() -> None:
    assert len(query_corpus.SUPPRESSED_DECLARATION_ATLAS_ROWS) == 12
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
    packet = query_corpus.paper_label_packet("sec:curvature")
    assert packet["kind"] == "paper_label"
    assert packet["paper"]["label"] == "sec:curvature"
    assert any(
        claim["id"] == "transport_curvature_reductions"
        for claim in packet["attached_claims"]
    )


def main() -> int:
    check_dictionary_budget_and_shape()
    check_vocabulary_mismatch_queries()
    check_witness_carrying_semantic_slices()
    check_elaborated_dependency_witnesses()
    check_multihop_formal_dependency_reasoning()
    check_missing_registered_artifact_is_typed_not_fatal()
    check_unavailable_paper_coordinate_is_typed_not_fatal()
    print("query corpus semantic-resilience checks: PASS")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
