#!/usr/bin/env python3
# SPDX-FileCopyrightText: 2026 Will Cook
# SPDX-License-Identifier: Apache-2.0

from copy import deepcopy
from unittest.mock import patch

import query_semantic
from query_semantic import (
    BUDGET,
    PROBLEMS,
    build_family_relations_packet,
    cmd_problem_registry,
    is_authored_interpretation,
    is_structural_interpretation,
    load_claims,
    load_palomar,
    main,
    encoded_json_bytes,
    problem_for_route,
    problem_scope_matches,
)


def test_authored_tier_is_not_inferred_from_statement_node_presence() -> None:
    structural = {
        "statement_node": "structural::abc",
        "interpretation_tier": "source_structural_family",
    }
    assert not is_authored_interpretation(structural)
    assert is_structural_interpretation(structural)


def test_authored_tier_is_explicit() -> None:
    authored = {
        "statement_node": "Z40::material_statement",
        "interpretation_tier": "authored_statement",
    }
    assert is_authored_interpretation(authored)
    assert not is_structural_interpretation(authored)


def test_zone_only_role_is_neither_interpretation_tier() -> None:
    role = {"zone": "Z40", "role": "substrate"}
    assert not is_authored_interpretation(role)
    assert not is_structural_interpretation(role)


def test_problem_registry_is_loaded_from_the_public_problem_index() -> None:
    assert PROBLEMS == ("68", "243", "249", "251", "257", "269", "1041", "1049")


def test_problem_registry_exposes_route_memory_resume_command() -> None:
    captured: dict = {}

    def capture(payload: object) -> int:
        captured["payload"] = payload
        return 0

    class Args:
        problem = None

    with patch("query_semantic.emit", side_effect=capture):
        result = cmd_problem_registry(
            {
                "declaration_roles": [],
                "zones": [],
                "statement_nodes": [],
                "summary": {"per_problem": {}},
            },
            Args(),
        )
    if result != 0:
        raise AssertionError(f"problem registry returned {result}")

    if "payload" not in captured:
        raise AssertionError("problem registry did not emit a packet")
    rows = captured["payload"]["problems"]
    if [row["erdos_number"] for row in rows] != [
        int(problem) for problem in PROBLEMS
    ]:
        raise AssertionError("problem registry selector coverage drifted")
    for row in rows:
        expected = (
            "python3 scripts/query_route_memory.py --problem "
            f"{row['erdos_number']}"
        )
        if row["follow"].get("route_memory") != expected:
            raise AssertionError("problem registry route-memory handoff drifted")


def test_historical_both_scope_does_not_leak_into_every_problem() -> None:
    assert problem_scope_matches("both", "249")
    assert problem_scope_matches("both", "257")
    assert not problem_scope_matches("both", "243")


def test_problem_route_prefers_authored_node_then_zone_then_exact_namespace() -> None:
    corpus = {
        "statement_nodes": [{"id": "Z90::node", "problem": "269"}],
        "zones": [{"zone_id": "Z91", "problem": "251"}],
    }
    assert problem_for_route(
        corpus,
        {
            "statement_node": "Z90::node",
            "zone": "Z91",
            "module": "ErdosProblems/Erdos243/Foo.lean",
        },
    ) == "243"
    assert problem_for_route(
        corpus,
        {
            "statement_node": "Z90::node",
            "zone": "Z91",
            "module": "Erdos249257/Foo.lean",
        },
    ) == "251"
    assert problem_for_route(
        corpus,
        {"statement_node": "Z90::node", "module": "Erdos249257/Foo.lean"},
    ) == "269"
    assert problem_for_route(
        corpus,
        {"module": "ErdosProblems/Erdos9999/Future.lean"},
    ) == "9999"


def test_palomar_relations_expose_249_peers_and_exact_boundaries() -> None:
    packet = build_family_relations_packet(
        load_palomar(), load_claims(), "first_harmonic_pivot_decomposition"
    )
    assert packet["family"]["source_route"] == "Erdos249257/FirstHarmonicPivot.lean"
    assert packet["family"]["source_declaration"] == (
        "Erdos249257.TotientTailPeriodKiller."
        "irrational_totient_series_of_pivotResidualDecorrelation"
    )
    assert "PivotBudgetAt" in packet["family"]["open_boundary"]
    stronger = [
        row
        for row in packet["relations"]
        if row["authority_rank_relation"] == "stronger_peer"
        if row["peer"]["family_id"] == "actual_lcm_orbit_separation"
    ]
    assert len(stronger) == 1
    assert stronger[0]["relation_class"] == "conditional_peer"
    assert stronger[0]["peer"]["source_route"] == (
        "Erdos249257/TotientActualLcmOrbitSeparation.lean"
    )
    assert "cofinal" in stronger[0]["peer"]["open_boundary"]
    actual_sources = {
        row["source_file"]: row
        for row in stronger[0]["peer"]["source_evidence"]
    }
    assert actual_sources[
        "Erdos249257/TotientActualLcmOrbitSeparation.lean"
    ]["source_anchor"] == "305"
    assert actual_sources[
        "Erdos249257/TotientActualLcmOrbitSign.lean"
    ]["source_anchor"] == "31-278"
    primary_index = stronger[0]["peer"]["primary_source_evidence_index"]
    assert stronger[0]["peer"]["source_evidence"][primary_index] == actual_sources[
        "Erdos249257/TotientActualLcmOrbitSeparation.lean"
    ]

    contrary = build_family_relations_packet(
        load_palomar(), load_claims(), "fixed_precision_transport_no_go"
    )
    weaker = [
        row
        for row in contrary["relations"]
        if row["authority_rank_relation"] == "weaker_peer"
        if row["peer"]["family_id"] == "actual_foreign_residue_projection"
    ]
    assert len(weaker) == 1
    assert weaker[0]["relation_class"] == "contrary_evidence"
    assert contrary["contrary_evidence_edges"] == [
        {
            "relation": "contrary_evidence_for",
            "relation_class": "contrary_evidence",
            "direction": "outgoing",
            "peer_family_id": "actual_foreign_residue_projection",
            "authority_rank_relation": "weaker_peer",
        }
    ]
    assert contrary["family"]["source_declaration"].endswith(
        "fixedPrecisionTropicalNoGo; "
        "Erdos249257.TotientTailPeriodKiller.vu_step_has_centred_completion; "
        "Erdos249257.TotientTailPeriodKiller.vu_word_has_prefix_locked_completion"
    )
    assert "finite-word" in contrary["family"]["open_boundary"]
    assert all(
        ";" not in command for command in contrary["follow"]["declarations"]
    )
    assert contrary["follow"]["problem_route"].endswith("erdos_249")


def test_support_relation_is_not_misclassified_as_prerequisite() -> None:
    packet = build_family_relations_packet(
        load_palomar(), load_claims(), "factorial_carry_characterisation"
    )
    support = next(
        row
        for row in packet["support_edges"]
        if row["peer_family_id"] == "factorial_channel_and_projection_rigidity"
    )
    assert support["relation"] == "supports_without_producing"
    assert support["relation_class"] == "support"
    assert packet["prerequisite_edges"] == []


def test_relation_only_family_remains_queryable_without_invented_rank() -> None:
    packet = build_family_relations_packet(
        load_palomar(), load_claims(), "totient_certificate_equivalences"
    )
    assert packet["family"]["authority_rank"] == {
        "status": "relation_family_not_in_programme_family_order",
        "programme_position": None,
        "basis": (
            "docs/PALOMAR_RESULT_SHOWCASE.json::selection_contract."
            "programme_family_order"
        ),
    }
    assert packet["family"]["problem"] == 249
    assert packet["relations"][0]["peer"]["family_id"] == (
        "strict_prime_tail_orbit_gap"
    )
    assert packet["relations"][0]["authority_rank_relation"] == (
        "not_comparable_unranked_family"
    )
    assert packet["family"]["source_evidence_status"] == (
        "review_metadata_only_no_exact_source_coordinate"
    )
    assert "does not infer a source" in packet["family"][
        "source_authority_boundary"
    ]
    assert packet["family"]["mechanism_status"] == (
        "not_separately_authored_in_current_authority"
    )
    assert packet["follow"]["declarations"] == []


def test_claims_main_result_supplies_exact_source_when_palomar_has_no_source_row() -> None:
    packet = build_family_relations_packet(
        load_palomar(), load_claims(), "bounded_negative_exclusion"
    )
    family = packet["family"]
    assert family["source_evidence_status"] == "exact_claims_main_result_rows"
    assert family["source_route"] == (
        "ErdosProblems/Erdos243/ReciprocalTailRigidity.lean"
    )
    assert family["source_declaration"] == (
        "ErdosProblems.Erdos243."
        "no_cofinallyBoundedNegative_of_normalizedVanishes"
    )
    assert family["source_evidence"][0]["source_kind"] == "claims_main_result"
    assert family["source_evidence"][0]["hypothesis_projection_status"] == (
        "statement_and_declaration_only_no_separate_hypothesis_list"
    )
    assert family["source_evidence_authorities"] == [
        "docs/claims.json::external_verification_packet.main_results"
    ]
    assert packet["follow"]["declarations"] == sorted(
        packet["follow"]["declarations"]
    )
    assert any(
        command.endswith(
            "ErdosProblems.Erdos243."
            "no_cofinallyBoundedNegative_of_normalizedVanishes"
        )
        for command in packet["follow"]["declarations"]
    )


def test_every_canonical_family_packet_is_bounded_and_boundary_honest() -> None:
    palomar = load_palomar()
    claims = load_claims()
    programme_ids = {
        str(family_id)
        for row in palomar["selection_contract"]["programme_family_order"]
        for family_id in row["family_ids"]
    }
    relation_ids = {
        str(family_id)
        for row in palomar["selection_contract"]["family_relations"]
        for family_id in (row["from_family_id"], row["to_family_id"])
    }
    for family_id in sorted(programme_ids | relation_ids):
        packet = build_family_relations_packet(palomar, claims, family_id)
        family = packet["family"]
        assert family["open_boundary"]
        assert family["mechanism_status"] in {
            "authored_source_mechanism",
            "ranked_mechanism_judgement",
            "not_separately_authored_in_current_authority",
        }
        assert family["source_evidence_status"] in {
            "exact_palomar_source_rows",
            "exact_claims_main_result_rows",
            "formal_declarations_only_no_exact_source_coordinate",
            "review_metadata_only_no_exact_source_coordinate",
        }
        if family["source_evidence"]:
            assert all(
                row["source_file"] or row["source_declaration"]
                for row in family["source_evidence"]
            )
        else:
            assert family["source_authority_boundary"]
        assert encoded_json_bytes(packet) <= BUDGET


def test_family_query_resolves_only_the_selected_relation_neighbourhood() -> None:
    palomar = load_palomar()
    claims = load_claims()
    family_id = "first_harmonic_pivot_decomposition"
    required = {family_id}
    for row in palomar["selection_contract"]["family_relations"]:
        endpoints = {str(row["from_family_id"]), str(row["to_family_id"])}
        if family_id in endpoints:
            required.update(endpoints)
    resolved: list[str] = []
    original = query_semantic._family_details

    def capture(key: str, *args, **kwargs) -> dict:
        resolved.append(key)
        return original(key, *args, **kwargs)

    with patch("query_semantic._family_details", side_effect=capture):
        build_family_relations_packet(palomar, claims, family_id)
    assert set(resolved) == required
    assert len(resolved) == len(required)


def test_family_relations_project_claim_status_without_inventing_a_rank() -> None:
    packet = build_family_relations_packet(
        load_palomar(), load_claims(), "conditional_carry_escape"
    )
    family = packet["family"]
    assert family["proof_status"] == (
        "conditional no-go consumer; novelty and significance unassessed"
    )
    assert family["proof_status_authority"].endswith(
        "families[].contribution_class"
    )
    weighted = next(
        row for row in packet["relations"]
        if row["peer"]["family_id"] == "weighted_phase_carry_observer"
    )
    assert weighted["peer"]["proof_status"] == (
        "locally proved result; novelty unassessed"
    )


def test_palomar_relation_and_detail_array_order_cannot_change_authority_rank() -> None:
    palomar = {
        "selection_contract": {
            "programme_family_order": [
                {
                    "problem": 249,
                    "family_ids": ["actual_lcm", "first_harmonic", "fixed", "foreign"],
                },
                {"problem": 257, "family_ids": ["cross_support"]},
            ],
            "family_relations": [
                {
                    "from_family_id": "first_harmonic",
                    "relation": "independent_conditional_endpoint_peer",
                    "to_family_id": "actual_lcm",
                    "reason": "independent endpoint consumers",
                },
                {
                    "from_family_id": "fixed",
                    "relation": "contrary_evidence_for",
                    "to_family_id": "foreign",
                    "reason": "fixed precision does not close global projection",
                },
                {
                    "from_family_id": "cross_support",
                    "relation": "supports_without_producing",
                    "to_family_id": "first_harmonic",
                    "reason": "cross-programme support does not define value order",
                },
            ],
        },
        "candidate_ranking": [
            {
                "rank": 2,
                "family_id": "first_harmonic",
                "declaration": "External.first_harmonic",
                "mechanism_depth_and_natural_friction": "ranked first harmonic mechanism",
            },
            {
                "rank": 1,
                "family_id": "actual_lcm",
                "declaration": "External.actual_lcm",
                "mechanism_depth_and_natural_friction": "ranked actual LCM mechanism",
            },
        ],
        "candidate_value_dispositions": {
            "source_landscape_candidates": [
                {
                    "family_id": "actual_lcm",
                    "candidate_id": "actual_lcm",
                    "comparator_declaration": "External.actual_lcm",
                    "source_declaration": "Source.actual_lcm",
                    "source_file": "Erdos249257/ActualLcm.lean",
                    "source_anchor": "42",
                    "hard_mechanism": "actual LCM mechanism",
                },
                {
                    "family_id": "actual_lcm",
                    "candidate_id": "actual_lcm_sign_support",
                    "source_declaration": "Source.actual_lcm_sign",
                    "source_file": "Erdos249257/ActualLcmSign.lean",
                    "source_anchor": "9-12",
                    "hard_mechanism": "actual LCM sign boundary",
                },
                {
                    "family_id": "first_harmonic",
                    "candidate_id": "first_harmonic",
                    "comparator_declaration": "External.first_harmonic",
                    "source_declaration": "Source.first_harmonic",
                    "source_file": "Erdos249257/FirstHarmonic.lean",
                    "source_anchor": "100",
                    "hard_mechanism": "first harmonic mechanism",
                },
                {
                    "family_id": "fixed",
                    "source_declaration": "Source.fixed",
                    "source_file": "Erdos249257/Fixed.lean",
                    "hard_mechanism": "fixed precision mechanism",
                },
                {
                    "family_id": "foreign",
                    "source_declaration": "Source.foreign",
                    "source_file": "Erdos249257/Foreign.lean",
                    "hard_mechanism": "foreign projection mechanism",
                },
            ]
        },
    }
    claims = {
        "external_verification_packet": {
            "review_matrix": [
                {
                    "problem": 249,
                    "families": [
                        {
                            "id": family_id,
                            "summary": f"{family_id} summary",
                            "boundary": f"{family_id} boundary",
                            "contribution_class": f"{family_id} class",
                            "evidence_mode": "fixture",
                            "declarations": [f"Source.{family_id}"],
                        }
                        for family_id in ["actual_lcm", "first_harmonic", "fixed", "foreign"]
                    ]
                },
                {
                    "problem": 257,
                    "families": [
                        {
                            "id": "cross_support",
                            "summary": "cross summary",
                            "boundary": "cross boundary",
                            "contribution_class": "cross class",
                            "evidence_mode": "fixture",
                            "declarations": ["Source.cross_support"],
                        }
                    ],
                },
            ]
        }
    }
    reversed_source = deepcopy(palomar)
    reversed_source["selection_contract"]["programme_family_order"].reverse()
    reversed_source["selection_contract"]["family_relations"].reverse()
    reversed_source["candidate_ranking"].reverse()
    reversed_source["candidate_value_dispositions"][
        "source_landscape_candidates"
    ].reverse()
    reversed_claims = deepcopy(claims)
    reversed_claims["external_verification_packet"]["review_matrix"].reverse()
    for block in reversed_claims["external_verification_packet"]["review_matrix"]:
        block["families"].reverse()

    normal = build_family_relations_packet(palomar, claims, "first_harmonic")
    reversed_packet = build_family_relations_packet(
        reversed_source, reversed_claims, "first_harmonic"
    )
    assert normal == reversed_packet
    assert normal["family"]["authority_rank"]["programme_position"] == 2
    assert "global_position" not in normal["family"]["authority_rank"]
    assert normal["stronger_peers"][0]["peer_family_id"] == "actual_lcm"
    cross = next(
        row for row in normal["relations"]
        if row["peer"]["family_id"] == "cross_support"
    )
    assert cross["authority_rank_relation"] == "not_comparable_cross_programme"
    actual = next(
        row["peer"]
        for row in normal["relations"]
        if row["peer"]["family_id"] == "actual_lcm"
    )
    primary = actual["source_evidence"][actual["primary_source_evidence_index"]]
    assert primary["source_file"] == "Erdos249257/ActualLcm.lean"
    assert primary["source_anchor"] == "42"
    assert normal["family"]["presentation_disposition"] == reversed_packet[
        "family"
    ]["presentation_disposition"]


def test_family_relations_does_not_load_unrelated_semantic_corpus() -> None:
    palomar = {
        "selection_contract": {
            "programme_family_order": [
                {"problem": 249, "family_ids": ["solo"]}
            ],
            "family_relations": [],
        },
        "candidate_ranking": [],
        "candidate_value_dispositions": {"source_landscape_candidates": []},
    }
    claims = {
        "external_verification_packet": {
            "review_matrix": [
                {
                    "problem": 249,
                    "families": [
                        {
                            "id": "solo",
                            "summary": "solo summary",
                            "boundary": "solo boundary",
                            "contribution_class": "fixture",
                            "evidence_mode": "fixture",
                            "declarations": ["Source.solo"],
                        }
                    ],
                }
            ]
        }
    }
    captured: dict = {}

    def capture(payload: object) -> int:
        captured["payload"] = payload
        return 0

    with (
        patch("sys.argv", ["query_semantic.py", "family-relations", "solo"]),
        patch("query_semantic.load", side_effect=AssertionError("must not load")),
        patch("query_semantic.load_palomar", return_value=palomar),
        patch("query_semantic.load_claims", return_value=claims),
        patch("query_semantic.emit", side_effect=capture),
    ):
        assert main() == 0
    assert captured["payload"]["family"]["family_id"] == "solo"


if __name__ == "__main__":
    tests = [
        value
        for name, value in sorted(globals().items())
        if name.startswith("test_") and callable(value)
    ]
    for test in tests:
        test()
    print(f"query semantic tier tests: {len(tests)} passed")
