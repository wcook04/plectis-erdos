#!/usr/bin/env python3
# SPDX-FileCopyrightText: 2026 Will Cook
# SPDX-License-Identifier: Apache-2.0

from copy import deepcopy
from unittest.mock import patch

from query_semantic import (
    PROBLEMS,
    build_family_relations_packet,
    cmd_problem_registry,
    is_authored_interpretation,
    is_structural_interpretation,
    load_claims,
    load_palomar,
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
        for row in packet["stronger_peers"]
        if row["peer"]["family_id"] == "actual_lcm_orbit_separation"
    ]
    assert len(stronger) == 1
    assert stronger[0]["relation_class"] == "conditional_peer"
    assert stronger[0]["peer"]["source_route"] == (
        "Erdos249257/TotientActualLcmOrbitSeparation.lean"
    )
    assert "cofinal" in stronger[0]["peer"]["open_boundary"]

    contrary = build_family_relations_packet(
        load_palomar(), load_claims(), "fixed_precision_transport_no_go"
    )
    weaker = [
        row
        for row in contrary["weaker_peers"]
        if row["peer"]["family_id"] == "actual_foreign_residue_projection"
    ]
    assert len(weaker) == 1
    assert weaker[0]["relation_class"] == "contrary_evidence"
    assert contrary["family"]["source_declaration"].endswith(
        "fixedPrecisionTropicalNoGo; "
        "Erdos249257.TotientTailPeriodKiller.vu_step_has_centred_completion; "
        "Erdos249257.TotientTailPeriodKiller.vu_word_has_prefix_locked_completion"
    )
    assert "finite-word" in contrary["family"]["open_boundary"]


def test_palomar_relation_and_detail_array_order_cannot_change_authority_rank() -> None:
    palomar = {
        "selection_contract": {
            "programme_family_order": [
                {
                    "problem": 249,
                    "family_ids": ["actual_lcm", "first_harmonic", "fixed", "foreign"],
                }
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
            ],
        },
        "candidate_ranking": [],
        "candidate_value_dispositions": {
            "source_landscape_candidates": [
                {
                    "family_id": "actual_lcm",
                    "source_declaration": "Source.actual_lcm",
                    "source_file": "Erdos249257/ActualLcm.lean",
                    "hard_mechanism": "actual LCM mechanism",
                },
                {
                    "family_id": "first_harmonic",
                    "source_declaration": "Source.first_harmonic",
                    "source_file": "Erdos249257/FirstHarmonic.lean",
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
                    "families": [
                        {
                            "id": family_id,
                            "summary": f"{family_id} summary",
                            "boundary": f"{family_id} boundary",
                        }
                        for family_id in ["actual_lcm", "first_harmonic", "fixed", "foreign"]
                    ]
                }
            ]
        }
    }
    reversed_source = deepcopy(palomar)
    reversed_source["selection_contract"]["family_relations"].reverse()
    reversed_source["candidate_value_dispositions"][
        "source_landscape_candidates"
    ].reverse()
    reversed_claims = deepcopy(claims)
    reversed_claims["external_verification_packet"]["review_matrix"][0][
        "families"
    ].reverse()

    normal = build_family_relations_packet(palomar, claims, "first_harmonic")
    reversed_packet = build_family_relations_packet(
        reversed_source, reversed_claims, "first_harmonic"
    )
    assert normal == reversed_packet
    assert normal["family"]["authority_rank"]["programme_position"] == 2
    assert normal["stronger_peers"][0]["peer"]["family_id"] == "actual_lcm"


if __name__ == "__main__":
    tests = [
        value
        for name, value in sorted(globals().items())
        if name.startswith("test_") and callable(value)
    ]
    for test in tests:
        test()
    print(f"query semantic tier tests: {len(tests)} passed")
