#!/usr/bin/env python3
"""Focused contract and live-Lean tests for ``proof_state_compiler.py``."""

from __future__ import annotations

import copy
import json

import proof_state_compiler as compiler


def check_goal_parser() -> None:
    state = """case left
x : Nat
⊢ x = x

case right
y : Nat
⊢ y ≤ y"""
    goals = compiler.split_goal_state(state)
    assert [goal["case"] for goal in goals] == ["left", "right"]
    assert [goal["target"] for goal in goals] == ["⊢ x = x", "⊢ y ≤ y"]


def check_minimal_cuts() -> None:
    cuts = compiler.minimal_hitting_sets(
        [{"a", "b"}, {"b", "c"}]
    )
    assert cuts == [["b"], ["a", "c"]]


def check_live_pilot() -> dict:
    packet = compiler.compile_pilot_suite()
    assert packet["schema_version"] == compiler.PILOT_SCHEMA
    assert packet["packet_bytes"] < compiler.MAX_PACKET_BYTES
    assert packet["pilot_verdict"] == {
        "blocked_control_is_precise": True,
        "counterfactual_closes": True,
        "independent_ready_control_closes": True,
    }
    causal = packet["causal_obstruction_receipt"]
    assert causal["same_target"]
    assert causal["same_candidate_action"]
    assert causal["added_assumptions"] == ["hdvd"]
    assert causal["effect"] == (
        "exact_obligation_is_causally_sufficient_for_this_transition"
    )

    blocked = packet["cases"]["integer_tail_without_divisibility"]
    transition = blocked["lean_tested_transitions"][0]
    assert transition["status"] == "lean_accepted_open_obligations"
    assert transition["lean_run_receipt"][
        "expected_unsolved_goal_error_ignored"
    ]
    assert transition["declaration_receipt"]["source_ref"] == (
        "Erdos249257/TotientTailPeriodKiller.lean:327"
    )
    assert blocked["minimal_blocker_cuts"][0]["targets"] == [
        "⊢ r.den ∣ 2 ^ N * (2 ^ h - 1)"
    ]

    ready = packet["cases"]["integer_tail_with_divisibility"]
    assert ready["closed_proof_receipts"]
    assert ready["lean_tested_transitions"][0]["proof_closed"]

    curvature = packet["cases"]["curvature_supply_control"]
    curvature_transition = curvature["lean_tested_transitions"][0]
    assert curvature_transition["proof_closed"]
    assert curvature_transition["open_obligations"][0]["target"] == (
        "⊢ SharpCurvatureSupply"
    )
    return packet


def check_typed_rejection() -> None:
    request = copy.deepcopy(compiler.pilot_requests()[0])
    request["goal_id"] = "deliberately_incompatible_candidate"
    request["candidates"][0] = {
        "candidate_id": "wrong_shape",
        "declaration": (
            "Erdos249257.TotientTailPeriodKiller."
            "irrational_totientSeries_of_sharpCurvatureSupply"
        ),
        "arguments": [],
        "discharge_tactics": [],
    }
    packet = compiler.compile_request(request)
    transition = packet["lean_tested_transitions"][0]
    assert transition["status"] == "lean_rejected"
    assert not transition["application_accepted"]
    assert transition["typed_failures"]
    assert packet["abstention_receipt"]["status"] == (
        "all_candidates_rejected_by_Lean"
    )


def main() -> int:
    check_goal_parser()
    check_minimal_cuts()
    packet = check_live_pilot()
    check_typed_rejection()
    print(
        json.dumps(
            {
                "schema": "proof-state-compiler-test-receipt/1",
                "passed": True,
                "checks": 4,
                "pilot_packet_bytes": packet["packet_bytes"],
                "environment_fingerprint": packet[
                    "environment_fingerprint"
                ]["fingerprint"],
            },
            sort_keys=True,
        )
    )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
