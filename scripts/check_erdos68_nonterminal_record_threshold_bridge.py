#!/usr/bin/env python3
"""Bind the nonterminal q=971 record to its exact #68 successor threshold.

The first genuinely nonterminal repeated factorial-one square record occurs
from ``361! - 1`` to ``609! - 1`` at ``q=971``.  The generic Lean consumer
puts ``971^2`` into the reduced predecessor-gap denominator at index 610 and
keeps the numerator nonzero modulo that square.  This checker independently
replays both the modular record and the exact rational-prefix recurrence, then
tests the cleared Archimedean threshold at the same successor state.

The result is one finite end-to-end mechanism certificate.  It is not an
infinitude theorem and does not assert that every repeated record forces the
threshold.
"""

from __future__ import annotations

import argparse
from fractions import Fraction
import hashlib
import json
from pathlib import Path
import sys
from typing import Any


REPO_ROOT = Path(__file__).resolve().parents[3]
sys.path.insert(0, str(REPO_ROOT))

from formal_math.erdos257_period_noncollapse.scripts.check_erdos68_arbitrary_valuation_records import (  # noqa: E402
    scan_prime,
)
from system.lib.formal_math_experiment_contract import (  # noqa: E402
    build_experiment_contract,
    source_record,
    validate_experiment_contract,
)


SOURCE_REF = (
    "formal_math/erdos257_period_noncollapse/scripts/"
    "check_erdos68_nonterminal_record_threshold_bridge.py"
)
VALUATION_SOURCE_REF = (
    "formal_math/erdos257_period_noncollapse/scripts/"
    "check_erdos68_arbitrary_valuation_records.py"
)
VALUATION_RECEIPT_REF = (
    "state/formal_math/erdos257_period_noncollapse/"
    "erdos68_arbitrary_valuation_record_receipt.json"
)
ANALYSIS_REF = (
    "formal_math/erdos257_period_noncollapse/ErdosProblems/Erdos68/"
    "NonterminalRecordThresholdBridgeComputationalLab.md"
)
LEAN_REF = (
    "formal_math/erdos257_period_noncollapse/ErdosProblems/Erdos68/"
    "PrimeZeroBranch.lean"
)
PACKET_REF = (
    "formal_math/erdos257_period_noncollapse/ErdosProblems/Erdos68/"
    "research_packet.json"
)
DEFAULT_OUTPUT = REPO_ROOT / (
    "state/formal_math/erdos257_period_noncollapse/"
    "erdos68_nonterminal_record_threshold_bridge_receipt.json"
)


def ceil_fraction(value: Fraction) -> int:
    return -((-value.numerator) // value.denominator)


def integer_fingerprint(value: int) -> dict[str, Any]:
    magnitude = abs(value)
    encoded = magnitude.to_bytes(
        max(1, (magnitude.bit_length() + 7) // 8), "big"
    )
    return {
        "sign": -1 if value < 0 else 1,
        "bit_length": magnitude.bit_length(),
        "sha256": hashlib.sha256(encoded).hexdigest(),
    }


def exact_successor_state(stop: int = 610) -> dict[str, Any]:
    delta = Fraction(1)
    factorial = 2
    selected: dict[int, dict[str, Any]] = {}
    for index in range(3, stop + 1):
        factorial *= index
        translated = index * delta - Fraction(1, factorial - 1)
        carry = ceil_fraction(translated) - 1
        delta = translated - carry
        assert 0 < delta <= 1
        if index in (609, 610):
            selected[index] = {
                "index": index,
                "carry": carry,
                "numerator": delta.numerator,
                "denominator": delta.denominator,
                "factorial": factorial,
            }
    return selected[610] | {"predecessor_609": selected[609]}


def build_payload() -> dict[str, Any]:
    prime = 971
    square = prime * prime
    record_row = scan_prime(prime)
    assert record_row["first_support_index"] == 361
    assert record_row["first_square_index"] == 609
    assert record_row["first_cube_index"] is None
    assert record_row["repeated_records"] == [
        {
            "q": 971,
            "earlier_support_index": 361,
            "record_index": 609,
            "previous_record_valuation": 1,
            "new_record_valuation": 2,
            "prime_power": square,
            "terminal_wilson_index": False,
        }
    ]

    state = exact_successor_state()
    index = int(state["index"])
    factorial = int(state["factorial"])
    numerator = int(state["numerator"])
    denominator = int(state["denominator"])
    cleared_left = ((index + 2) * factorial - 2) * denominator
    cleared_right = index * index * (factorial - 1) * numerator
    margin = cleared_right - cleared_left
    checks = {
        "record_is_nonterminal": 609 != prime - 2,
        "record_power_divides_actual_successor_denominator":
            denominator % square == 0,
        "actual_successor_numerator_projection_nonzero":
            numerator % square != 0,
        "actual_successor_fraction_reduced":
            __import__("math").gcd(numerator, denominator) == 1,
        "cleared_tailfree_threshold_holds": margin >= 0,
        "actual_successor_carry_is_nonunit": int(state["carry"]) != 1,
    }
    if not all(checks.values()):
        raise AssertionError([name for name, passed in checks.items() if not passed])
    assert int(state["carry"]) == 506
    assert numerator % square == 41085
    assert integer_fingerprint(numerator) == {
        "sign": 1,
        "bit_length": 1322154,
        "sha256": "adace1aedaf9f8ad896785903d9ca2afe799358da3c667a8bd9d3bdc6586f1e4",
    }
    assert integer_fingerprint(denominator) == {
        "sign": 1,
        "bit_length": 1322158,
        "sha256": "fb32e20adda4327a991a61ec2142727964a5f6956ee869f38aa7529cf881f94a",
    }
    assert integer_fingerprint(margin) == {
        "sign": 1,
        "bit_length": 1326943,
        "sha256": "53488568db98413313ff3878348f9693143916f8a12b362253e3d3e00ecf57da",
    }

    contract = build_experiment_contract(
        problem_id="erdos_68",
        target_statement="Prove irrationality of sum_(n>=2) 1/(n!-1).",
        claim_ceiling=(
            "One finite nonterminal repeated-square event whose actual successor "
            "state also closes the exact tail-free threshold; no causal theorem "
            "for all records, cofinal supply, or irrationality proof."
        ),
        hypothesis_id="nonterminal_repeated_records_cannot_reach_archimedean_closure",
        hypothesis_statement=(
            "The sparse nonterminal repeated-square mechanism may enter a reduced "
            "denominator but never reaches a state satisfying the checked "
            "Archimedean predecessor-gap threshold."
        ),
        probe_id="q971_exact_successor_threshold_bridge",
        probe_question=(
            "Does the first nonterminal repeated square feed a genuine successor "
            "denominator and nonzero projection at a state where the complete "
            "cleared threshold also holds?"
        ),
        computation=(
            "Recompute the complete q^3 factorial-residue trace for q=971, then "
            "iterate the exact Fraction predecessor-gap recurrence through m=610 "
            "and compare the two cleared threshold integers."
        ),
        falsifier=(
            "One nonterminal repeated-square successor with q^2 dividing its "
            "reduced denominator, nonzero numerator modulo q^2, and nonnegative "
            "cleared threshold margin."
        ),
        stop_condition=(
            "Stop at the first known genuinely nonterminal repeated record and bind "
            "its exact successor state; do not extend a prime horizon."
        ),
        survival_consequence=(
            "If the q=971 successor missed the threshold, keep the valuation and "
            "Archimedean producers separate pending a new coupling invariant."
        ),
        falsification_consequence=(
            "Open a composable repeated-record-to-threshold mechanism: seek a "
            "cofinal quantitative theorem guaranteeing both pieces together."
        ),
        consumer_ref=LEAN_REF,
        consumer_declarations=[
            "ErdosProblems.Erdos68.factorialGap_firstRepeatedPrimeSquare_entry",
            "ErdosProblems.Erdos68.predecessorGapNumerator_threshold_iff_cleared",
            "ErdosProblems.Erdos68.predecessorGapNumerator_threshold_forces_nonunit_or_maximal_digit",
            "ErdosProblems.Erdos68.irrational_factorialGapSeries_of_cofinal_predecessorGapNumerator_threshold",
        ],
        analysis_refs=[ANALYSIS_REF, PACKET_REF],
        source_refs=[SOURCE_REF, VALUATION_SOURCE_REF, LEAN_REF],
        input_receipt_refs=[VALUATION_RECEIPT_REF],
        result_status="exact_one_way_result",
        result_summary=(
            "The q=971 record from indices 361 to 609 is nonterminal; at m=610, "
            "971^2 divides the actual reduced denominator, the numerator is 41085 "
            "modulo 971^2, and the exact cleared threshold margin is positive."
        ),
        resource_bounds={"prime_q": 971, "record_index": 609, "max_index": 610},
        progress_class="mechanism_opened",
        decision_basis=(
            "The same exact successor state satisfies the Lean-consumed local "
            "amplification conditions and the independent Archimedean closing "
            "inequality, so the two formerly separate finite mechanisms compose."
        ),
        next_analytic_target=(
            "Prove cofinally that repeated-record amplification states meet the "
            "cleared threshold, or isolate a quantitative record condition that "
            "forces the required numerator-to-denominator ratio."
        ),
    )
    validate_experiment_contract(contract, repo_root=REPO_ROOT)
    return {
        "schema": "erdos68-nonterminal-record-threshold-bridge/1",
        "status": "verified_exact_nonterminal_record_threshold_mechanism_opening",
        "experiment_contract": contract,
        "record": record_row,
        "successor_state": {
            "index": index,
            "carry": state["carry"],
            "prime_power": square,
            "numerator_mod_prime_power": numerator % square,
            "denominator_mod_prime_power": denominator % square,
            "numerator": integer_fingerprint(numerator),
            "denominator": integer_fingerprint(denominator),
            "cleared_threshold_margin": integer_fingerprint(margin),
            "checks": checks,
        },
        "consequence_decisions": [
            {
                "mechanism": "nonterminal_repeated_record_to_finite_threshold",
                "decision": "opened_by_q971_at_successor_610",
            },
            {
                "mechanism": "all_repeated_records_force_threshold",
                "decision": "not_claimed",
            },
            {
                "mechanism": "cofinal_supply_or_irrationality",
                "decision": "not_claimed",
            },
        ],
        "source_records": [
            source_record(REPO_ROOT, ref)
            for ref in [
                SOURCE_REF,
                VALUATION_SOURCE_REF,
                VALUATION_RECEIPT_REF,
                ANALYSIS_REF,
                LEAN_REF,
                PACKET_REF,
            ]
        ],
    }


def emit(payload: dict[str, Any], output: Path, check: bool) -> int:
    rendered = json.dumps(payload, indent=2, sort_keys=True) + "\n"
    if check:
        if not output.exists() or output.read_text(encoding="utf-8") != rendered:
            print(f"stale receipt: {output}", file=sys.stderr)
            return 1
        print(json.dumps({"status": "current", "output": str(output)}))
        return 0
    output.parent.mkdir(parents=True, exist_ok=True)
    output.write_text(rendered, encoding="utf-8")
    print(json.dumps({"status": "written", "output": str(output)}))
    return 0


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--output", type=Path, default=DEFAULT_OUTPUT)
    parser.add_argument("--check", action="store_true")
    args = parser.parse_args()
    return emit(build_payload(), args.output, args.check)


if __name__ == "__main__":
    raise SystemExit(main())
