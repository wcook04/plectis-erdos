#!/usr/bin/env python3
"""Exact counterexamples to pure-period fatal-horizon bounds.

One target first dies at its source period, refuting the strict ``<P`` bound.
A second survives its complete period and first dies at ``P+1``, refuting the
corrected ``<=P`` bound.  Every comparison is a ``Fraction`` comparison or an
equivalent cleared-integer sign check.
"""
from __future__ import annotations

import argparse
import hashlib
import json
from fractions import Fraction
from pathlib import Path


SCRIPT_PATH = Path(__file__).resolve()
REPO_ROOT = SCRIPT_PATH.parents[3]
DEFAULT_OUTPUT = (
    REPO_ROOT
    / "state/formal_math/erdos257_period_noncollapse/"
    "pure_period_fatal_horizon_counterexample_receipt.json"
)
CASES = (
    {
        "name": "strict_boundary_period_26",
        "period": 26,
        "numerator": 16_559_772,
        "first_fatal_rank": 26,
        "prefix": (3, 4, 5, 8, 10, 14, 16, 19, 21, 23, 24),
    },
    {
        "name": "post_period_29",
        "period": 29,
        "numerator": 182_693_966,
        "first_fatal_rank": 30,
        "prefix": (2, 8, 9, 10, 14, 15, 17, 18, 20, 21, 23, 24, 25, 26, 27),
    },
)


def canonical_bytes(value: object) -> bytes:
    return (json.dumps(value, sort_keys=True, separators=(",", ":")) + "\n").encode()


def sha256(path: Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest()


def integer_receipt(value: int) -> dict[str, object]:
    return {
        "value": str(value),
        "bit_length": value.bit_length(),
        "sha256": hashlib.sha256(
            value.to_bytes(max(1, (value.bit_length() + 7) // 8), "big")
        ).hexdigest(),
    }


def build_case(spec: dict[str, object]) -> dict[str, object]:
    period = int(spec["period"])
    numerator = int(spec["numerator"])
    fatal_rank = int(spec["first_fatal_rank"])
    prefix = tuple(int(rank) for rank in spec["prefix"])
    denominator = (1 << period) - 1
    target = Fraction(numerator, denominator)
    reduced_numerator = target.numerator
    reduced_denominator = target.denominator
    assert reduced_denominator > 1
    assert pow(2, period, reduced_denominator) == 1
    assert all(
        pow(2, divisor, reduced_denominator) != 1
        for divisor in range(1, period)
        if period % divisor == 0
    )

    residual = target
    actual_prefix: list[int] = []
    decisions: list[int] = []
    for rank in range(1, fatal_rank + 1):
        weight = Fraction(1, (1 << rank) - 1)
        take = residual >= weight
        decisions.append(int(take))
        if take:
            residual -= weight
            actual_prefix.append(rank)
    assert tuple(actual_prefix) == prefix
    assert decisions[-1] == 0

    dyadic_edge = Fraction(1, 1 << fatal_rank)
    skipped_weight = Fraction(1, (1 << fatal_rank) - 1)
    # For k>n,
    #   w_k-2^-k = 4^-k/(1-2^-k)
    #             < 4^-k/(1-2^-(n+1)).
    # Summing the geometric majorant gives this strict infinite-tail bound.
    correction_tail_upper = Fraction(
        1 << (fatal_rank + 1),
        3 * ((1 << (fatal_rank + 1)) - 1) * (1 << (2 * fatal_rank)),
    )
    fatal_tail_upper = dyadic_edge + correction_tail_upper
    assert dyadic_edge < residual < skipped_weight
    assert residual > fatal_tail_upper

    # The residual before any earlier rank consists of the later displayed
    # prefix atoms plus this positive terminal residual.  Since the terminal
    # residual is below w_N, it is below the full remaining tail at every
    # rank < N.  Hence N is the first fatal rank.
    for rank in range(1, fatal_rank):
        later_prefix = sum(
            (
                Fraction(1, (1 << exponent) - 1)
                for exponent in prefix
                if exponent > rank
            ),
            Fraction(),
        )
        assert later_prefix + residual < sum(
            (
                Fraction(1, (1 << exponent) - 1)
                for exponent in range(rank + 1, fatal_rank + 1)
            ),
            Fraction(),
        )

    common_denominator = residual.denominator
    residual_numerator = residual.numerator
    lower_gap = (1 << fatal_rank) * residual_numerator - common_denominator
    upper_gap = (
        common_denominator - ((1 << fatal_rank) - 1) * residual_numerator
    )
    fatal_gap = (
        residual_numerator * fatal_tail_upper.denominator
        - common_denominator * fatal_tail_upper.numerator
    )
    assert lower_gap > 0
    assert upper_gap > 0
    assert fatal_gap > 0

    mersenne_scaled_prefix = denominator * sum(
        (Fraction(1, (1 << rank) - 1) for rank in prefix), Fraction()
    )
    scaled_prefix_fraction = mersenne_scaled_prefix % 1
    assert numerator == (
        mersenne_scaled_prefix.numerator // mersenne_scaled_prefix.denominator + 1
    )
    integer_gap = denominator * residual
    assert integer_gap == 1 - scaled_prefix_fraction

    return {
        "name": spec["name"],
        "target": {
            "period": period,
            "unreduced_numerator": numerator,
            "unreduced_denominator": denominator,
            "reduced_numerator": reduced_numerator,
            "reduced_denominator": reduced_denominator,
            "binary_word": format(numerator, f"0{period}b"),
        },
        "greedy": {
            "prefix_support": list(prefix),
            "decision_word_through_fatal_rank": "".join(map(str, decisions)),
            "survives_complete_source_period": fatal_rank > period,
            "first_fatal_rank": fatal_rank,
            "terminal_residual": {
                "numerator": str(residual_numerator),
                "denominator": str(common_denominator),
            },
        },
        "discovery_coordinate": {
            "scaled_prefix_fraction_numerator": str(scaled_prefix_fraction.numerator),
            "scaled_prefix_fraction_denominator": str(scaled_prefix_fraction.denominator),
            "integer_gap_to_next_numerator": {
                "numerator": str(integer_gap.numerator),
                "denominator": str(integer_gap.denominator),
            },
            "terminal_dyadic_excess_times_four_pow_rank": float(
                (residual - dyadic_edge) * (1 << (2 * fatal_rank))
            ),
        },
        "cleared_positive_gaps": {
            "above_dyadic_edge": integer_receipt(lower_gap),
            "below_skipped_weight": integer_receipt(upper_gap),
            "above_infinite_tail_upper_bound": integer_receipt(fatal_gap),
        },
    }


def build_receipt() -> dict[str, object]:
    cases = [build_case(spec) for spec in CASES]
    assert cases[0]["greedy"]["first_fatal_rank"] == cases[0]["target"]["period"]
    assert cases[1]["greedy"]["first_fatal_rank"] > cases[1]["target"]["period"]
    receipt: dict[str, object] = {
        "schema": "pure_period_fatal_horizon_counterexample_receipt_v1",
        "cases": cases,
        "mechanism_decision": {
            "strict_bound_falsified": "first_fatal<P, by strict_boundary_period_26",
            "one_period_bound_falsified": "first_fatal<=P, by post_period_29",
            "decisive_counterexample": (
                "a pure-period-29 target survives rank P and first dies at P+1"
            ),
            "consequence": (
                "no one-source-period fatality horizon can certify all-depth survival"
            ),
        },
        "validation": {
            "script_sha256": sha256(SCRIPT_PATH),
            "exact_binary_periods": True,
            "exact_greedy_prefixes": True,
            "analytic_infinite_tail_bound": (
                "T_n < 2^-n + 4^-n/[3(1-2^-(n+1))]"
            ),
            "ok": True,
        },
        "claim_status": (
            "exact finite counterexamples to both <P and <=P fatal-horizon bounds; both targets are fatal, so neither is an Erdős 257 counterexample"
        ),
    }
    receipt["canonical_digest"] = hashlib.sha256(canonical_bytes(receipt)).hexdigest()
    return receipt


def check_receipt(path: Path) -> None:
    stored = json.loads(path.read_text())
    expected = build_receipt()
    if stored != expected:
        raise AssertionError("stored receipt does not match exact recomputation")
    print(json.dumps({"receipt": str(path), "ok": True}, indent=2))


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--output", type=Path, default=DEFAULT_OUTPUT)
    parser.add_argument("--check-receipt", type=Path)
    args = parser.parse_args()
    if args.check_receipt:
        check_receipt(args.check_receipt)
        return
    receipt = build_receipt()
    args.output.parent.mkdir(parents=True, exist_ok=True)
    args.output.write_bytes(canonical_bytes(receipt))
    print(
        json.dumps(
            {
                "output": str(args.output),
                "cases": [
                    {
                        "name": case["name"],
                        "target": case["target"],
                        "greedy": case["greedy"],
                    }
                    for case in receipt["cases"]
                ],
                "mechanism_decision": receipt["mechanism_decision"],
                "validation": receipt["validation"],
            },
            indent=2,
            sort_keys=True,
        )
    )


if __name__ == "__main__":
    main()
