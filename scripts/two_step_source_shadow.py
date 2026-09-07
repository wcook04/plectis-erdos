#!/usr/bin/env python3
"""Exact audit for the bounded-lookahead primitive-source shadow.

The script uses Fraction throughout.  It checks the proposed shadow inequality

    sum_d g_d q_{N,d} >= sum_d c_d q_{N,d},

where g is the ordinary real-greedy word, through rank N, for the truncated
primitive Lambert source sum_{d <= N+H} c_d/(2^d-1).
"""

from __future__ import annotations

import argparse
import json
from fractions import Fraction
from math import gcd


def mersenne(rank: int) -> int:
    return (1 << rank) - 1


def quotient(horizon: int, rank: int) -> int:
    return (1 << horizon) // mersenne(rank)


def primitive_product_coefficients(
    left: int, right: int, stop: int
) -> list[int]:
    """c_n = #{(i,j)>0 : gcd(i,j)=1 and left*i+right*j=n}."""
    coefficients = [0] * (stop + 1)
    for i in range(1, stop // left + 1):
        remaining = stop - left * i
        for j in range(1, remaining // right + 1):
            if gcd(i, j) == 1:
                coefficients[left * i + right * j] += 1
    return coefficients


def totients(stop: int) -> list[int]:
    values = list(range(stop + 1))
    for prime in range(2, stop + 1):
        if values[prime] != prime:
            continue
        for multiple in range(prime, stop + 1, prime):
            values[multiple] -= values[multiple] // prime
    if stop >= 1:
        values[1] = 1
    return values


def totient_four_ninths_coefficients(stop: int) -> list[int]:
    phi = totients(stop // 2)
    coefficients = [0] * (stop + 1)
    for rank in range(2, stop + 1, 2):
        coefficients[rank] = phi[rank // 2]
    return coefficients


def greedy_word(target: Fraction, stop: int) -> tuple[list[int], Fraction]:
    selected: list[int] = []
    residual = target
    for rank in range(1, stop + 1):
        coin = Fraction(1, mersenne(rank))
        if coin <= residual:
            selected.append(rank)
            residual -= coin
    return selected, residual


def raw_pulse(coefficients: list[int], rank: int) -> int:
    """The divisor sum A_rank = sum_{d | rank} c_d."""
    return sum(
        coefficients[divisor]
        for divisor in range(1, rank + 1)
        if rank % divisor == 0
    )


def fractional_part(numerator: int, denominator: int) -> Fraction:
    return Fraction(numerator % denominator, denominator)


def audit_source(
    *,
    label: str,
    target: Fraction,
    coefficients: list[int],
    depth: int,
    lookahead: int,
    expected_nonnegative: bool,
    product_period: int | None = None,
) -> dict[str, object]:
    weights = [Fraction(0)] + [
        Fraction(1, mersenne(rank))
        for rank in range(1, depth + lookahead + 1)
    ]
    source_prefix = [Fraction(0)] * (depth + lookahead + 1)
    for rank in range(1, depth + lookahead + 1):
        source_prefix[rank] = (
            source_prefix[rank - 1] + coefficients[rank] * weights[rank]
        )

    first_failure: dict[str, int] | None = None
    first_positive: dict[str, int] | None = None
    minimum_margin: int | None = None
    maximum_margin = 0
    maximum_raw_carry = 0
    minimum_source_budget: Fraction | None = None
    minimum_terminal_run = depth

    for horizon in range(1, depth + 1):
        truncated_target = source_prefix[horizon + lookahead]
        selected, residual = greedy_word(truncated_target, horizon)
        greedy_quotient = sum(quotient(horizon, rank) for rank in selected)
        source_quotient = sum(
            coefficients[rank] * quotient(horizon, rank)
            for rank in range(1, horizon + 1)
        )
        margin = greedy_quotient - source_quotient
        raw_carry = (target.numerator * (1 << horizon)) // target.denominator
        raw_carry -= source_quotient

        assert residual >= 0
        assert raw_carry >= 0
        if product_period is not None:
            assert raw_carry == horizon // product_period
        else:
            assert raw_carry <= (horizon + 2) // 3

        selected_set = set(selected)
        source_fractional_load = sum(
            coefficients[rank]
            * fractional_part(1 << horizon, mersenne(rank))
            for rank in range(1, horizon + 1)
        )
        lookahead_mass = (1 << horizon) * sum(
            coefficients[rank] * weights[rank]
            for rank in range(
                horizon + 1, horizon + lookahead + 1
            )
        )
        source_budget = source_fractional_load + lookahead_mass
        boolean_fractional_load = sum(
            fractional_part(1 << horizon, mersenne(rank))
            for rank in selected
        )
        assert Fraction(margin) == (
            source_budget
            - boolean_fractional_load
            - (1 << horizon) * residual
        )

        pulse_lower_bound = Fraction(raw_pulse(coefficients, horizon + 1), 2)
        if lookahead >= 2:
            pulse_lower_bound += Fraction(
                raw_pulse(coefficients, horizon + 2), 4
            )
        assert source_budget >= pulse_lower_bound

        last_skipped = max(
            rank
            for rank in range(1, horizon + 1)
            if rank not in selected_set
        )
        terminal_run = horizon - last_skipped
        terminal_residual_ceiling = weights[last_skipped] - sum(
            weights[rank]
            for rank in range(last_skipped + 1, horizon + 1)
        )
        assert residual < terminal_residual_ceiling
        minimum_terminal_run = min(minimum_terminal_run, terminal_run)
        minimum_source_budget = (
            source_budget
            if minimum_source_budget is None
            else min(minimum_source_budget, source_budget)
        )

        minimum_margin = margin if minimum_margin is None else min(
            minimum_margin, margin
        )
        maximum_margin = max(maximum_margin, margin)
        maximum_raw_carry = max(maximum_raw_carry, raw_carry)
        if margin > 0 and first_positive is None:
            first_positive = {"horizon": horizon, "margin": margin}
        if margin < 0 and first_failure is None:
            first_failure = {
                "horizon": horizon,
                "margin": margin,
                "next_pulse": raw_pulse(coefficients, horizon + 1),
                "second_pulse": (
                    raw_pulse(coefficients, horizon + 2)
                    if lookahead >= 2
                    else None
                ),
                "source_budget": str(source_budget),
                "boolean_fractional_load": str(
                    boolean_fractional_load
                ),
                "scaled_residual": str((1 << horizon) * residual),
                "last_skipped_rank": last_skipped,
                "terminal_take_run": terminal_run,
            }

    if expected_nonnegative:
        assert first_failure is None

    return {
        "label": label,
        "lookahead": lookahead,
        "depth": depth,
        "minimum_margin": minimum_margin,
        "maximum_margin": maximum_margin,
        "first_positive_margin": first_positive,
        "first_failure": first_failure,
        "maximum_raw_carry": maximum_raw_carry,
        "minimum_source_budget": str(minimum_source_budget),
        "minimum_terminal_take_run": minimum_terminal_run,
        "status": (
            "verified_nonnegative_to_depth"
            if first_failure is None
            else "exact_counterexample_found"
        ),
    }


def parse_args() -> argparse.Namespace:
    parser = argparse.ArgumentParser()
    parser.add_argument("--depth", type=int, default=450)
    return parser.parse_args()


def main() -> None:
    args = parse_args()
    depth = args.depth
    max_lookahead = 2
    stop = depth + max_lookahead

    positive_cases = [
        audit_source(
            label="M(2,3)=1/21; one-step shadow",
            target=Fraction(1, mersenne(2) * mersenne(3)),
            coefficients=primitive_product_coefficients(2, 3, stop),
            depth=depth,
            lookahead=1,
            expected_nonnegative=True,
            product_period=6,
        ),
        audit_source(
            label="M(2,3)=1/21; two-step shadow",
            target=Fraction(1, mersenne(2) * mersenne(3)),
            coefficients=primitive_product_coefficients(2, 3, stop),
            depth=depth,
            lookahead=2,
            expected_nonnegative=True,
            product_period=6,
        ),
        audit_source(
            label="M(4,5)=1/465; two-step shadow",
            target=Fraction(1, mersenne(4) * mersenne(5)),
            coefficients=primitive_product_coefficients(4, 5, stop),
            depth=depth,
            lookahead=2,
            expected_nonnegative=True,
            product_period=20,
        ),
        audit_source(
            label="totient source 4/9; two-step shadow",
            target=Fraction(4, 9),
            coefficients=totient_four_ninths_coefficients(stop),
            depth=depth,
            lookahead=2,
            expected_nonnegative=True,
        ),
    ]

    controls = []
    for left, right in [(3, 9), (4, 8), (5, 10), (6, 9), (4, 4), (3, 3)]:
        controls.append(
            audit_source(
                label=f"noncoprime control M({left},{right})",
                target=Fraction(1, mersenne(left) * mersenne(right)),
                coefficients=primitive_product_coefficients(left, right, stop),
                depth=depth,
                lookahead=2,
                expected_nonnegative=False,
            )
        )

    expected_control_failures = {
        "noncoprime control M(3,9)": 21,
        "noncoprime control M(4,8)": 20,
        "noncoprime control M(5,10)": 25,
        "noncoprime control M(6,9)": 33,
        "noncoprime control M(4,4)": 12,
        "noncoprime control M(3,3)": 9,
    }
    for receipt in controls:
        assert receipt["first_failure"] is not None
        assert receipt["first_failure"]["horizon"] == expected_control_failures[
            receipt["label"]
        ]
        assert receipt["first_failure"]["next_pulse"] == 0
        assert receipt["first_failure"]["second_pulse"] == 0

    print(
        json.dumps(
            {
                "claim": "bounded-lookahead primitive-source quotient shadow",
                "claim_status": "finite exact evidence; all-depth theorem open",
                "positive_cases": positive_cases,
                "discriminating_controls": controls,
            },
            indent=2,
            sort_keys=True,
        )
    )


if __name__ == "__main__":
    main()
