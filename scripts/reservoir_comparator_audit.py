#!/usr/bin/env python3
"""Exact checks for the reservoir lexicographic comparator calculation.

This script verifies the superincreasing corrected quotient coefficients
and reproduces the first failure of the direct quotient-row deletion repair.
It supplies finite checks only; the coefficient proof is in
ReservoirComparatorAttack.md.
"""

from __future__ import annotations

import argparse
import json
from fractions import Fraction
from math import isqrt


def quotient_weight(horizon: int, rank: int) -> int:
    return (1 << horizon) // ((1 << rank) - 1)


def reservoir_weight(horizon: int, rank: int) -> int:
    return (
        quotient_weight(horizon, rank)
        - 1
        + int(2 * rank <= horizon)
    )


def source_count(horizon: int) -> int:
    return sum(rank % 6 in (5, 0) for rank in range(1, horizon + 1))


def reservoir(bits: list[int]) -> int:
    horizon = len(bits)
    target_prefix = (1 << horizon) // 21
    weighted = sum(
        bit * reservoir_weight(horizon, rank)
        for rank, bit in enumerate(bits, start=1)
    )
    return source_count(horizon) + 3 - target_prefix + weighted


def quotient_greedy_word(horizon: int) -> list[int]:
    capacity = (1 << horizon) // 21
    bits: list[int] = []
    for rank in range(1, horizon + 1):
        weight = quotient_weight(horizon, rank)
        take = int(weight <= capacity)
        bits.append(take)
        if take:
            capacity -= weight
    return bits


def real_sum(bits: list[int]) -> Fraction:
    return sum(
        (
            Fraction(1, (1 << rank) - 1)
            for rank, bit in enumerate(bits, start=1)
            if bit
        ),
        Fraction(0),
    )


def verify_strong_gap(max_horizon: int) -> dict[str, int]:
    minimum_positive_gap: int | None = None
    minimum_horizon = 0
    minimum_rank = 0
    for horizon in range(2, max_horizon + 1):
        tail = 0
        for rank in range(horizon, 0, -1):
            weight = reservoir_weight(horizon, rank)
            if rank < horizon:
                gap = weight - tail
                if gap <= 0:
                    raise AssertionError(
                        f"strong gap failed at N={horizon}, d={rank}: {gap}"
                    )
                if minimum_positive_gap is None or gap < minimum_positive_gap:
                    minimum_positive_gap = gap
                    minimum_horizon = horizon
                    minimum_rank = rank
            tail += weight
    assert minimum_positive_gap is not None
    return {
        "max_horizon": max_horizon,
        "minimum_positive_gap": minimum_positive_gap,
        "minimum_gap_horizon": minimum_horizon,
        "minimum_gap_rank": minimum_rank,
    }


def threshold_word(horizon: int) -> tuple[list[int], int]:
    """Lexicographically least word whose reservoir is nonnegative."""
    weights = [
        reservoir_weight(horizon, rank) for rank in range(1, horizon + 1)
    ]
    target = (1 << horizon) // 21 - source_count(horizon) - 3
    remaining_tail = sum(weights)
    deficit = target
    bits: list[int] = []
    for weight in weights:
        remaining_tail -= weight
        take = int(remaining_tail < deficit)
        bits.append(take)
        if take:
            deficit -= weight
    if deficit > 0:
        raise AssertionError(f"threshold was not crossed at N={horizon}")
    return bits, -deficit


def certify_real_feasible(bits: list[int]) -> tuple[int, int]:
    """Certify comparison with both the binary truncation and 1/21."""
    horizon = len(bits)
    precision = 2 * horizon + 128
    scale = 1 << precision
    target_lower = scale // 21
    truncation_scaled = ((1 << horizon) // 21) << (precision - horizon)
    sum_upper = 0
    for rank, bit in enumerate(bits, start=1):
        if bit:
            denominator = (1 << rank) - 1
            sum_upper += (scale + denominator - 1) // denominator
    target_margin = target_lower - sum_upper
    truncation_margin = truncation_scaled - sum_upper
    if target_margin < 0:
        raise AssertionError(
            f"threshold comparator not certified feasible at N={horizon}"
        )
    if truncation_margin < 0:
        raise AssertionError(
            f"threshold comparator exceeds binary truncation at N={horizon}"
        )
    return target_margin, truncation_margin


def verify_threshold_comparators(max_horizon: int) -> dict[str, int]:
    maximum_overshoot = (-1, 0)
    minimum_margin_bits: tuple[int, int] | None = None
    previous_bits: list[int] | None = None
    maximum_recut_lag = (0, 0, 0)
    recut_count = 0
    for horizon in range(1, max_horizon + 1):
        bits, overshoot = threshold_word(horizon)
        target_margin, truncation_margin = certify_real_feasible(bits)
        if previous_bits is not None:
            first_difference = next(
                (
                    rank
                    for rank in range(1, horizon)
                    if bits[rank - 1] != previous_bits[rank - 1]
                ),
                None,
            )
            if first_difference is not None:
                if bits[first_difference - 1] != 1:
                    raise AssertionError(
                        "threshold words decreased lexicographically at "
                        f"N={horizon}, d={first_difference}"
                    )
                recut_count += 1
                maximum_recut_lag = max(
                    maximum_recut_lag,
                    (horizon - first_difference, horizon, first_difference),
                )
        previous_bits = bits
        maximum_overshoot = max(maximum_overshoot, (overshoot, horizon))
        margin_bits = min(
            target_margin.bit_length(), truncation_margin.bit_length()
        )
        if minimum_margin_bits is None or margin_bits < minimum_margin_bits[0]:
            minimum_margin_bits = (margin_bits, horizon)
    assert minimum_margin_bits is not None
    return {
        "max_horizon": max_horizon,
        "maximum_threshold_overshoot": maximum_overshoot[0],
        "maximum_overshoot_horizon": maximum_overshoot[1],
        "minimum_directed_margin_bit_length": minimum_margin_bits[0],
        "minimum_margin_horizon": minimum_margin_bits[1],
        "lex_increase_recut_count": recut_count,
        "maximum_recut_lag": maximum_recut_lag[0],
        "maximum_recut_lag_horizon": maximum_recut_lag[1],
        "maximum_recut_lag_first_rank": maximum_recut_lag[2],
    }


def verify_sample_horizon(horizon: int) -> dict[str, int]:
    bits, overshoot = threshold_word(horizon)
    target_margin, truncation_margin = certify_real_feasible(bits)
    return {
        "horizon": horizon,
        "selected": sum(bits),
        "threshold_overshoot": overshoot,
        "target_margin_bit_length": target_margin.bit_length(),
        "binary_truncation_margin_bit_length": truncation_margin.bit_length(),
    }


def verify_square_root_comparator(max_horizon: int) -> dict[str, int]:
    maximum_excess = (-10**9, 0)
    checked = 0
    for horizon in range(1, max_horizon + 1):
        safety = 2 * isqrt(horizon) + 5
        capacity = (1 << horizon) // 21 - safety
        if capacity < 0:
            continue
        bits: list[int] = []
        for rank in range(1, horizon + 1):
            weight = quotient_weight(horizon, rank)
            take = int(weight <= capacity)
            bits.append(take)
            if take:
                capacity -= weight
        if capacity != 0:
            raise AssertionError(
                f"square-root comparator has terminal remainder at N={horizon}"
            )
        checked += 1
        upper_count = sum(bits[horizon // 2 :])
        excess = upper_count - source_count(horizon)
        maximum_excess = max(maximum_excess, (excess, -horizon))
    if checked == 0:
        raise AssertionError("no nonnegative square-root target was checked")
    return {
        "max_horizon": max_horizon,
        "checked_nonnegative_targets": checked,
        "maximum_upper_count_minus_source_count": maximum_excess[0],
        "first_maximum_horizon": -maximum_excess[1],
    }


def first_direct_repair_failure(search_horizon: int) -> dict[str, object]:
    target = Fraction(1, 21)
    for horizon in range(1, search_horizon + 1):
        bits = quotient_greedy_word(horizon)
        if real_sum(bits) <= target:
            continue
        repaired = bits.copy()
        deleted: list[int] = []
        for rank in range(horizon, 0, -1):
            if repaired[rank - 1]:
                repaired[rank - 1] = 0
                deleted.append(rank)
                if real_sum(repaired) <= target:
                    break
        if real_sum(repaired) > target:
            raise AssertionError("deletion repair did not reach feasibility")
        if reservoir(repaired) < 0:
            return {
                "horizon": horizon,
                "quotient_support": [
                    rank for rank, bit in enumerate(bits, start=1) if bit
                ],
                "quotient_reservoir": reservoir(bits),
                "deleted_ranks": deleted,
                "repaired_support": [
                    rank for rank, bit in enumerate(repaired, start=1) if bit
                ],
                "repaired_reservoir": reservoir(repaired),
                "repaired_real_sum": str(real_sum(repaired)),
            }
    raise AssertionError("no direct-repair counterexample in search range")


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--gap-depth", type=int, default=1000)
    parser.add_argument("--repair-depth", type=int, default=100)
    parser.add_argument("--threshold-depth", type=int, default=1000)
    parser.add_argument(
        "--sample-horizon", type=int, action="append", default=[]
    )
    parser.add_argument("--sqrt-depth", type=int, default=0)
    args = parser.parse_args()
    if (
        args.gap_depth < 2
        or args.repair_depth < 9
        or args.threshold_depth < 1
        or args.sqrt_depth < 0
        or any(horizon < 1 for horizon in args.sample_horizon)
    ):
        raise SystemExit(
            "gap depth must be at least 2, repair depth at least 9, "
            "and threshold and sample depths positive"
        )
    result = {
        "method": "exact integer coefficient gaps and exact rational feasibility",
        "strong_gap": verify_strong_gap(args.gap_depth),
        "threshold_comparator": verify_threshold_comparators(
            args.threshold_depth
        ),
        "sample_horizons": [
            verify_sample_horizon(horizon) for horizon in args.sample_horizon
        ],
        "square_root_comparator": (
            verify_square_root_comparator(args.sqrt_depth)
            if args.sqrt_depth
            else None
        ),
        "first_direct_repair_failure": first_direct_repair_failure(
            args.repair_depth
        ),
        "claim_status": "finite checks supporting an exact written derivation",
    }
    print(json.dumps(result, indent=2, sort_keys=True))


if __name__ == "__main__":
    main()
