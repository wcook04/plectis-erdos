#!/usr/bin/env python3
"""Exact finite audit of the actual doubling block and quotient suffix.

The greedy decisions are certified by a fixed dyadic enclosure.  The script
then checks the Lambert-defect recurrence, the low-suffix carry identity, and
the delayed-doubling density candidate.  Every reported assertion is finite.
"""

from __future__ import annotations

import argparse
import json


def source_ones(horizon: int) -> int:
    return 2 * (horizon // 6) + int(horizon % 6 >= 5)


def sharper_threshold_comparator_audit(max_horizon: int) -> dict[str, object]:
    """Audit the canonical superincreasing comparator for the sharper law.

    Feasibility is certified by directed fixed-point bounds on the fractional
    quotient remainders.  No floating-point comparison is used.
    """
    quotient_weights = [0]
    precision = 160
    scale = 1 << precision
    minimum_scaled_margin: tuple[int, int, dict[str, int]] | None = None
    maximum_overshoot = (-1, 0)
    for horizon in range(1, max_horizon + 1):
        for rank in range(1, horizon):
            quotient_weights[rank] = (
                2 * quotient_weights[rank] + int(horizon % rank == 0)
            )
        quotient_weights.append(1)
        weights = [
            2 * quotient_weights[rank] - int(2 * rank > horizon)
            for rank in range(1, horizon + 1)
        ]
        target = (
            2 * ((1 << horizon) // 21) - source_ones(horizon) - 4
        )
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
            raise AssertionError(f"threshold not crossed at N={horizon}")
        overshoot = -deficit
        maximum_overshoot = max(maximum_overshoot, (overshoot, -horizon))

        defect = (1 << horizon) // 21 - sum(
            quotient_weights[rank] * bits[rank - 1]
            for rank in range(1, horizon + 1)
        )
        fractional_upper = 0
        for rank, bit in enumerate(bits, start=1):
            if not bit:
                continue
            denominator = (1 << rank) - 1
            numerator = 1 << (horizon % rank)
            fractional_upper += (
                scale * numerator + denominator - 1
            ) // denominator
        target_fraction_numerator = (1 << horizon) % 21
        feasible_lower = (
            defect * scale
            + scale * target_fraction_numerator // 21
        )
        directed_margin = feasible_lower - fractional_upper
        if directed_margin < 0:
            raise AssertionError(
                "sharper threshold comparator not certified feasible at "
                f"N={horizon}, directed margin={directed_margin}"
            )
        receipt = {
            "rank": horizon,
            "directed_margin_numerator_at_2_pow_160": directed_margin,
            "defect": defect,
            "overshoot": overshoot,
            "selected_count": sum(bits),
            "upper_half_selected_count": sum(bits[horizon // 2 :]),
        }
        if (
            minimum_scaled_margin is None
            or directed_margin < minimum_scaled_margin[0]
        ):
            minimum_scaled_margin = (directed_margin, horizon, receipt)
    assert minimum_scaled_margin is not None
    return {
        "max_horizon": max_horizon,
        "fixed_point_precision": precision,
        "minimum_directed_fractional_margin": minimum_scaled_margin[2],
        "maximum_threshold_overshoot": maximum_overshoot[0],
        "first_maximum_overshoot_horizon": -maximum_overshoot[1],
        "claim_status": "exact finite directed-rounding certificate only",
    }


def actual_greedy_bits(depth: int) -> list[int]:
    precision = 2 * depth + 64
    scale = 1 << precision
    lower = scale // 21
    upper = (scale + 20) // 21
    bits = [0] * (depth + 1)
    for n in range(1, depth + 1):
        weight_floor = scale // ((1 << n) - 1)
        if lower >= weight_floor + 1:
            lower -= weight_floor + 1
            upper -= weight_floor
            bits[n] = 1
        elif upper <= weight_floor:
            continue
        else:
            raise AssertionError(f"ambiguous branch at rank {n}")
    return bits


def audit(depth: int) -> dict[str, object]:
    bits = actual_greedy_bits(depth)
    prefix_count = [0] * (depth + 1)
    source_count = [0] * (depth + 1)
    divisor_count = [0] * (depth + 1)
    for n in range(1, depth + 1):
        prefix_count[n] = prefix_count[n - 1] + bits[n]
        source_count[n] = source_count[n - 1] + int(n % 6 in (5, 0))
        if bits[n]:
            for multiple in range(n, depth + 1, n):
                divisor_count[multiple] += 1

    defect = [0] * (depth + 1)
    for n in range(1, depth + 1):
        source_bit = int(n % 6 in (5, 0))
        defect[n] = (
            2 * defect[n - 1] + source_bit - divisor_count[n]
        )
        if defect[n] < 0:
            raise AssertionError(f"negative actual defect at rank {n}")

    maximum_density = (-10**9, 0)
    for n in range(1, depth + 1):
        excess = (
            prefix_count[n] - n // 3 - prefix_count[n // 2]
        )
        maximum_density = max(maximum_density, (excess, -n))

    sharper_minimum = (10**9, 0)
    sharper_zero_ranks: list[int] = []
    minimum_zero_defect_reservoir = (10**9, 0)
    previous_defect = 0
    first_failure_pressure = (-10**9, 0, {})
    for n in range(1, depth + 1):
        source_ones = source_count[n]
        p_state = (
            source_ones + prefix_count[n // 2] - prefix_count[n]
        )
        reservoir_state = p_state + 3 - defect[n]
        sharper_state = p_state + 4 - 2 * defect[n]
        sharper_minimum = min(sharper_minimum, (sharper_state, n))
        if sharper_state == 0:
            sharper_zero_ranks.append(n)
        if defect[n] == 0:
            minimum_zero_defect_reservoir = min(
                minimum_zero_defect_reservoir, (reservoir_state, n)
            )
        proper_load = divisor_count[n] - bits[n]
        self_double = int(n % 2 == 0) * bits[n // 2]
        source_bit = int(n % 6 in (5, 0))
        increment_without_withdrawal = (
            bits[n] - source_bit + self_double + 2 * proper_load
        )
        withdrawal_pressure = 2 * previous_defect - increment_without_withdrawal
        first_failure_pressure = max(
            first_failure_pressure,
            (
                withdrawal_pressure,
                -n,
                {
                    "rank": n,
                    "previous_defect": previous_defect,
                    "bit": bits[n],
                    "source_bit": source_bit,
                    "proper_divisor_load": proper_load,
                    "self_double_bit": self_double,
                    "sharper_state": sharper_state,
                },
            ),
        )
        previous_defect = defect[n]

    endpoint_patterns: dict[str, int] = {}
    for k in range(1, (depth - 2) // 2 + 1):
        pattern = f"{bits[k + 1]}{bits[2 * k + 1]}{bits[2 * k + 2]}"
        endpoint_patterns[pattern] = endpoint_patterns.get(pattern, 0) + 1
    if depth >= 20_000:
        assert len(endpoint_patterns) == 8

    maximum_borrow = (-10**9, 0, {})
    prefix_word = 0
    for n in range(1, depth + 1):
        prefix_word = 2 * prefix_word + bits[n]
        if n < 5 or n % 2 == 0:
            continue
        k = (n - 1) // 2
        mask = (1 << k) - 1
        actual_word = prefix_word & mask
        q = defect[n] & mask
        full_sum = actual_word + q
        low_suffix = full_sum & mask
        final_carry = full_sum >> k
        carry_count = (
            actual_word.bit_count() + q.bit_count() - full_sum.bit_count()
        )
        borrow_excess = actual_word.bit_count() - low_suffix.bit_count()
        assert borrow_excess == (
            carry_count + final_carry - q.bit_count()
        )
        receipt = {
            "K": k,
            "Q_2K_plus_1": defect[n],
            "q_K": q,
            "actual_block_popcount": actual_word.bit_count(),
            "low_suffix_popcount": low_suffix.bit_count(),
            "binary_carry_count": carry_count,
            "final_carry": final_carry,
            "source_ones_in_block": source_count[n] - source_count[k + 1],
            "quotient_suffix_allowance": (2 * k + 5) // 3,
            "quotient_suffix_slack": (
                (2 * k + 5) // 3 - low_suffix.bit_count()
            ),
            "actual_odd_block_allowance": (
                (2 * k + 1) // 3 + 2 - bits[k + 1]
            ),
            "actual_odd_block_slack": (
                (2 * k + 1) // 3
                + 2
                - bits[k + 1]
                - actual_word.bit_count()
            ),
            "reservoir_bit_length": full_sum.bit_length(),
            "reservoir_lt_2_pow_K": full_sum < 1 << k,
        }
        maximum_borrow = max(
            maximum_borrow, (borrow_excess, -k, receipt)
        )

    k = 6
    n = 2 * k + 1
    prefix_word = 0
    for rank in range(1, n + 1):
        prefix_word = 2 * prefix_word + bits[rank]
    actual_word = prefix_word & ((1 << k) - 1)
    reservoir = actual_word + defect[n]
    direct_reservoir = (1 << n) // 21 - sum(
        (1 << n) // ((1 << rank) - 1)
        for rank in range(1, k + 2)
        if bits[rank]
    )
    assert reservoir == direct_reservoir
    k_six = {
        "actual_block_word": actual_word,
        "actual_block_binary": format(actual_word, f"0{k}b"),
        "Q_13": defect[n],
        "odd_quotient_reservoir": reservoir,
        "reservoir_binary": format(reservoir, f"0{k}b"),
    }
    assert k_six == {
        "actual_block_word": 61,
        "actual_block_binary": "111101",
        "Q_13": 1,
        "odd_quotient_reservoir": 62,
        "reservoir_binary": "111110",
    }

    cofinite_start = 7
    cofinite_depth = 18
    cofinite_bits = [0] * (cofinite_depth + 1)
    cofinite_divisor_count = [0] * (cofinite_depth + 1)
    cofinite_prefix_count = [0] * (cofinite_depth + 1)
    cofinite_defect = [0] * (cofinite_depth + 1)
    cofinite_first_sharper_failure: dict[str, int] | None = None
    for rank in range(cofinite_start, cofinite_depth + 1):
        cofinite_bits[rank] = 1
        for multiple in range(rank, cofinite_depth + 1, rank):
            cofinite_divisor_count[multiple] += 1
    for rank in range(1, cofinite_depth + 1):
        cofinite_prefix_count[rank] = (
            cofinite_prefix_count[rank - 1] + cofinite_bits[rank]
        )
        cofinite_defect[rank] = (
            2 * cofinite_defect[rank - 1]
            + int(rank % 6 in (5, 0))
            - cofinite_divisor_count[rank]
        )
        cofinite_source_count = sum(
            int(j % 6 in (5, 0)) for j in range(1, rank + 1)
        )
        cofinite_p = (
            cofinite_source_count
            + cofinite_prefix_count[rank // 2]
            - cofinite_prefix_count[rank]
        )
        cofinite_sharper = cofinite_p + 4 - 2 * cofinite_defect[rank]
        if cofinite_sharper < 0 and cofinite_first_sharper_failure is None:
            cofinite_first_sharper_failure = {
                "rank": rank,
                "defect": cofinite_defect[rank],
                "P": cofinite_p,
                "F": cofinite_sharper,
            }
    assert min(cofinite_defect) >= 0
    cofinite_excess = (
        cofinite_prefix_count[cofinite_depth]
        - cofinite_depth // 3
        - cofinite_prefix_count[cofinite_depth // 2]
    )
    assert cofinite_excess == 3
    assert cofinite_first_sharper_failure == {
        "rank": 7,
        "defect": 5,
        "P": 1,
        "F": -5,
    }

    return {
        "depth": depth,
        "density": {
            "maximum_excess": maximum_density[0],
            "first_maximum_rank": -maximum_density[1],
        },
        "sharper_actual_invariant": {
            "formula": "P_N + 4 - 2 Q_N",
            "minimum": sharper_minimum[0],
            "first_minimum_rank": sharper_minimum[1],
            "zero_ranks": sharper_zero_ranks,
            "minimum_reservoir_at_zero_defect": (
                minimum_zero_defect_reservoir[0]
            ),
            "first_minimum_zero_defect_rank": (
                minimum_zero_defect_reservoir[1]
            ),
            "maximum_one_step_withdrawal_pressure": (
                first_failure_pressure[0]
            ),
            "first_maximum_pressure_receipt": first_failure_pressure[2],
        },
        "K_6_word_discrepancy": k_six,
        "endpoint_pattern_counts": endpoint_patterns,
        "maximum_borrow_excess": {
            "excess": maximum_borrow[0],
            **maximum_borrow[2],
        },
        "cofinite_fixed_source_countermodel": {
            "support_start": cofinite_start,
            "test_rank": cofinite_depth,
            "minimum_defect_through_test_rank": min(cofinite_defect),
            "density_excess_at_test_rank": cofinite_excess,
            "first_sharper_invariant_failure": (
                cofinite_first_sharper_failure
            ),
        },
        "claim_status": "exact finite computation only",
    }


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--depth", type=int, default=20_000)
    parser.add_argument("--threshold-depth", type=int, default=0)
    args = parser.parse_args()
    if args.depth < 18:
        raise SystemExit("depth must be at least 18")
    if args.threshold_depth < 0:
        raise SystemExit("threshold depth must be nonnegative")
    result = audit(args.depth)
    if args.threshold_depth:
        result["sharper_threshold_comparator"] = (
            sharper_threshold_comparator_audit(args.threshold_depth)
        )
    assert result["density"]["maximum_excess"] <= 2
    assert result["sharper_actual_invariant"]["minimum"] >= 0
    print(json.dumps(result, indent=2, sort_keys=True))


if __name__ == "__main__":
    main()
