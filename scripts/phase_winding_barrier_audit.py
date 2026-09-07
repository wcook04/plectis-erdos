#!/usr/bin/env python3
"""Exact finite audit of the phase-winding barrier for the 1/21 greedy orbit.

The actual greedy decisions are certified by directed dyadic enclosures.  For
each rejected rank m, the script forms the counterfactual word which keeps the
actual prefix below m, forces rank m, and then appends zeroes.  It tests the
integer inequality

    F_alt(m+k) - k >= ceil(2^k Delta_m),

where Delta_m is the scaled real excess of the forced coin.  This is a finite
audit of a conjectural all-depth inequality, not a proof of it.
"""

from __future__ import annotations

import argparse
import json
from fractions import Fraction
from math import isqrt, lcm


def source_bit(rank: int) -> int:
    return int(rank % 6 in (5, 0))


def ceil_fraction(value: Fraction) -> int:
    return (value.numerator + value.denominator - 1) // value.denominator


def actual_greedy_enclosure(depth: int) -> tuple[list[int], list[int], list[int], int]:
    precision = 2 * depth + 64
    scale = 1 << precision
    lower = scale // 21
    upper = (scale + 20) // 21
    bits = [0] * (depth + 1)
    before_lower = [0] * (depth + 1)
    before_upper = [0] * (depth + 1)
    for rank in range(1, depth + 1):
        before_lower[rank] = lower
        before_upper[rank] = upper
        weight_floor = scale // ((1 << rank) - 1)
        if lower >= weight_floor + 1:
            lower -= weight_floor + 1
            upper -= weight_floor
            bits[rank] = 1
        elif upper <= weight_floor:
            continue
        else:
            raise AssertionError(f"ambiguous actual branch at rank {rank}")
    return bits, before_lower, before_upper, scale


def orbit_states(bits: list[int]) -> dict[str, list[int]]:
    depth = len(bits) - 1
    prefix = [0] * (depth + 1)
    source = [0] * (depth + 1)
    divisor_load = [0] * (depth + 1)
    for rank in range(1, depth + 1):
        prefix[rank] = prefix[rank - 1] + bits[rank]
        source[rank] = source[rank - 1] + source_bit(rank)
        if bits[rank]:
            for multiple in range(rank, depth + 1, rank):
                divisor_load[multiple] += 1

    defect = [0] * (depth + 1)
    sharper = [0] * (depth + 1)
    sharper[0] = 4
    for rank in range(1, depth + 1):
        defect[rank] = (
            2 * defect[rank - 1] + source_bit(rank) - divisor_load[rank]
        )
        p_state = source[rank] + prefix[rank // 2] - prefix[rank]
        sharper[rank] = p_state + 4 - 2 * defect[rank]
    return {
        "prefix": prefix,
        "source": source,
        "divisor_load": divisor_load,
        "defect": defect,
        "sharper": sharper,
    }


def exact_delta_bounds(
    rank: int,
    before_lower: int,
    before_upper: int,
    scale: int,
) -> tuple[Fraction, Fraction]:
    threshold = Fraction(1 << rank, (1 << rank) - 1)
    delta_lower = threshold - Fraction((1 << rank) * before_upper, scale)
    delta_upper = threshold - Fraction((1 << rank) * before_lower, scale)
    if not (0 < delta_lower <= delta_upper):
        raise AssertionError(f"invalid rejected-coin excess at rank {rank}")
    return delta_lower, delta_upper


def exact_binary_depth(lower: Fraction, upper: Fraction) -> int:
    """Return ceil(-log2 Delta), certified from an enclosing interval."""
    if not (0 < lower <= upper < 1):
        raise AssertionError("binary depth is requested only for 0 < Delta < 1")
    candidate = 0
    while upper * (1 << candidate) < 1:
        candidate += 1
    if not (lower * (1 << candidate) >= 1 and upper * (1 << (candidate - 1)) < 1):
        raise AssertionError("dyadic enclosure does not certify binary depth")
    return candidate


def forced_proper_load(rank: int, forcing_rank: int, bits: list[int]) -> int:
    """Proper-divisor load of actual-prefix + forced digit + terminal zeros."""
    total = 0
    for divisor in range(1, isqrt(rank) + 1):
        if rank % divisor:
            continue
        partner = rank // divisor
        for candidate in {divisor, partner}:
            if candidate == rank:
                continue
            selected = (
                (candidate < forcing_rank and bits[candidate] == 1)
                or candidate == forcing_rank
            )
            total += int(selected)
    return total


def forced_one_zero_continuation_audit(depth: int, lookahead: int) -> dict[str, object]:
    bits, before_lower, before_upper, scale = actual_greedy_enclosure(depth)
    states = orbit_states(bits)
    prefix = states["prefix"]
    source = states["source"]
    divisor_load = states["divisor_load"]
    defect = states["defect"]
    sharper = states["sharper"]

    minimum_barrier: tuple[int, dict[str, int]] | None = None
    minimum_skipped_clearance: tuple[int, dict[str, int]] | None = None
    largest_depth_excess: tuple[int, dict[str, int]] | None = None
    skipped_crossings: list[dict[str, int]] = []
    selected_without_crossing: list[int] = []
    maximum_selected_first_crossing = (0, 0)
    lower_sheet_seam_count = 0
    upper_sliver_seam_count = 0
    half_scale_crossing_run_count = 0
    longest_run_relative_to_start = (0.0, 0, 0)
    most_negative_barrier_increment: tuple[int, dict[str, int]] | None = None
    negative_barrier_increment_count = 0
    negative_increment_without_divisor_payment_count = 0
    zero_barrier_step_count = 0
    minimum_after_zero_barrier: tuple[int, dict[str, int]] | None = None

    for rank in range(2, depth):
        proper_load = divisor_load[rank] - bits[rank]
        forced_defect = (
            2 * defect[rank - 1] + source_bit(rank) - proper_load - 1
        )
        forced_p = source[rank] + prefix[rank // 2] - (prefix[rank - 1] + 1)
        forced_f = forced_p + 4 - 2 * forced_defect

        delta_lower: Fraction | None = None
        delta_upper: Fraction | None = None
        binary_depth: int | None = None
        if bits[rank] == 0:
            delta_lower, delta_upper = exact_delta_bounds(
                rank, before_lower[rank], before_upper[rank], scale
            )
            if rank + 1 <= depth and bits[rank + 1] == 1:
                # Every observed seam start lies on the lower sheet Y<1.
                y_upper = Fraction((1 << rank) * before_upper[rank], scale)
                if y_upper < 1:
                    lower_sheet_seam_count += 1
                    binary_depth = exact_binary_depth(delta_lower, delta_upper)
                else:
                    upper_sliver_seam_count += 1
                    # No upper-sliver seam occurs in the audited orbit.  The
                    # binary-depth statistic is defined only on the lower sheet.
                    continue
                receipt = {
                    "rank": rank,
                    "binary_depth": binary_depth,
                    "F_before": sharper[rank - 1],
                    "depth_minus_F_before": binary_depth - sharper[rank - 1],
                }
                score = receipt["depth_minus_F_before"]
                if largest_depth_excess is None or score > largest_depth_excess[0]:
                    largest_depth_excess = (score, receipt)

        first_crossing: int | None = None
        forced_q = forced_defect
        forced_f_at_rank = forced_f
        previous_q = forced_q
        previous_ceiling: int | None = None
        previous_barrier: int | None = None
        if bits[rank] == 0:
            assert delta_lower is not None and delta_upper is not None
            initial_ceiling_lower = ceil_fraction(delta_lower)
            initial_ceiling_upper = ceil_fraction(delta_upper)
            if initial_ceiling_lower != initial_ceiling_upper:
                raise AssertionError(f"initial excess ceiling not certified at rank={rank}")
            previous_ceiling = initial_ceiling_lower
            previous_barrier = forced_f - initial_ceiling_lower
        upper_k = min(lookahead, depth - rank)
        for offset in range(1, upper_k + 1):
            horizon = rank + offset
            if horizon < 2 * rank:
                # Every proper divisor is below the forcing rank.  Remove
                # only the actual endpoint bit from the precomputed load.
                proper_load = divisor_load[horizon] - bits[horizon]
            else:
                proper_load = forced_proper_load(horizon, rank, bits)
            forced_q = (
                2 * forced_q
                + source_bit(horizon)
                - proper_load
            )
            half = horizon // 2
            forced_half_count = prefix[min(half, rank - 1)] + int(rank <= half)
            forced_p = (
                source[horizon]
                + forced_half_count
                - (prefix[rank - 1] + 1)
            )
            forced_f = forced_p + 4 - 2 * forced_q
            clearance = forced_f - offset
            receipt = {
                "rank": rank,
                "offset": offset,
                "horizon": horizon,
                "F_alt": forced_f,
                "clearance_F_alt_minus_k": clearance,
                "Q_alt": forced_q,
                "actual_bit_at_rank": bits[rank],
            }
            if bits[rank] == 0:
                assert delta_lower is not None and delta_upper is not None
                scaled_lower = (1 << offset) * delta_lower
                scaled_upper = (1 << offset) * delta_upper
                ceiling_lower = ceil_fraction(scaled_lower)
                ceiling_upper = ceil_fraction(scaled_upper)
                if ceiling_lower != ceiling_upper:
                    raise AssertionError(
                        f"excess ceiling not certified at rank={rank}, k={offset}"
                    )
                barrier = clearance - ceiling_lower
                barrier_receipt = dict(receipt)
                barrier_receipt.update(
                    {
                        "ceil_2_pow_k_Delta": ceiling_lower,
                        "barrier": barrier,
                    }
                )
                if minimum_barrier is None or barrier < minimum_barrier[0]:
                    minimum_barrier = (barrier, barrier_receipt)
                if (
                    minimum_skipped_clearance is None
                    or clearance < minimum_skipped_clearance[0]
                ):
                    minimum_skipped_clearance = (clearance, barrier_receipt)
                if clearance <= 0:
                    skipped_crossings.append(barrier_receipt)

                assert previous_ceiling is not None and previous_barrier is not None
                phase_half_payment = 2 * previous_ceiling - ceiling_lower
                if phase_half_payment not in (0, 1):
                    raise AssertionError(
                        f"non-Boolean phase payment at rank={rank}, k={offset}"
                    )
                half_bit = (
                    bits[half]
                    if half < rank
                    else int(half == rank)
                ) if horizon % 2 == 0 else 0
                winding_before = previous_q + previous_ceiling
                predicted_increment = (
                    2 * proper_load
                    + half_bit
                    + phase_half_payment
                    - (
                        previous_q
                        + winding_before
                        + source_bit(horizon)
                        + 1
                    )
                )
                actual_increment = barrier - previous_barrier
                if predicted_increment != actual_increment:
                    raise AssertionError(
                        f"barrier recurrence failed at rank={rank}, k={offset}"
                    )
                if actual_increment < 0:
                    negative_barrier_increment_count += 1
                    if proper_load == 0 and half_bit == 0:
                        negative_increment_without_divisor_payment_count += 1
                    increment_receipt = {
                        "rank": rank,
                        "offset": offset,
                        "horizon": horizon,
                        "increment": actual_increment,
                        "H_before": previous_barrier,
                        "H_after": barrier,
                        "Q_before": previous_q,
                        "phase_winding_before": winding_before,
                        "proper_divisor_load": proper_load,
                        "self_double_bit": half_bit,
                        "phase_half_payment": phase_half_payment,
                        "source_bit": source_bit(horizon),
                    }
                    if (
                        most_negative_barrier_increment is None
                        or actual_increment < most_negative_barrier_increment[0]
                    ):
                        most_negative_barrier_increment = (
                            actual_increment, increment_receipt
                        )
                if previous_barrier == 0:
                    zero_barrier_step_count += 1
                    zero_receipt = {
                        "rank": rank,
                        "offset": offset,
                        "horizon": horizon,
                        "H_after": barrier,
                        "proper_divisor_load": proper_load,
                        "self_double_bit": half_bit,
                        "phase_half_payment": phase_half_payment,
                        "source_bit": source_bit(horizon),
                    }
                    if (
                        minimum_after_zero_barrier is None
                        or barrier < minimum_after_zero_barrier[0]
                    ):
                        minimum_after_zero_barrier = (barrier, zero_receipt)
                previous_q = forced_q
                previous_ceiling = ceiling_lower
                previous_barrier = barrier
            elif first_crossing is None and clearance <= 0:
                first_crossing = offset

        if bits[rank] == 1:
            if first_crossing is None and upper_k == lookahead:
                selected_without_crossing.append(rank)
            elif first_crossing is not None:
                maximum_selected_first_crossing = max(
                    maximum_selected_first_crossing, (first_crossing, -rank)
                )

        # Check the pulse-eliminated endpoint identity on every actual seam
        # whose complete following run lies in the audited range.
        if bits[rank] == 0 and rank + 1 <= depth and bits[rank + 1] == 1:
            run = 1
            while rank + run + 1 <= depth and bits[rank + run + 1] == 1:
                run += 1
            longest_run_relative_to_start = max(
                longest_run_relative_to_start, (run / rank, -rank, run)
            )
            if run >= rank:
                half_scale_crossing_run_count += 1
            if run < rank and run <= upper_k:
                q_alt = forced_defect
                tau = 0
                sigma = 0
                for offset in range(1, run + 1):
                    horizon = rank + offset
                    q_alt = (
                        2 * q_alt
                        + source_bit(horizon)
                        - (divisor_load[horizon] - bits[horizon])
                    )
                    tau += source_bit(horizon)
                    if horizon % 2 == 0:
                        sigma += bits[horizon // 2]
                predicted_actual_f = (
                    sharper[rank]
                    - 2
                    + 2 * (defect[rank] - q_alt)
                    + tau
                    + sigma
                    - run
                )
                if predicted_actual_f != sharper[rank + run]:
                    raise AssertionError(
                        f"block telescope failed at rank={rank}, run={run}"
                    )

    if (
        minimum_barrier is None
        or minimum_skipped_clearance is None
        or largest_depth_excess is None
    ):
        raise AssertionError("audit range too small")

    # Exact rational regression for the same-cylinder counterexample.
    target_minus = Fraction(1, 21) - Fraction(1, 3 * (1 << 63))
    remainder = target_minus
    minus_bits = [0] * 64
    before_61 = Fraction(0)
    for rank in range(1, 64):
        if rank == 61:
            before_61 = remainder
        weight = Fraction(1, (1 << rank) - 1)
        if weight <= remainder:
            minus_bits[rank] = 1
            remainder -= weight
    minus_states = orbit_states(minus_bits)
    if minus_bits[61:64] != [0, 1, 1]:
        raise AssertionError("same-cylinder regression no longer has block 011")
    delta_minus = Fraction(1 << 61, (1 << 61) - 1) - (1 << 61) * before_61
    forced_word = minus_bits[:61] + [1, 0, 0]
    forced_states = orbit_states(forced_word)
    f_alt_minus = forced_states["sharper"][63]
    minus_barrier = f_alt_minus - 2 - ceil_fraction(4 * delta_minus)
    if (f_alt_minus, minus_states["sharper"][63], minus_barrier) != (2, -1, -1):
        raise AssertionError("same-cylinder barrier regression changed")

    prefix_phase_denominator = 21
    for rank in range(1, 61):
        if bits[rank]:
            prefix_phase_denominator = lcm(
                prefix_phase_denominator, (1 << rank) - 1
            )

    return {
        "depth": depth,
        "lookahead": lookahead,
        "minimum_exact_phase_winding_barrier": minimum_barrier[1],
        "minimum_skipped_unrounded_clearance": minimum_skipped_clearance[1],
        "largest_binary_depth_minus_previous_F_on_seam_starts": largest_depth_excess[1],
        "lower_sheet_seam_starts": lower_sheet_seam_count,
        "upper_sliver_seam_starts": upper_sliver_seam_count,
        "half_scale_crossing_actual_runs": half_scale_crossing_run_count,
        "largest_actual_run_to_start_ratio": {
            "rank": -longest_run_relative_to_start[1],
            "run_length": longest_run_relative_to_start[2],
            "ratio": longest_run_relative_to_start[0],
        },
        "negative_barrier_increment_count": negative_barrier_increment_count,
        "negative_increment_without_divisor_or_self_double_payment_count": (
            negative_increment_without_divisor_payment_count
        ),
        "most_negative_barrier_increment": (
            None
            if most_negative_barrier_increment is None
            else most_negative_barrier_increment[1]
        ),
        "zero_barrier_step_count": zero_barrier_step_count,
        "minimum_after_zero_barrier": (
            None
            if minimum_after_zero_barrier is None
            else minimum_after_zero_barrier[1]
        ),
        "skipped_ranks_with_nonpositive_clearance": skipped_crossings,
        "selected_ranks_without_a_nonpositive_clearance_within_lookahead": selected_without_crossing,
        "maximum_first_crossing_lag_for_selected_ranks": {
            "lag": maximum_selected_first_crossing[0],
            "first_rank": -maximum_selected_first_crossing[1],
        },
        "same_cylinder_x_minus": {
            "block_61_to_63": "011",
            "F_alt_at_63": f_alt_minus,
            "actual_F_at_63": minus_states["sharper"][63],
            "ceil_4_Delta": ceil_fraction(4 * delta_minus),
            "barrier": minus_barrier,
        },
        "rank_61_naive_lcm_spacing": {
            "prefix_through_rank": 60,
            "common_denominator_bit_length": prefix_phase_denominator.bit_length(),
            "seam_run_length_in_counterexample": 2,
        },
        "claim_status": "exact finite audit only; the all-depth barrier is conjectural",
    }


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--depth", type=int, default=10000)
    parser.add_argument("--lookahead", type=int, default=64)
    args = parser.parse_args()
    if args.depth < 64:
        raise SystemExit("--depth must be at least 64")
    print(json.dumps(forced_one_zero_continuation_audit(args.depth, args.lookahead), indent=2))


if __name__ == "__main__":
    main()
