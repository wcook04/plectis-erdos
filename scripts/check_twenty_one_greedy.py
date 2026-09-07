#!/usr/bin/env python3
"""Exact interval certificates for the 1/21 Mersenne itinerary.

The computation uses integer enclosures at a fixed dyadic precision.  It
never decides a branch from floating point.  Besides certifying the greedy
digits, it checks the strict dyadic remainder cap and reconstructs the exact
denominator-21 Lambert carry from divisor counts.

It also runs a second, independent exact calculation.  Write

    1 / (2^n - 1) = 2^-n + epsilon_n.

If a support word ``p`` has length ``K``, every continuation has correction
in the interval formed by its exact prefix correction plus
``[0, 2 / (3 * 4^K)]``.  Subtracting this interval from ``1/21`` produces a
binary cylinder.  Starting from ``00001``, those cylinders force strictly
longer words; all interval endpoints and containment tests use
``fractions.Fraction``.

Both calculations are finite evidence, not an infinite-membership proof.
The Lean endpoints in ``BooleanMobiusCarry.lean`` consume either an all-depth
carry bound or an unbounded correction-prefix forcing chain.

A third exact calculation replays the even-depth quotient recurrence from
``TwentyOneQuotientGreedy.lean``.  At transition ``R -> R+1`` it uses only
the selected-divisor pulse at ``2R+1, 2R+2`` and the scalar lower state.
The predicted boundary bit is checked against the independently certified
rational greedy bit.  Closed capacity, cardinality domination, and the weak
preterminal core bound are audited at every replayed depth.  It also
completes each lower state by the exact binary suffix at ranks
``R+1,...,2R``.  In the certified range every lower state is strictly below
``2^R``, so every complete quotient row has terminal defect exactly zero.
"""

from __future__ import annotations

import argparse
import hashlib
import json
from dataclasses import dataclass
from fractions import Fraction


@dataclass(frozen=True)
class Receipt:
    ranks: int
    precision_bits: int
    selected_digits: int
    skipped_digits: int
    last_skipped_rank: int
    max_selected_run: int
    max_selected_run_start: int
    max_selected_run_end: int
    max_skipped_run: int
    max_skipped_run_start: int
    max_skipped_run_end: int
    empty_doubling_blocks: tuple[int, ...]
    doubling_block_hit_verified_from: int
    doubling_block_hit_verified_through: int
    max_lambert_defect: int
    first_max_lambert_defect_rank: int
    floor_six_defect_bound_verified: bool
    defect_zero_return_count: int
    defect_last_zero_return_rank: int | None
    defect_le_one_return_count: int
    defect_last_le_one_return_rank: int | None
    defect_le_one_max_observed_gap: int
    six_step_contraction_failure_count: int
    first_six_step_contraction_failure_rank: int | None
    first_six_step_contraction_failure_start_defect: int | None
    first_six_step_contraction_failure_end_defect: int | None
    six_step_max_defect_increment: int
    shortest_verified_floor_slope_block_length: int | None
    shortest_verified_floor_slope_block_increment: int | None
    shortest_verified_floor_slope_block_max_observed_increment: int | None
    slope_danger_rank_count: int
    slope_danger_last_rank: int | None
    slope_danger_repair_failure_count: int
    slope_danger_high_defect_localization_verified: bool
    min_relative_margin_numerator_bits: int
    min_relative_margin_numerator_sha256: str
    min_relative_margin_denominator_power: int
    min_relative_margin_rank: int
    uniform_relative_margin_bits: int
    itinerary_sha256: str
    correction_seed_depth: int
    correction_requested_depth: int
    correction_certified_depth: int
    correction_prefix_depths: tuple[int, ...]
    correction_crossed_boundary_valuations: tuple[int, ...]
    correction_crossed_boundary_count: int
    correction_max_crossed_boundary_valuation: int
    correction_valuation_le_one_observed: bool
    correction_minimum_uncapped_depth_gain: int
    correction_strict_amplification_verified: bool
    correction_prefix_matches_greedy: bool
    correction_dyadic_residual_identity_verified: bool
    correction_fraction_audit_depth: int
    correction_prefix_sha256: str
    quotient_recurrence_matches_greedy: bool
    quotient_closed_state_verified: bool
    quotient_weak_core_bound_verified: bool
    quotient_cardinality_state_verified: bool
    quotient_strict_closed_state_verified: bool
    quotient_full_terminal_zero_verified: bool
    quotient_full_terminal_defect_max: int
    quotient_full_terminal_nonzero_count: int
    quotient_saturated_state_count: int
    quotient_min_take_cardinality_gap: int
    quotient_min_take_cardinality_gap_rank: int
    quotient_min_closed_capacity_margin: int
    quotient_min_closed_capacity_margin_rank: int


def mersenne_dyadic_correction(n: int) -> Fraction:
    """Return 1/(2^n-1) - 2^-n exactly."""

    power = 1 << n
    return Fraction(1, power * (power - 1))


def correction_tail_upper_bound(depth: int) -> Fraction:
    """Strict upper bound for sum_{n>depth} epsilon_n.

    Since ``epsilon_n < 2 / 4^n``, the geometric tail is
    ``2 / (3 * 4^depth)``.
    """

    return Fraction(2, 3 * (1 << (2 * depth)))


def largest_trapped_dyadic_cell(
    lower: Fraction, upper: Fraction, max_depth: int
) -> tuple[int, int]:
    """Largest tested dyadic cell strictly containing ``[lower, upper]``.

    The returned integer is the cell numerator.  Strictness at the right
    endpoint makes its length-``depth`` binary word canonical.
    """

    if not 0 <= lower <= upper < 1:
        raise AssertionError("correction image left the unit interval")
    best_depth = 0
    best_numerator = 0
    for depth in range(1, max_depth + 1):
        scale = 1 << depth
        numerator = (lower.numerator * scale) // lower.denominator
        if upper < Fraction(numerator + 1, scale):
            best_depth = depth
            best_numerator = numerator
        else:
            break
    return best_depth, best_numerator


def two_adic_valuation(value: int) -> int:
    """Return the exact 2-adic valuation of a nonzero integer."""

    if value == 0:
        raise ValueError("two-adic valuation is undefined at zero")
    absolute = abs(value)
    return (absolute & -absolute).bit_length() - 1


def integers_in_closed_interval(
    lower: Fraction, upper: Fraction
) -> tuple[int, ...]:
    """Return all integers in a rational closed interval."""

    first = -((-lower.numerator) // lower.denominator)
    last = upper.numerator // upper.denominator
    if first > last:
        return ()
    return tuple(range(first, last + 1))


def correction_prefix_certificate_fraction(
    requested_depth: int,
) -> tuple[tuple[int, ...], str, tuple[int, ...]]:
    """Reference implementation using direct rational correction sums.

    This implementation is deliberately retained as a bounded audit oracle.
    Its denominator grows as a product of Mersenne factors, so it must not be
    used for the long certificate itself.
    """

    if requested_depth < 5:
        raise ValueError("correction certificate requires depth at least five")

    prefix = "00001"
    depths = [len(prefix)]
    crossing_valuations: list[int] = []
    while len(prefix) < requested_depth:
        prefix_correction = sum(
            (
                mersenne_dyadic_correction(n)
                for n, bit in enumerate(prefix, start=1)
                if bit == "1"
            ),
            Fraction(0),
        )
        uncertainty = correction_tail_upper_bound(len(prefix))
        lower = Fraction(1, 21) - prefix_correction - uncertainty
        upper = Fraction(1, 21) - prefix_correction
        scaled_crossings = integers_in_closed_interval(
            lower * (1 << (2 * len(prefix))),
            upper * (1 << (2 * len(prefix))),
        )
        if len(scaled_crossings) > 1:
            raise AssertionError(
                f"more than one crossed boundary at depth {len(prefix)}"
            )
        crossing_valuations.append(
            -1
            if not scaled_crossings
            else two_adic_valuation(scaled_crossings[0])
        )
        search_depth = min(requested_depth, 2 * len(prefix) + 8)
        depth, numerator = largest_trapped_dyadic_cell(
            lower, upper, search_depth
        )
        if depth <= len(prefix):
            raise AssertionError(
                f"correction prefix failed to amplify at depth {len(prefix)}"
            )
        next_prefix = format(numerator, f"0{depth}b")
        if not next_prefix.startswith(prefix):
            raise AssertionError(
                f"correction prefix changed before depth {len(prefix)}"
            )
        prefix = next_prefix
        depths.append(depth)

    return tuple(depths), prefix, tuple(crossing_valuations)


def correction_prefix_certificate_from_residual(
    requested_depth: int,
    precision_bits: int,
    residual_lowers: list[int],
    residual_uppers: list[int],
    greedy_bits: list[str],
) -> tuple[tuple[int, ...], str, tuple[int, ...]]:
    """Iterate correction enclosures using the certified greedy residual.

    If ``P_K`` is the length-``K`` binary prefix numeral and ``R_K`` is the
    Mersenne greedy residual, then

        1/21 - correction(prefix K) = P_K / 2^K + R_K.

    Thus the old product-denominator correction sum can be replaced by the
    already-certified dyadic enclosure for ``R_K``.  The only remaining
    rational denominator is ``3 * 2^precision_bits`` from the geometric
    correction-tail bound.
    """

    if requested_depth < 5:
        raise ValueError("correction certificate requires depth at least five")
    if len(residual_lowers) <= requested_depth:
        raise ValueError("residual lower-bound table is too short")
    if len(residual_uppers) <= requested_depth:
        raise ValueError("residual upper-bound table is too short")
    if len(greedy_bits) < requested_depth:
        raise ValueError("greedy itinerary is too short")

    scale = 1 << precision_bits
    prefix = "00001"
    if prefix != "".join(greedy_bits[: len(prefix)]):
        raise AssertionError("correction seed disagrees with greedy itinerary")
    depths = [len(prefix)]
    crossing_valuations: list[int] = []
    while len(prefix) < requested_depth:
        depth_now = len(prefix)
        prefix_numerator = int(prefix, 2)
        binary_prefix = Fraction(prefix_numerator, 1 << depth_now)
        lower = (
            binary_prefix
            + Fraction(residual_lowers[depth_now], scale)
            - correction_tail_upper_bound(depth_now)
        )
        upper = (
            binary_prefix
            + Fraction(residual_uppers[depth_now], scale)
        )
        scaled_crossings = integers_in_closed_interval(
            lower * (1 << (2 * depth_now)),
            upper * (1 << (2 * depth_now)),
        )
        if len(scaled_crossings) > 1:
            raise AssertionError(
                f"more than one crossed boundary at depth {depth_now}"
            )
        crossing_valuations.append(
            -1
            if not scaled_crossings
            else two_adic_valuation(scaled_crossings[0])
        )
        search_depth = min(requested_depth, 2 * depth_now + 8)
        depth, numerator = largest_trapped_dyadic_cell(
            lower, upper, search_depth
        )
        if depth <= depth_now:
            raise AssertionError(
                f"correction prefix failed to amplify at depth {depth_now}"
            )
        next_prefix = format(numerator, f"0{depth}b")
        if not next_prefix.startswith(prefix):
            raise AssertionError(
                f"correction prefix changed before depth {depth_now}"
            )
        if next_prefix != "".join(greedy_bits[:depth]):
            raise AssertionError(
                f"correction prefix disagrees with greedy itinerary at {depth}"
            )
        prefix = next_prefix
        depths.append(depth)

    return tuple(depths), prefix, tuple(crossing_valuations)


def mersenne_weight_floor_scaled(precision_bits: int, n: int) -> int:
    """Return floor(2^P / (2^n - 1)) exactly."""

    return (1 << precision_bits) // ((1 << n) - 1)


def certify(
    ranks: int, precision_bits: int, correction_depth: int | None = None
) -> Receipt:
    if ranks < 5:
        raise ValueError("ranks must be at least five")
    if precision_bits < 2 * ranks + 32:
        raise ValueError("precision must be at least 2*ranks + 32")
    requested_correction_depth = (
        ranks if correction_depth is None else correction_depth
    )
    if not 5 <= requested_correction_depth <= ranks:
        raise ValueError("correction depth must lie between five and ranks")

    scale = 1 << precision_bits
    lower = scale // 21
    upper = (scale + 20) // 21
    residual_lowers = [lower]
    residual_uppers = [upper]
    divisor_counts = [0] * (ranks + 1)
    quotient_divisor_counts = [0] * (2 * ranks + 3)
    itinerary = bytearray((ranks + 7) // 8)
    greedy_bits: list[str] = []

    selected = 0
    last_skipped_rank = 0
    current_selected_run = 0
    current_selected_run_start = 0
    max_selected_run = 0
    max_selected_run_start = 0
    max_selected_run_end = 0
    current_skipped_run = 0
    current_skipped_run_start = 0
    max_skipped_run = 0
    max_skipped_run_start = 0
    max_skipped_run_end = 0
    selected_prefix_counts = [0]
    carry = 1
    periodic_remainder = 1
    max_defect = 0
    first_max_rank = 0
    lambert_defects = [0]
    min_margin: int | None = None
    min_margin_denominator_power = 0
    min_margin_rank = 0
    quotient_state = 0
    quotient_selected = 0
    quotient_saturated_state_count = 0
    quotient_full_terminal_defect_max = 0
    quotient_full_terminal_nonzero_count = 0
    quotient_min_take_cardinality_gap: int | None = None
    quotient_min_take_cardinality_gap_rank = 0
    quotient_min_closed_capacity_margin: int | None = None
    quotient_min_closed_capacity_margin_rank = 0

    for n in range(1, ranks + 1):
        quotient_predicted_selected = False
        quotient_next_state = 0
        if n >= 2:
            previous_rank = n - 1
            quotient_pulse = (
                2 * quotient_divisor_counts[2 * previous_rank + 1]
                + quotient_divisor_counts[2 * previous_rank + 2]
            )
            target_pulse = (
                4 * pow(2, 2 * previous_rank, 21)
            ) // 21
            quotient_core = (
                4 * quotient_state + target_pulse - quotient_pulse
            )
            if quotient_core < 0:
                raise AssertionError(
                    f"quotient pulse exceeded the carry at rank {n}"
                )
            quotient_coin = (1 << n) + 1
            quotient_predicted_selected = quotient_coin <= quotient_core
            quotient_next_state = (
                quotient_core - quotient_coin
                if quotient_predicted_selected
                else quotient_core
            )
            closed_capacity = 1 << n
            if quotient_next_state > closed_capacity:
                raise AssertionError(
                    f"closed quotient state failed at rank {n}"
                )
            if quotient_core > 2 * closed_capacity + 1:
                raise AssertionError(
                    f"weak quotient core bound failed at rank {n}"
                )
            capacity_margin = closed_capacity - quotient_next_state
            if (
                quotient_min_closed_capacity_margin is None
                or capacity_margin < quotient_min_closed_capacity_margin
            ):
                quotient_min_closed_capacity_margin = capacity_margin
                quotient_min_closed_capacity_margin_rank = n
            if quotient_predicted_selected:
                take_gap = quotient_next_state - (quotient_selected + 1)
                if take_gap < 0:
                    raise AssertionError(
                        f"quotient cardinality state failed at rank {n}"
                    )
                if (
                    quotient_min_take_cardinality_gap is None
                    or take_gap < quotient_min_take_cardinality_gap
                ):
                    quotient_min_take_cardinality_gap = take_gap
                    quotient_min_take_cardinality_gap_rank = n

        weight_floor = mersenne_weight_floor_scaled(precision_bits, n)

        if lower >= weight_floor + 1:
            selected_now = True
            itinerary[(n - 1) // 8] |= 1 << ((n - 1) % 8)
            selected += 1
            if current_selected_run == 0:
                current_selected_run_start = n
            current_selected_run += 1
            if current_selected_run > max_selected_run:
                max_selected_run = current_selected_run
                max_selected_run_start = current_selected_run_start
                max_selected_run_end = n
            current_skipped_run = 0
            lower -= weight_floor + 1
            upper -= weight_floor
            for multiple in range(n, ranks + 1, n):
                divisor_counts[multiple] += 1
            greedy_bits.append("1")
        elif upper <= weight_floor:
            selected_now = False
            last_skipped_rank = n
            current_selected_run = 0
            if current_skipped_run == 0:
                current_skipped_run_start = n
            current_skipped_run += 1
            if current_skipped_run > max_skipped_run:
                max_skipped_run = current_skipped_run
                max_skipped_run_start = current_skipped_run_start
                max_skipped_run_end = n
            greedy_bits.append("0")
        else:
            raise AssertionError(
                f"ambiguous greedy branch at rank {n}; increase precision"
            )
        if n == 1 and selected_now:
            raise AssertionError("rank one unexpectedly entered the support")
        if n >= 2:
            if selected_now != quotient_predicted_selected:
                raise AssertionError(
                    "quotient recurrence disagreed with rational greedy "
                    f"at rank {n}"
                )
            quotient_state = quotient_next_state
            if selected_now:
                quotient_selected += 1
                for multiple in range(n, 2 * ranks + 3, n):
                    quotient_divisor_counts[multiple] += 1
            if quotient_selected > quotient_state:
                raise AssertionError(
                    f"quotient cardinality state failed at rank {n}"
                )
            if quotient_state == 1 << n:
                quotient_saturated_state_count += 1
            # Ranks n+1,...,2n are the complete binary word
            # 2^(n-1),...,1.  Under the checked closed bound its terminal
            # defect is therefore one precisely at the saturated state
            # 2^n, and zero everywhere else.
            quotient_full_terminal_defect = int(
                quotient_state == 1 << n
            )
            quotient_full_terminal_defect_max = max(
                quotient_full_terminal_defect_max,
                quotient_full_terminal_defect,
            )
            quotient_full_terminal_nonzero_count += (
                quotient_full_terminal_defect
            )
        residual_lowers.append(lower)
        residual_uppers.append(upper)
        selected_prefix_counts.append(selected)

        cap_power = precision_bits - n
        cap = 1 << cap_power
        if upper >= cap:
            raise AssertionError(f"strict dyadic cap failed at rank {n}")
        margin = cap - upper
        if cap_power >= 21 and margin < (1 << (cap_power - 21)):
            raise AssertionError(f"uniform 2^-21 relative margin failed at rank {n}")
        if (
            min_margin is None
            or (margin << min_margin_denominator_power)
            < (min_margin << cap_power)
        ):
            min_margin = margin
            min_margin_denominator_power = cap_power
            min_margin_rank = n

        carry = 2 * carry - 21 * divisor_counts[n]
        if carry < 0:
            raise AssertionError(f"denominator-21 carry negative at rank {n}")

        bit = 1 if n % 6 in (0, 5) else 0
        periodic_remainder = 2 * periodic_remainder - 21 * bit
        defect, remainder = divmod(carry - periodic_remainder, 21)
        if remainder:
            raise AssertionError(f"nonintegral Lambert defect at rank {n}")
        if defect < 0:
            raise AssertionError(f"Lambert defect negative at rank {n}")
        if defect > max_defect:
            max_defect = defect
            first_max_rank = n
        if defect > n // 6:
            raise AssertionError(f"sharp floor(n/6) carry bound failed at rank {n}")
        lambert_defects.append(defect)

    assert min_margin is not None
    assert quotient_min_take_cardinality_gap is not None
    assert quotient_min_closed_capacity_margin is not None
    if quotient_full_terminal_nonzero_count:
        raise AssertionError(
            "a complete quotient row retained nonzero terminal defect"
        )
    six_step_failures = tuple(
        n
        for n in range(ranks - 5)
        if lambert_defects[n + 6] > lambert_defects[n] + 1
    )
    defect_zero_return_ranks = tuple(
        n for n in range(1, ranks + 1) if lambert_defects[n] == 0
    )
    defect_le_one_return_ranks = tuple(
        n for n in range(1, ranks + 1) if lambert_defects[n] <= 1
    )
    defect_le_one_max_observed_gap = max(
        (
            right - left
            for left, right in zip(
                defect_le_one_return_ranks,
                defect_le_one_return_ranks[1:],
            )
        ),
        default=0,
    )
    first_six_step_failure = (
        six_step_failures[0] if six_step_failures else None
    )
    six_step_max_increment = max(
        (
            lambert_defects[n + 6] - lambert_defects[n]
            for n in range(ranks - 5)
        ),
        default=0,
    )
    shortest_verified_floor_slope_block: tuple[int, int, int] | None = None
    for block_length in range(6, ranks // 2 + 1, 6):
        allowed_increment = block_length // 6
        max_observed_increment = max(
            lambert_defects[n + block_length] - lambert_defects[n]
            for n in range(ranks - block_length + 1)
        )
        if max_observed_increment <= allowed_increment:
            shortest_verified_floor_slope_block = (
                block_length,
                allowed_increment,
                max_observed_increment,
            )
            break
    slope_danger_ranks: list[int] = []
    slope_danger_repair_failures: list[int] = []
    for n in range(ranks - 5):
        periodic_charge = 3 * pow(2, n, 21)
        slope_allowance = n // 6 + 1
        amplified_defect = 64 * lambert_defects[n] + periodic_charge
        if slope_allowance < amplified_defect:
            slope_danger_ranks.append(n)
            repair_load = (
                32 * divisor_counts[n + 1]
                + 16 * divisor_counts[n + 2]
                + 8 * divisor_counts[n + 3]
                + 4 * divisor_counts[n + 4]
                + 2 * divisor_counts[n + 5]
                + divisor_counts[n + 6]
            )
            if amplified_defect > repair_load + slope_allowance:
                slope_danger_repair_failures.append(n)
            if n >= 384 * lambert_defects[n] + 354:
                raise AssertionError(
                    f"slope-danger localization failed at rank {n}"
                )
    (
        correction_depths,
        correction_prefix,
        correction_crossing_valuations,
    ) = correction_prefix_certificate_from_residual(
        requested_correction_depth,
        precision_bits,
        residual_lowers,
        residual_uppers,
        greedy_bits,
    )
    fraction_audit_depth = min(requested_correction_depth, 75)
    (
        audit_depths,
        audit_prefix,
        audit_crossing_valuations,
    ) = correction_prefix_certificate_fraction(fraction_audit_depth)
    if (
        correction_depths[: len(audit_depths)] != audit_depths
        or correction_prefix[: len(audit_prefix)] != audit_prefix
        or correction_crossing_valuations[: len(audit_crossing_valuations)]
        != audit_crossing_valuations
    ):
        raise AssertionError(
            "dyadic-residual correction certificate disagrees with "
            "the direct Fraction audit"
        )
    correction_matches_greedy = (
        correction_prefix
        == "".join(greedy_bits[: len(correction_prefix)])
    )
    if not correction_matches_greedy:
        raise AssertionError("correction prefix disagrees with greedy itinerary")
    doubling_block_limit = ranks // 2
    empty_doubling_blocks = tuple(
        depth
        for depth in range(1, doubling_block_limit + 1)
        if selected_prefix_counts[2 * depth] == selected_prefix_counts[depth]
    )
    doubling_block_hit_verified_from = (
        max(empty_doubling_blocks, default=0) + 1
    )
    margin_bytes = min_margin.to_bytes((min_margin.bit_length() + 7) // 8, "big")
    return Receipt(
        ranks=ranks,
        precision_bits=precision_bits,
        selected_digits=selected,
        skipped_digits=ranks - selected,
        last_skipped_rank=last_skipped_rank,
        max_selected_run=max_selected_run,
        max_selected_run_start=max_selected_run_start,
        max_selected_run_end=max_selected_run_end,
        max_skipped_run=max_skipped_run,
        max_skipped_run_start=max_skipped_run_start,
        max_skipped_run_end=max_skipped_run_end,
        empty_doubling_blocks=empty_doubling_blocks,
        doubling_block_hit_verified_from=doubling_block_hit_verified_from,
        doubling_block_hit_verified_through=doubling_block_limit,
        max_lambert_defect=max_defect,
        first_max_lambert_defect_rank=first_max_rank,
        floor_six_defect_bound_verified=True,
        defect_zero_return_count=len(defect_zero_return_ranks),
        defect_last_zero_return_rank=(
            defect_zero_return_ranks[-1]
            if defect_zero_return_ranks
            else None
        ),
        defect_le_one_return_count=len(defect_le_one_return_ranks),
        defect_last_le_one_return_rank=(
            defect_le_one_return_ranks[-1]
            if defect_le_one_return_ranks
            else None
        ),
        defect_le_one_max_observed_gap=defect_le_one_max_observed_gap,
        six_step_contraction_failure_count=len(six_step_failures),
        first_six_step_contraction_failure_rank=first_six_step_failure,
        first_six_step_contraction_failure_start_defect=(
            None
            if first_six_step_failure is None
            else lambert_defects[first_six_step_failure]
        ),
        first_six_step_contraction_failure_end_defect=(
            None
            if first_six_step_failure is None
            else lambert_defects[first_six_step_failure + 6]
        ),
        six_step_max_defect_increment=six_step_max_increment,
        shortest_verified_floor_slope_block_length=(
            None
            if shortest_verified_floor_slope_block is None
            else shortest_verified_floor_slope_block[0]
        ),
        shortest_verified_floor_slope_block_increment=(
            None
            if shortest_verified_floor_slope_block is None
            else shortest_verified_floor_slope_block[1]
        ),
        shortest_verified_floor_slope_block_max_observed_increment=(
            None
            if shortest_verified_floor_slope_block is None
            else shortest_verified_floor_slope_block[2]
        ),
        slope_danger_rank_count=len(slope_danger_ranks),
        slope_danger_last_rank=(
            slope_danger_ranks[-1] if slope_danger_ranks else None
        ),
        slope_danger_repair_failure_count=len(
            slope_danger_repair_failures
        ),
        slope_danger_high_defect_localization_verified=True,
        min_relative_margin_numerator_bits=min_margin.bit_length(),
        min_relative_margin_numerator_sha256=hashlib.sha256(margin_bytes).hexdigest(),
        min_relative_margin_denominator_power=min_margin_denominator_power,
        min_relative_margin_rank=min_margin_rank,
        uniform_relative_margin_bits=21,
        itinerary_sha256=hashlib.sha256(itinerary).hexdigest(),
        correction_seed_depth=5,
        correction_requested_depth=requested_correction_depth,
        correction_certified_depth=len(correction_prefix),
        correction_prefix_depths=correction_depths,
        correction_crossed_boundary_valuations=correction_crossing_valuations,
        correction_crossed_boundary_count=sum(
            valuation >= 0 for valuation in correction_crossing_valuations
        ),
        correction_max_crossed_boundary_valuation=max(
            correction_crossing_valuations, default=-1
        ),
        correction_valuation_le_one_observed=all(
            valuation <= 1 for valuation in correction_crossing_valuations
        ),
        correction_minimum_uncapped_depth_gain=min(
            (
                next_depth - depth
                for depth, next_depth in zip(
                    correction_depths,
                    (
                        correction_depths[1:-1]
                        if correction_depths[-1] == requested_correction_depth
                        else correction_depths[1:]
                    ),
                )
            ),
            default=0,
        ),
        correction_strict_amplification_verified=True,
        correction_prefix_matches_greedy=correction_matches_greedy,
        correction_dyadic_residual_identity_verified=True,
        correction_fraction_audit_depth=fraction_audit_depth,
        correction_prefix_sha256=hashlib.sha256(
            correction_prefix.encode("ascii")
        ).hexdigest(),
        quotient_recurrence_matches_greedy=True,
        quotient_closed_state_verified=True,
        quotient_weak_core_bound_verified=True,
        quotient_cardinality_state_verified=True,
        quotient_strict_closed_state_verified=True,
        quotient_full_terminal_zero_verified=True,
        quotient_full_terminal_defect_max=(
            quotient_full_terminal_defect_max
        ),
        quotient_full_terminal_nonzero_count=(
            quotient_full_terminal_nonzero_count
        ),
        quotient_saturated_state_count=quotient_saturated_state_count,
        quotient_min_take_cardinality_gap=(
            quotient_min_take_cardinality_gap
        ),
        quotient_min_take_cardinality_gap_rank=(
            quotient_min_take_cardinality_gap_rank
        ),
        quotient_min_closed_capacity_margin=(
            quotient_min_closed_capacity_margin
        ),
        quotient_min_closed_capacity_margin_rank=(
            quotient_min_closed_capacity_margin_rank
        ),
    )


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--ranks", type=int, default=10_000)
    parser.add_argument("--precision-bits", type=int)
    parser.add_argument(
        "--correction-depth",
        type=int,
        help="exact correction-prefix depth (default: all requested ranks)",
    )
    args = parser.parse_args()
    precision = args.precision_bits or (2 * args.ranks + 1_024)
    receipt = certify(args.ranks, precision, args.correction_depth)
    print(json.dumps(receipt.__dict__, indent=2, sort_keys=True))


if __name__ == "__main__":
    main()
