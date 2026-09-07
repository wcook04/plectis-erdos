#!/usr/bin/env python3
"""Exact finite audit of sparse rational clocks and finite-prefix recuts.

For a rational target x with an explicitly supplied binary period, greedy
decisions are certified by directed dyadic intervals.  The script computes
the divisor defect Q_N, the delayed-doubling state P_N, and

    F_N = P_N - 2 Q_N.

It also verifies, on a finite interval, the exact bounded floor-carry cocycle
between two targets whose greedy expansions differ by a prescribed finite
prefix.  None of the finite audits is an all-depth proof.
"""

from __future__ import annotations

import argparse
import json
from fractions import Fraction


def periodic_word(
    numerator: int,
    denominator: int,
    period: int,
) -> tuple[int, list[int]]:
    """Return the period numerator and its padded binary word."""
    mersenne = (1 << period) - 1
    if mersenne % denominator != 0:
        raise ValueError(f"denominator {denominator} does not divide 2^{period}-1")
    word_numerator = numerator * (mersenne // denominator)
    if not 0 <= word_numerator < mersenne:
        raise ValueError("target must lie in [0,1)")
    word = [
        (word_numerator >> (period - 1 - index)) & 1
        for index in range(period)
    ]
    return word_numerator, word


def exact_greedy_bits(numerator: int, denominator: int, depth: int) -> list[int]:
    """Certify the first `depth` greedy decisions by directed dyadic bounds."""
    precision = 2 * depth + 64
    scale = 1 << precision
    lower = scale * numerator // denominator
    upper = (scale * numerator + denominator - 1) // denominator
    bits = [0] * (depth + 1)
    for rank in range(1, depth + 1):
        weight_floor = scale // ((1 << rank) - 1)
        if lower >= weight_floor + 1:
            lower -= weight_floor + 1
            upper -= weight_floor
            bits[rank] = 1
        elif upper <= weight_floor:
            continue
        else:
            raise AssertionError(
                f"dyadic interval does not decide rank {rank}; increase precision"
            )
    return bits


def states(
    numerator: int,
    denominator: int,
    period: int,
    depth: int,
) -> dict[str, object]:
    word_numerator, word = periodic_word(numerator, denominator, period)
    bits = exact_greedy_bits(numerator, denominator, depth)
    divisor_count = [0] * (depth + 1)
    for rank in range(1, depth + 1):
        if bits[rank]:
            for multiple in range(rank, depth + 1, rank):
                divisor_count[multiple] += 1

    prefix_count = [0] * (depth + 1)
    source_count = 0
    defect = 0
    required_allowance = -10**9
    first_required_allowance_rank = 0
    maximum_defect = 0
    last_selected = 0
    energy = [0] * (depth + 1)
    defects = [0] * (depth + 1)
    for rank in range(1, depth + 1):
        prefix_count[rank] = prefix_count[rank - 1] + bits[rank]
        if bits[rank]:
            last_selected = rank
        source_bit = word[(rank - 1) % period]
        source_count += source_bit
        defect = 2 * defect + source_bit - divisor_count[rank]
        if defect < 0:
            raise AssertionError(f"negative defect at rank {rank}")
        defects[rank] = defect
        delayed_state = (
            source_count + prefix_count[rank // 2] - prefix_count[rank]
        )
        value = 2 * defect - delayed_state
        if value > required_allowance:
            required_allowance = value
            first_required_allowance_rank = rank
        maximum_defect = max(maximum_defect, defect)
        energy[rank] = delayed_state - 2 * defect

    tail_window = min(1000, depth)
    tail_selected = sum(bits[depth - tail_window + 1 :])
    zero_energy_ranks = [rank for rank in range(1, depth + 1) if energy[rank] == 0]
    first_energy_drop = next(
        (
            {
                "rank": rank,
                "previous_energy": energy[rank - 1],
                "energy": energy[rank],
            }
            for rank in range(2, depth + 1)
            if energy[rank] < energy[rank - 1]
        ),
        None,
    )
    first_defect_above_period = next(
        (
            {"rank": rank, "defect": defects[rank]}
            for rank in range(1, depth + 1)
            if defects[rank] > period
        ),
        None,
    )
    first_defect_above_ceiling_log_two = next(
        (
            {
                "rank": rank,
                "defect": defects[rank],
                "ceiling_log_two": (rank - 1).bit_length(),
            }
            for rank in range(2, depth + 1)
            if defects[rank] > (rank - 1).bit_length()
        ),
        None,
    )
    result = {
        "target": f"{numerator}/{denominator}",
        "period": period,
        "period_numerator": word_numerator,
        "period_word": "".join(map(str, word)),
        "period_popcount": sum(word),
        "source_density": f"{sum(word)}/{period}",
        "depth": depth,
        "required_endpoint_allowance": required_allowance,
        "first_required_allowance_rank": first_required_allowance_rank,
        "maximum_defect": maximum_defect,
        "selected": prefix_count[depth],
        "skipped": depth - prefix_count[depth],
        "last_selected_rank": last_selected,
        "tail_window": tail_window,
        "tail_window_selected": tail_selected,
        "tail_window_skipped": tail_window - tail_selected,
        "terminal_unshifted_energy": energy[depth],
        "zero_energy_ranks": zero_energy_ranks,
        "first_energy_drop": first_energy_drop,
        "first_defect_above_period": first_defect_above_period,
        "first_defect_above_ceiling_log_two": (
            first_defect_above_ceiling_log_two
        ),
        "claim_status": "exact finite directed-interval computation only",
    }
    return {
        "summary": result,
        "bits": bits,
        "defects": defects,
        "energy": energy,
    }


def exact_prefix(target: Fraction, maximum_rank: int) -> tuple[list[int], Fraction]:
    residual = target
    selected: list[int] = []
    for rank in range(1, maximum_rank + 1):
        weight = Fraction(1, (1 << rank) - 1)
        if residual >= weight:
            residual -= weight
            selected.append(rank)
    return selected, residual


def recut_audit(depth: int) -> dict[str, object]:
    """Verify two finite-prefix gauges of the same tail target."""
    tail = Fraction(16, 31 * 511)
    gauges = [
        {
            "name": "short_period_gauge",
            "target": Fraction(90, 511),
            "prefix": [3, 5],
            "period": 9,
        },
        {
            "name": "near_balanced_gauge",
            "target": Fraction(50026, 237615),
            "prefix": [3, 4],
            "period": 180,
        },
    ]
    tail_state = states(tail.numerator, tail.denominator, 45, depth)
    receipts: list[dict[str, object]] = []
    for gauge in gauges:
        target = gauge["target"]
        prefix = gauge["prefix"]
        maximum_rank = max(prefix)
        expected = tail + sum(
            (Fraction(1, (1 << rank) - 1) for rank in prefix),
            Fraction(),
        )
        assert target == expected
        selected_prefix, residual = exact_prefix(target, 5)
        assert selected_prefix == prefix
        assert residual == tail
        gauge_state = states(
            target.numerator,
            target.denominator,
            int(gauge["period"]),
            depth,
        )
        tail_bits = tail_state["bits"]
        gauge_bits = gauge_state["bits"]
        assert gauge_bits[maximum_rank + 1 :] == tail_bits[maximum_rank + 1 :]

        # The exact floor discrepancy is the quotient-defect coboundary.
        maximum_cocycle = 0
        minimum_cocycle = len(prefix)
        for rank in range(1, depth + 1):
            cocycle = (
                (target.numerator * (1 << rank)) // target.denominator
                - (tail.numerator * (1 << rank)) // tail.denominator
                - sum(
                    (1 << rank) // ((1 << prefix_rank) - 1)
                    for prefix_rank in prefix
                )
            )
            defect_difference = (
                gauge_state["defects"][rank] - tail_state["defects"][rank]
            )
            assert defect_difference == cocycle
            assert 0 <= cocycle <= len(prefix)
            minimum_cocycle = min(minimum_cocycle, cocycle)
            maximum_cocycle = max(maximum_cocycle, cocycle)

        receipts.append(
            {
                "name": gauge["name"],
                "target": str(target),
                "tail_target": str(tail),
                "prefix": prefix,
                "prefix_identity_verified": True,
                "common_tail_verified_through": depth,
                "floor_cocycle_range": [minimum_cocycle, maximum_cocycle],
                "summary": gauge_state["summary"],
            }
        )
    return {
        "tail_summary": tail_state["summary"],
        "gauges": receipts,
        "claim_status": (
            "prefix identities and floor-cocycle bounds are exact; "
            "common-tail and endpoint audits are finite"
        ),
    }


def fatal_zero_extension_receipt() -> dict[str, object]:
    """Give an exact fatal-gap certificate for 104/255."""
    target = Fraction(104, 255)
    selected, residual = exact_prefix(target, 17)
    tail_upper_bound = Fraction(1, 1 << 16)
    assert residual > tail_upper_bound
    # For n > 17, 1/(2^n-1) < 2^(1-n), whose sum is 2^-16.
    return {
        "target": "104/255",
        "source_word": "01101000",
        "source_density": "3/8",
        "selected_through_rank_17": selected,
        "residual_after_rank_17": str(residual),
        "strict_tail_upper_bound": str(tail_upper_bound),
        "fatal_gap_certified": True,
        "claim_status": "exact rational certificate",
    }


def base_queue_receipt() -> dict[str, object]:
    """Test the queue using only the guaranteed ranks 3 and 5."""
    word = [int(character) for character in "001011010"]
    support = {3, 5}
    defect = 0
    cumulative_defect = 0
    first_failure: dict[str, int] | None = None
    for rank in range(1, 13):
        divisor_load = sum(
            int(divisor in support)
            for divisor in range(1, rank + 1)
            if rank % divisor == 0
        )
        defect = 2 * defect + word[(rank - 1) % 9] - divisor_load
        cumulative_defect += defect
        service_capacity = sum(
            rank // divisor
            for divisor in support
            if 2 * divisor <= rank
        )
        energy = service_capacity - cumulative_defect
        if energy < 0 and first_failure is None:
            first_failure = {
                "rank": rank,
                "defect": defect,
                "cumulative_defect": cumulative_defect,
                "service_capacity": service_capacity,
                "energy": energy,
            }
    assert first_failure == {
        "rank": 12,
        "defect": 4,
        "cumulative_defect": 9,
        "service_capacity": 6,
        "energy": -3,
    }
    return {
        "target": "90/511",
        "frozen_support": [3, 5],
        "first_negative_queue_energy": first_failure,
        "claim_status": "exact integer recurrence",
    }


def self_product_identity_receipt() -> dict[str, object]:
    """Verify the x_a product identity and its first failure to replicate."""
    for parameter in range(2, 21):
        x_value = Fraction(
            (1 << (parameter - 1)) + 1,
            (1 << (2 * parameter - 1)) - 1,
        )
        asserted = (
            Fraction(1, (1 << parameter) - 1)
            + Fraction(1, (1 << (2 * parameter)) - 1)
            + x_value * Fraction(1, (1 << (2 * parameter)) - 1)
        )
        assert x_value == asserted

    x_value = Fraction(17, 511)
    selected, _ = exact_prefix(x_value, 20)
    assert selected[:4] == [5, 10, 15, 19]
    after_three = x_value - sum(
        (
            Fraction(1, (1 << rank) - 1)
            for rank in (5, 10, 15)
        ),
        Fraction(),
    )
    early_rank_difference = after_three - Fraction(1, (1 << 19) - 1)
    assert early_rank_difference == Fraction(3901643, 41384962918761)
    assert early_rank_difference > 0
    return {
        "identity": "x_a = w_a + w_(2a) + x_a*w_(2a)",
        "parameters_verified": [2, 20],
        "a_5_target": str(x_value),
        "a_5_first_selected_ranks": selected[:4],
        "residual_after_5_10_15": str(after_three),
        "residual_minus_w_19": str(early_rank_difference),
        "naive_shifted_self_replication": (
            "false: rank 19 is selected before rank 20"
        ),
        "claim_status": (
            "identity is proved by algebra in the note; displayed a=5 "
            "comparisons are exact rational computations"
        ),
    }


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--depth", type=int, default=10_000)
    args = parser.parse_args()
    if args.depth < 100:
        raise SystemExit("depth must be at least 100")

    candidates = [
        (90, 511, 9),
        (11, 127, 7),
        (5, 31, 5),
    ]
    candidate_results = [
        states(numerator, denominator, period, args.depth)["summary"]
        for numerator, denominator, period in candidates
    ]
    expected_allowances = [0, 1, 2]
    assert [
        result["required_endpoint_allowance"] for result in candidate_results
    ] == expected_allowances
    for result in candidate_results:
        assert result["tail_window_selected"] > 0
        assert result["tail_window_skipped"] > 0

    output = {
        "method": "directed dyadic greedy bounds and exact integer recurrences",
        "candidates": candidate_results,
        "finite_prefix_recuts": recut_audit(args.depth),
        "self_product_identity": self_product_identity_receipt(),
        "guaranteed_pulse_queue_test": base_queue_receipt(),
        "zero_extension_counterexample": fatal_zero_extension_receipt(),
        "global_claim_status": (
            "finite evidence except for the displayed rational identities, "
            "bounded floor-cocycle lemma instances, and fatal-gap certificate"
        ),
    }
    print(json.dumps(output, indent=2, sort_keys=True))


if __name__ == "__main__":
    main()
