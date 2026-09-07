#!/usr/bin/env python3
"""Exact audit of the future-divisor resolvent for the actual 1/21 prefix.

The script verifies the evaluation, transport, cut, and boundary identities.
It also records exact counterexamples to descent principles which omit the
saturated-row equation.  Those counterexamples do not disprove a descent
theorem that genuinely uses exact saturation.
"""

from __future__ import annotations

import argparse
import json
from bisect import bisect_right
from fractions import Fraction


def weight(rank: int) -> Fraction:
    return Fraction(1, (1 << rank) - 1)


def actual_greedy(depth: int) -> tuple[list[int], list[Fraction]]:
    bits = [0] * (depth + 1)
    remainders = [Fraction(1, 21)]
    remainder = Fraction(1, 21)
    for rank in range(1, depth + 1):
        coin = weight(rank)
        if remainder >= coin:
            bits[rank] = 1
            remainder -= coin
        remainders.append(remainder)
    return bits, remainders


def selected(bits: list[int], boundary: int) -> list[int]:
    return [rank for rank in range(2, boundary + 1) if bits[rank]]


def fractional_part(numerator: int, denominator: int) -> Fraction:
    return Fraction(numerator % denominator, denominator)


def resolvent_half(bits: list[int], boundary: int) -> Fraction:
    scale = 1 << (2 * boundary)
    return sum(
        (
            fractional_part(scale, (1 << divisor) - 1)
            for divisor in selected(bits, boundary)
        ),
        Fraction(),
    )


def arrival_count(bits: list[int], boundary: int, offset: int) -> int:
    return sum(
        (2 * boundary + offset) % divisor == 0
        for divisor in selected(bits, boundary)
    )


def two_step_pulse(bits: list[int], boundary: int) -> int:
    return (
        2 * arrival_count(bits, boundary, 1)
        + arrival_count(bits, boundary, 2)
    )


def quotient_state(bits: list[int], boundary: int) -> int:
    scale = 1 << (2 * boundary)
    return scale // 21 - sum(
        scale // ((1 << divisor) - 1)
        for divisor in selected(bits, boundary)
    )


def block_charge(bits: list[int], boundary: int) -> int:
    return sum(
        1 << (2 * boundary - multiple)
        for divisor in selected(bits, boundary)
        for multiple in range(
            (boundary // divisor + 1) * divisor,
            2 * boundary + 1,
            divisor,
        )
    )


def old_cut_fraction(bits: list[int], boundary: int) -> Fraction:
    scale = 1 << boundary
    return sum(
        (
            fractional_part(scale, (1 << divisor) - 1)
            for divisor in selected(bits, boundary)
        ),
        Fraction(),
    )


def epsilon_upper_bound(boundary: int) -> Fraction:
    """A strict upper bound for sum_{k>=3} 2^((2-k)R)/(2^k-1)."""
    return Fraction(1, 7 * ((1 << boundary) - 1))


def verify_identities(
    bits: list[int], remainders: list[Fraction], depth: int
) -> dict[str, object]:
    for boundary in range(2, depth):
        rho = resolvent_half(bits, boundary)
        pulse = two_step_pulse(bits, boundary)

        # Shift the binary boundary by two positions and insert the new clock.
        transported = 4 * rho - pulse
        if bits[boundary + 1]:
            transported += weight(boundary + 1)
        assert resolvent_half(bits, boundary + 1) == transported

        # The forced-block charge and future resolvent partition one clock tail.
        assert (
            Fraction(block_charge(bits, boundary)) + rho
            == (1 << boundary) * old_cut_fraction(bits, boundary)
        )

        # Exact floor decomposition of the actual-prefix quotient state.
        target_phase = fractional_part(1 << (2 * boundary), 21)
        assert Fraction(quotient_state(bits, boundary)) == (
            (1 << (2 * boundary)) * remainders[boundary]
            - target_phase
            + rho
        )

        # Coefficient-level form of the full generating-function transport.
        for offset in range(1, min(3 * boundary, 80) + 1):
            asserted = arrival_count(bits, boundary, offset + 2)
            if bits[boundary + 1] and offset % (boundary + 1) == 0:
                asserted += 1
            assert arrival_count(bits, boundary + 1, offset) == asserted

    return {
        "verified_boundaries": [2, depth - 1],
        "coefficient_offsets_per_boundary": "1 through min(3R,80)",
        "claim_status": "exact integer and rational identities",
    }


def row_receipt(bits: list[int], boundary: int) -> dict[str, object]:
    rho = resolvent_half(bits, boundary)
    a = boundary // 3
    ancestors = [a + 1, 2 * (a + 1)]
    missing = [rank for rank in ancestors if not bits[rank]]
    descendants = []
    for rank in missing:
        descendant_rho = resolvent_half(bits, rank)
        descendants.append(
            {
                "rank": rank,
                "phase_mod_3": rank % 3,
                "quotient_excess": quotient_state(bits, rank) - (1 << rank),
                "resolvent_half": str(descendant_rho),
                "resolvent_less_than_three_sevenths": (
                    descendant_rho < Fraction(3, 7)
                ),
                "nu_1": arrival_count(bits, rank, 1),
                "nu_2": arrival_count(bits, rank, 2),
            }
        )
    return {
        "rank": boundary,
        "phase_mod_3": boundary % 3,
        "quotient_excess": quotient_state(bits, boundary) - (1 << boundary),
        "exact_saturation": quotient_state(bits, boundary) == (1 << boundary),
        "resolvent_half": str(rho),
        "resolvent_plus_epsilon_upper_less_than_three_sevenths": (
            rho + epsilon_upper_bound(boundary) < Fraction(3, 7)
        ),
        "nu_1": arrival_count(bits, boundary, 1),
        "nu_2": arrival_count(bits, boundary, 2),
        "two_step_pulse": two_step_pulse(bits, boundary),
        "ancestor_pair": ancestors,
        "missing_ancestors": missing,
        "missing_ancestor_rows": descendants,
    }


def descent_counterexamples(bits: list[int]) -> dict[str, object]:
    rows = [row_receipt(bits, boundary) for boundary in (20, 56)]
    for row in rows:
        assert row["phase_mod_3"] == 2
        assert row[
            "resolvent_plus_epsilon_upper_less_than_three_sevenths"
        ]
        assert row["two_step_pulse"] <= 1
        assert row["missing_ancestors"]
        assert not row["exact_saturation"]
        assert all(
            not child["resolvent_less_than_three_sevenths"]
            for child in row["missing_ancestor_rows"]
        )
    return {
        "rows": rows,
        "falsified_statement": (
            "phase R=2 mod 3, low resolvent, sparse first-two pulse, and an "
            "ancestor hole force a low-resolvent ancestor-scale row"
        ),
        "not_falsified": (
            "a descent theorem which additionally uses the exact saturated-"
            "row equation"
        ),
        "claim_status": "exact actual-prefix counterexamples",
    }


def first_crossing_algebra() -> dict[str, object]:
    """Record the exact take/skip split for a first supercapacity crossing."""
    return {
        "take_transition": "m_(R+1)=4*m_R+p_R+1-t_R",
        "take_first_crossing_consequence": (
            "m_R=0, t_R=3, and p_R<=1"
        ),
        "skip_transition": "m_(R+1)=4*m_R-2^(R+1)+p_R-t_R",
        "skip_first_crossing_condition": (
            "4*m_R+p_R-t_R < 2^(R+1); this does not force m_R=0"
        ),
        "claim_status": "exact integer deduction from the actual-prefix recurrence",
    }


def saturation_scan(bits: list[int], depth: int) -> dict[str, object]:
    saturated = [
        boundary
        for boundary in range(2, depth + 1)
        if quotient_state(bits, boundary) == (1 << boundary)
    ]
    return {
        "depth": depth,
        "actual_prefix_saturated_rows": saturated,
        "claim_status": "exact finite integer computation",
    }


def minimal_nonnegative_boolean_model(boundary: int) -> dict[str, object]:
    """Exhaustively minimize e=S_R-2^R over all Boolean D with e>=0."""
    weighted_ranks = [
        ((1 << (2 * boundary)) // ((1 << rank) - 1), rank)
        for rank in range(2, boundary + 1)
    ]
    split = len(weighted_ranks) // 2
    left = weighted_ranks[:split]
    right = weighted_ranks[split:]

    left_sums = [(0, 0)]
    for index, (value, _rank) in enumerate(left):
        left_sums += [
            (subtotal + value, mask | (1 << index))
            for subtotal, mask in left_sums
        ]
    right_sums = [(0, 0)]
    for index, (value, _rank) in enumerate(right):
        right_sums += [
            (subtotal + value, mask | (1 << index))
            for subtotal, mask in right_sums
        ]
    right_sums.sort()
    right_values = [subtotal for subtotal, _mask in right_sums]

    target_sum = (1 << (2 * boundary)) // 21 - (1 << boundary)
    best_sum = -1
    best_left_mask = 0
    best_right_mask = 0
    for left_sum, left_mask in left_sums:
        index = bisect_right(right_values, target_sum - left_sum) - 1
        if index < 0:
            continue
        combined = left_sum + right_sums[index][0]
        if combined > best_sum:
            best_sum = combined
            best_left_mask = left_mask
            best_right_mask = right_sums[index][1]

    support = [
        rank
        for index, (_value, rank) in enumerate(left)
        if (best_left_mask >> index) & 1
    ] + [
        rank
        for index, (_value, rank) in enumerate(right)
        if (best_right_mask >> index) & 1
    ]
    model_bits = [0] * (boundary + 1)
    for rank in support:
        model_bits[rank] = 1
    excess = quotient_state(model_bits, boundary) - (1 << boundary)
    assert excess == target_sum - best_sum >= 0

    smaller_nonnegative_rows = [
        {
            "rank": rank,
            "excess": quotient_state(model_bits, rank) - (1 << rank),
        }
        for rank in range(2, boundary)
        if quotient_state(model_bits, rank) >= (1 << rank)
    ]
    a = boundary // 3
    ancestors = [a + 1, 2 * (a + 1)]
    missing = [rank for rank in ancestors if not model_bits[rank]]
    rho = resolvent_half(model_bits, boundary)
    return {
        "rank": boundary,
        "support": support,
        "excess": excess,
        "minimal_nonnegative_excess_among_all_boolean_supports": True,
        "phase_mod_3": boundary % 3,
        "resolvent_half": str(rho),
        "resolvent_plus_epsilon_upper_less_than_three_sevenths": (
            rho + epsilon_upper_bound(boundary) < Fraction(3, 7)
        ),
        "two_step_pulse": two_step_pulse(model_bits, boundary),
        "ancestor_pair": ancestors,
        "missing_ancestors": missing,
        "smaller_nonnegative_restriction_rows": smaller_nonnegative_rows,
        "claim_status": "exact exhaustive meet-in-the-middle subset search",
    }


def strict_layer_model_receipt() -> dict[str, object]:
    models = [
        minimal_nonnegative_boolean_model(boundary)
        for boundary in (8, 20)
    ]
    assert [model["support"] for model in models] == [
        [5, 7],
        [5, 7, 8, 9, 10, 11, 13, 16, 18],
    ]
    assert [model["excess"] for model in models] == [234, 332107]
    actual_bits, _remainders = actual_greedy(20)
    for model in models:
        boundary = int(model["rank"])
        actual_prefix = selected(actual_bits, boundary - 1)
        assert model["support"] == actual_prefix
        model["agrees_with_actual_greedy_through_rank"] = boundary - 1
        model["boundary_decision_changed_to_skip"] = boundary
        assert model["phase_mod_3"] == 2
        assert model[
            "resolvent_plus_epsilon_upper_less_than_three_sevenths"
        ]
        assert model["two_step_pulse"] <= 1
        assert model["missing_ancestors"]
        assert model["smaller_nonnegative_restriction_rows"] == []
    return {
        "models": models,
        "falsified_statement": (
            "a phase-aligned minimal nonnegative Boolean layer with low full "
            "resolvent and sparse pulse has a smaller nonnegative socket "
            "obtained by restricting its labelled clocks"
        ),
        "not_falsified": (
            "a target-specific recut which changes the support and separately "
            "re-establishes greedy admissibility and the exact row equation"
        ),
        "claim_status": "exact exhaustive Boolean socket models",
    }


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--depth", type=int, default=200)
    args = parser.parse_args()
    if args.depth < 57:
        raise SystemExit("depth must be at least 57")
    bits, remainders = actual_greedy(args.depth)
    print(
        json.dumps(
            {
                "identity_audit": verify_identities(
                    bits, remainders, args.depth
                ),
                "first_crossing_interface": first_crossing_algebra(),
                "saturation_scan": saturation_scan(bits, args.depth),
                "naive_descent_counterexamples": descent_counterexamples(bits),
                "strict_layer_boolean_models": strict_layer_model_receipt(),
                "global_claim_status": (
                    "exact identities and exact counterexamples to saturation-"
                    "free descent; no saturated socket or all-depth descent is proved"
                ),
            },
            indent=2,
            sort_keys=True,
        )
    )


if __name__ == "__main__":
    main()
