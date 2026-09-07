#!/usr/bin/env python3
"""Exact receipts for the anchored-coefficient zero-buffer seam."""

from __future__ import annotations

import json
from fractions import Fraction
from math import gcd


def lcm(a: int, b: int) -> int:
    return a // gcd(a, b) * b


def seam_data(height: int, rank: int) -> tuple[int, int, int, int]:
    assert rank >= 2
    assert height % rank == 0
    assert height % (rank - 1) == 0
    numerator = (1 << height) - 1
    atom = 3 * (numerator // ((1 << rank) - 1))
    predecessor = 3 * (numerator // ((1 << (rank - 1)) - 1))
    width = predecessor - 2 * atom
    quotient_width = numerator // (
        ((1 << (rank - 1)) - 1) * ((1 << rank) - 1)
    )
    assert width == 3 * quotient_width
    return 2 * atom, predecessor, width, quotient_width


def residue_coverage(height: int, rank: int, bits: int) -> bool:
    lower, upper, _, quotient_width = seam_data(height, rank)
    modulus = 1 << bits
    assert quotient_width >= modulus
    assert lower % 3 == 0 and lower + 3 * modulus <= upper
    residues = {
        (lower + 3 * offset) % modulus for offset in range(modulus)
    }
    return residues == set(range(modulus))


def first_covering_height(rank: int, bits: int) -> int:
    period = lcm(15, lcm(rank, rank - 1))
    height = period
    while True:
        *_, quotient_width = seam_data(height, rank)
        if quotient_width >= 1 << bits:
            return height
        height += period


def borrow_transport_receipts() -> list[dict[str, int]]:
    receipts: list[dict[str, int]] = []
    for base_height, exponent in [(15, 10), (15, 2), (105, 97)]:
        rank = 2 + base_height - exponent
        common_height = lcm(base_height, rank)
        incoming = (
            (1 << exponent)
            * ((1 << common_height) - 1)
            // ((1 << base_height) - 1)
        )
        atom = (
            3
            * ((1 << common_height) - 1)
            // ((1 << rank) - 1)
        )
        residual = incoming - atom
        assert residual > 0
        window = min(base_height, rank)
        modulus = 1 << window
        assert residual % modulus == ((1 << exponent) - 3) % modulus
        receipts.append(
            {
                "base_height": base_height,
                "exponent": exponent,
                "front_rank": rank,
                "common_height": common_height,
                "window_bits": window,
                "residual_suffix": residual % modulus,
            }
        )
    return receipts


def clock_corridor_receipts() -> list[dict[str, int]]:
    receipts: list[dict[str, int]] = []
    for rank in range(4, 19):
        height = lcm(15, lcm(rank, rank - 1))
        lower, upper, _, _ = seam_data(height, rank)
        scale = 1 << (height - rank)
        assert 6 * scale < lower < upper < 7 * scale

        common_suffix_bits = height - 2 * rank + 4
        common_prefix = 3 * (1 << (rank - 3))
        assert lower >> common_suffix_bits == common_prefix
        assert (upper - 1) >> common_suffix_bits == common_prefix

        lower_remainder = lower - 6 * scale
        upper_remainder = upper - 6 * scale
        assert lower_remainder == (
            6 * (((1 << (height - rank)) - 1) // ((1 << rank) - 1))
        )
        assert upper_remainder == (
            3
            * (((1 << (height - rank + 1)) - 1) // ((1 << (rank - 1)) - 1))
        )
        receipts.append(
            {
                "rank": rank,
                "height": height,
                "leading_radix_digit": lower // scale,
                "common_prefix_bits": rank - 1,
                "common_prefix_value": common_prefix,
                "renormalized_lower_bit_length": lower_remainder.bit_length(),
                "renormalized_upper_bit_length": upper_remainder.bit_length(),
            }
        )
    return receipts


def root_rank_fifteen_receipt() -> dict[str, int | bool]:
    """Exact finite audit: no Boolean prefix below 15 strands the bad pair."""
    weight = lambda rank: Fraction(1, (1 << rank) - 1)
    target = Fraction(1, 21)
    prefix_weights = [weight(rank) for rank in range(2, 15)]
    dangerous = 0
    for mask in range(1 << len(prefix_weights)):
        residual = target - sum(
            (
                prefix_weights[index]
                for index in range(len(prefix_weights))
                if mask & (1 << index)
            ),
            Fraction(0),
        )
        if 2 * weight(15) <= residual < weight(14):
            dangerous += 1
    assert dangerous == 0

    height = lcm(15, 14)
    lower, _, _, _ = seam_data(height, 15)
    lifted_bad_pair = 6 * (((1 << height) - 1) // ((1 << 15) - 1))
    assert lower == lifted_bad_pair

    current_height = height
    current_lower = lower
    strip_count = 0
    while current_height > 15:
        current_lower -= 6 * (1 << (current_height - 15))
        current_height -= 15
        expected = 6 * (((1 << current_height) - 1) // ((1 << 15) - 1))
        assert current_lower == expected
        strip_count += 1
    assert current_lower == 6
    return {
        "rank": 15,
        "boolean_prefixes_checked": 1 << len(prefix_weights),
        "complete_root_dangerous_prefixes": dangerous,
        "ancestry_impostor_height": height,
        "ancestry_impostor_strip_count": strip_count,
        "terminal_coefficient": current_lower,
        "impostor_is_exact_lift_of_root_bits_1_2": True,
    }


def suffix_solvency_counterexample() -> dict[str, str | int | bool]:
    weight = lambda rank: Fraction(1, (1 << rank) - 1)
    height = 15
    protected_rank = 7
    window = height - 2 * protected_rank + 4
    assert window == 5
    suffix_value = Fraction((1 << window) - 3, 3 * ((1 << height) - 1))
    remainder = suffix_value - weight(12)
    tax = weight(protected_rank - 1) * weight(protected_rank)
    assert suffix_value == Fraction(29, 98301)
    assert remainder == Fraction(974, 19168695)
    assert 0 < remainder < tax
    assert tax - remainder == Fraction(20063, 270491585)
    return {
        "height": height,
        "protected_rank": protected_rank,
        "forced_suffix_window": window,
        "suffix_coefficient": (1 << window) - 3,
        "allowed_discharge_rank": 12,
        "positive_remainder": str(remainder),
        "adjacent_tax": str(tax),
        "remainder_below_tax": True,
    }


def main() -> None:
    root_coefficient = 1510
    bad_coefficient = 6
    assert root_coefficient & 31 == bad_coefficient

    lift_height = 60
    lift_factor = ((1 << lift_height) - 1) // ((1 << 15) - 1)
    assert lift_factor % (1 << 15) == 1
    assert (root_coefficient * lift_factor) % 32 == bad_coefficient
    assert (bad_coefficient * lift_factor) % (1 << 15) == bad_coefficient

    receipts: list[dict[str, int | bool]] = []
    for rank, bits in [(4, 5), (5, 7), (8, 8), (15, 6)]:
        height = first_covering_height(rank, bits)
        lower, upper, width, quotient_width = seam_data(height, rank)
        covered = residue_coverage(height, rank, bits)
        assert covered
        receipts.append(
            {
                "rank": rank,
                "bits": bits,
                "height": height,
                "lower_coefficient_bit_length": lower.bit_length(),
                "upper_coefficient_bit_length": upper.bit_length(),
                "interval_width_bit_length": width.bit_length(),
                "divisible_by_three_count_at_least": 1 << bits,
                "all_residues_covered": covered,
            }
        )

    print(
        json.dumps(
            {
                "root_coefficient": root_coefficient,
                "isolated_bad_coefficient": bad_coefficient,
                "common_low_five_bits": root_coefficient & 31,
                "lift_height": lift_height,
                "lift_factor_mod_2_pow_15": lift_factor % (1 << 15),
                "borrow_transport_receipts": borrow_transport_receipts(),
                "clock_corridor_receipts": clock_corridor_receipts(),
                "residue_coverage_receipts": receipts,
                "root_rank_fifteen_receipt": root_rank_fifteen_receipt(),
                "suffix_solvency_counterexample": suffix_solvency_counterexample(),
                "conclusion": (
                    "Every fixed 2-adic coefficient suffix occurs in a "
                    "height-15-compatible zero-buffer seam; exclusion needs "
                    "a moving most-significant window coupled to ownership."
                ),
            },
            indent=2,
            sort_keys=True,
        )
    )


if __name__ == "__main__":
    main()
