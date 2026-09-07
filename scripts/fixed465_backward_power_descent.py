#!/usr/bin/env python3
"""Exact finite audit for Fixed465BackwardPowerDescent.md.

The orbit calculation uses the unreduced fixed-source integers P, S, and R.
Its depth bound is finite and does not prove dyadic undershoot.
"""

from __future__ import annotations

import argparse
import json
from fractions import Fraction
from math import gcd


TARGET_DENOMINATOR = 465


def mersenne(rank: int) -> int:
    return (1 << rank) - 1


def prime_factors(value: int) -> list[int]:
    """Return the distinct prime factors by exact trial division."""
    factors: list[int] = []
    divisor = 2
    while divisor * divisor <= value:
        if value % divisor == 0:
            factors.append(divisor)
            while value % divisor == 0:
                value //= divisor
        divisor = 3 if divisor == 2 else divisor + 2
    if value > 1:
        factors.append(value)
    return factors


def multiplicative_order_two(prime: int) -> int:
    """Return the multiplicative order of 2 modulo an odd prime."""
    residue = 2 % prime
    order = 1
    while residue != 1:
        residue = (2 * residue) % prime
        order += 1
    return order


def check_private_primes(max_rank: int = 30) -> int:
    """Check primitive Mersenne prime divisors on a finite rank range."""
    checked = 0
    for rank in range(7, max_rank + 1):
        primitive = [
            prime
            for prime in prime_factors(mersenne(rank))
            if multiplicative_order_two(prime) == rank
        ]
        assert primitive
        assert all(TARGET_DENOMINATOR % prime for prime in primitive)
        checked += 1
    return checked


def check_inverse_interval() -> int:
    """Check the displayed inverse-map identities on exact rational samples."""
    checked = 0
    for selected_rank in range(9, 31):
        mp = mersenne(selected_rank)
        for unsafe_rank in range(selected_rank + 1, 2 * selected_rank + 4):
            mm = mersenne(unsafe_rank)
            power = 1 << unsafe_rank
            z = Fraction(mm + power, 2)
            x = Fraction(mp * z, mp + z)
            lower = Fraction(mp * mm, mp + mm)
            upper = Fraction(mp * power, mp + power)
            width = Fraction(
                mp * mp,
                (mp + mm) * (mp + power),
            )
            assert lower < x < upper
            assert upper - lower == width
            assert Fraction(mp * mp, mp + power) < mp - x
            assert mp - x < Fraction(mp * mp, mp + mm)
            assert x > (1 << (selected_rank - 1))
            jump = unsafe_rank - selected_rank
            quotient = (mp - 1) // ((1 << jump) + 1)
            lower_gap = Fraction(mp * mp, mp + power)
            upper_gap = Fraction(mp * mp, mp + mm)
            assert quotient < lower_gap < upper_gap < quotient + 1
            sample_ratio = (lower_gap + upper_gap) / 2
            sample_remainder = (
                sample_ratio.numerator - quotient * sample_ratio.denominator
            )
            assert 0 < sample_remainder < sample_ratio.denominator
            assert gcd(sample_remainder, sample_ratio.denominator) == gcd(
                sample_ratio.numerator,
                sample_ratio.denominator,
            )
            complementary_remainder = (
                (quotient + 1) * sample_ratio.denominator
                - sample_ratio.numerator
            )
            assert (
                complementary_remainder
                == sample_ratio.denominator - sample_remainder
            )
            assert 0 < complementary_remainder < sample_ratio.denominator
            assert gcd(
                complementary_remainder,
                sample_ratio.denominator,
            ) == gcd(sample_ratio.numerator, sample_ratio.denominator)
            if unsafe_rank >= 2 * selected_rank:
                assert quotient == 0
                assert mp - x < 1
            else:
                assert quotient >= 1
            if (
                unsafe_rank < 2 * selected_rank
                and 3 * selected_rank < 2 * unsafe_rank
            ):
                power_rank = 2 * selected_rank - unsafe_rank
                assert quotient == mersenne(power_rank)
                x_power = 1 << power_rank
                y_power = 1 << jump
                lower_complement = Fraction(
                    x_power * x_power * y_power
                    + 2 * x_power * y_power
                    - 2 * x_power
                    - 1,
                    mp + mm,
                )
                upper_complement = Fraction(
                    x_power * x_power * y_power
                    + 2 * x_power * y_power
                    - x_power
                    - 1,
                    mp + power,
                )
                sample_complement = Fraction(
                    complementary_remainder,
                    sample_ratio.denominator,
                )
                assert lower_complement < sample_complement < upper_complement
                assert sample_ratio.denominator > 1 / upper_complement
            checked += 1
    return checked


def audit(depth: int) -> dict[str, object]:
    if depth < 9:
        raise ValueError("depth must be at least 9")

    product = 1
    prefix_sum_numerator = 0
    residual_numerator = 1
    selected: list[int] = []
    unsafe_skips: list[int] = []
    numerator_decreases: list[int] = []
    maximum_take_gap = 0
    previous_take = 0

    for rank in range(1, depth + 1):
        mr = mersenne(rank)
        if residual_numerator * mr >= TARGET_DENOMINATOR * product:
            old_product = product
            old_prefix_sum_numerator = prefix_sum_numerator
            old_residual_numerator = residual_numerator

            product = old_product * mr
            prefix_sum_numerator = (
                old_prefix_sum_numerator * mr + old_product
            )
            residual_numerator = (
                mr * old_residual_numerator
                - TARGET_DENOMINATOR * old_product
            )

            assert residual_numerator == (
                product
                - TARGET_DENOMINATOR * prefix_sum_numerator
            )
            assert residual_numerator >= 0
            if rank <= 100:
                assert gcd(residual_numerator, old_residual_numerator) == gcd(
                    old_residual_numerator,
                    TARGET_DENOMINATOR * old_product,
                )
            if residual_numerator < old_residual_numerator:
                numerator_decreases.append(rank)
            selected.append(rank)
            maximum_take_gap = max(maximum_take_gap, rank - previous_take)
            previous_take = rank
            if residual_numerator == 0:
                break
        else:
            # At a skipped rank, dyadic unsafety is strict because the
            # displayed residual denominator is odd.
            if (residual_numerator << rank) > (
                TARGET_DENOMINATOR * product
            ):
                unsafe_skips.append(rank)

    return {
        "target": "1/465",
        "depth": depth,
        "arithmetic": "exact unreduced integers",
        "selected_rank_count": len(selected),
        "last_selected_rank": selected[-1] if selected else None,
        "maximum_take_gap": maximum_take_gap,
        "unsafe_skips": unsafe_skips,
        "unreduced_numerator_decreases": numerator_decreases,
        "inverse_interval_samples_checked": check_inverse_interval(),
        "primitive_mersenne_ranks_checked": check_private_primes(),
        "claim_status": "exact finite audit only",
    }


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--depth", type=int, default=2_000)
    args = parser.parse_args()
    print(json.dumps(audit(args.depth), indent=2, sort_keys=True))


if __name__ == "__main__":
    main()
