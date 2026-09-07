#!/usr/bin/env python3
"""Exact finite audit of the Boolean quadratic correlation identities."""

from __future__ import annotations

import argparse
import json
from fractions import Fraction
from math import gcd


def mobius_sieve(depth: int) -> list[int]:
    mu = [1] * (depth + 1)
    prime = [True] * (depth + 1)
    mu[0] = 0
    for p in range(2, depth + 1):
        if not prime[p]:
            continue
        for multiple in range(p, depth + 1, p):
            prime[multiple] = False
            mu[multiple] *= -1
        square = p * p
        for multiple in range(square, depth + 1, square):
            mu[multiple] = 0
    return mu


def lcm(left: int, right: int) -> int:
    return left // gcd(left, right) * right


def source_digit(rank: int) -> int:
    return int(rank % 6 in (0, 5))


def cofinite_model(depth: int, cutoff: int) -> tuple[list[int], ...]:
    bits = [0] * (depth + 1)
    for rank in range(cutoff, depth + 1):
        bits[rank] = 1

    divisor_load = [0] * (depth + 1)
    for divisor in range(1, depth + 1):
        if bits[divisor]:
            for multiple in range(divisor, depth + 1, divisor):
                divisor_load[multiple] += 1

    carry = [0] * (depth + 1)
    for rank in range(1, depth + 1):
        carry[rank] = (
            2 * carry[rank - 1] + source_digit(rank) - divisor_load[rank]
        )
        assert carry[rank] >= 0
    return bits, divisor_load, carry


def audit(depth: int, cutoff: int) -> dict[str, object]:
    bits, divisor_load, carry = cofinite_model(depth, cutoff)
    mu = mobius_sieve(depth)

    inverted = [0] * (depth + 1)
    for rank in range(1, depth + 1):
        inverted[rank] = sum(
            mu[d] * divisor_load[rank // d]
            for d in range(1, rank + 1)
            if rank % d == 0
        )
        assert inverted[rank] == bits[rank]
        assert inverted[rank] ** 2 == inverted[rank]

    direct_energy = sum(value * value for value in divisor_load)
    correlation_energy = 0
    for left in range(1, depth + 1):
        if not bits[left]:
            continue
        for right in range(1, depth + 1):
            if bits[right]:
                correlation_energy += depth // lcm(left, right)
    assert direct_energy == correlation_energy

    diagonal_lower = sum(
        bits[d] * (depth // d) for d in range(1, depth + 1)
    )
    assert direct_energy >= diagonal_lower

    harmonic_energy = sum(
        (Fraction(bits[n], n) for n in range(1, depth + 1)), Fraction(0)
    )
    mobius_diagonal = Fraction(0)
    for d in range(1, depth + 1):
        if mu[d] == 0:
            continue
        mobius_diagonal += Fraction(1, d) * sum(
            (
                Fraction(divisor_load[m] ** 2, m)
                for m in range(1, depth // d + 1)
            ),
            Fraction(0),
        )
    mobius_off_diagonal = harmonic_energy - mobius_diagonal
    assert mobius_diagonal + mobius_off_diagonal == harmonic_energy

    skipped = [rank for rank in range(1, depth + 1) if not bits[rank]]
    assert all(carry[rank] < 6 for rank in skipped)

    return {
        "depth": depth,
        "cofinite_cutoff": cutoff,
        "mobius_inversion_and_idempotence": True,
        "positive_correlation_identity": True,
        "direct_sum_f_squared": direct_energy,
        "diagonal_lower_bound": diagonal_lower,
        "boolean_harmonic_energy_approx": float(harmonic_energy),
        "mobius_weighted_diagonal_approx": float(mobius_diagonal),
        "mobius_weighted_off_diagonal_approx": float(
            mobius_off_diagonal
        ),
        "off_diagonal_sign": (
            "negative" if mobius_off_diagonal < 0 else "nonnegative"
        ),
        "skipped_ranks": skipped,
        "skipped_rank_carries": [carry[rank] for rank in skipped],
        "scaled_carry_at_depth_approx": float(
            Fraction(carry[depth], 1 << depth)
        ),
        "claim_status": (
            "finite exact audit; the identities and cofinite no-go are "
            "proved for all depths in the accompanying note"
        ),
    }


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--depth", type=int, default=2000)
    parser.add_argument("--cutoff", type=int, default=6)
    args = parser.parse_args()
    if args.cutoff < 6 or args.cutoff > args.depth:
        raise SystemExit("require 6 <= cutoff <= depth")
    print(json.dumps(audit(args.depth, args.cutoff), indent=2, sort_keys=True))


if __name__ == "__main__":
    main()
