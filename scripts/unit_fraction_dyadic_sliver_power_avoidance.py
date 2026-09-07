#!/usr/bin/env python3
"""Exact finite audit for UnitFractionDyadicSliverPowerAvoidance.md.

The exhaustive subset and unit-denominator searches are finite evidence
only.  All comparisons use Fraction or cleared integer arithmetic.
"""

from __future__ import annotations

import argparse
from fractions import Fraction
from itertools import combinations


def weight(rank: int) -> Fraction:
    return Fraction(1, (1 << rank) - 1)


def interval_has_integer(prefix: Fraction, rank: int) -> tuple[bool, int]:
    lower = 1 / (prefix + weight(rank))
    upper = 1 / (prefix + Fraction(1, 1 << rank))
    candidate = lower.numerator // lower.denominator + 1
    return Fraction(candidate) <= upper, candidate


def exhaustive_subsets(max_rank: int) -> int:
    checked = 0
    for rank in range(3, max_rank + 1):
        earlier = list(range(2, rank))
        for size in range(len(earlier) + 1):
            for support in combinations(earlier, size):
                if not support:
                    continue
                prefix = sum((weight(d) for d in support), Fraction())
                hit, candidate = interval_has_integer(prefix, rank)
                if hit:
                    raise AssertionError(
                        f"integer sliver hit: rank={rank}, support={support}, "
                        f"D={candidate}"
                    )
                checked += 1
    return checked


def unit_fraction_orbits(max_denominator: int, depth: int) -> int:
    checked_skips = 0
    for denominator in range(3, max_denominator, 2):
        residual = Fraction(1, denominator)
        for rank in range(1, depth + 1):
            atom = weight(rank)
            if residual >= atom:
                residual -= atom
                if residual == 0:
                    break
            else:
                checked_skips += 1
                if residual * (1 << rank) >= 1:
                    reciprocal_ceiling = (
                        residual.denominator + residual.numerator - 1
                    ) // residual.numerator
                    raise AssertionError(
                        f"dangerous skip: D={denominator}, rank={rank}, "
                        f"ceil(1/r)={reciprocal_ceiling}"
                    )
    return checked_skips


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--subset-depth", type=int, default=20)
    parser.add_argument("--max-denominator", type=int, default=5000)
    parser.add_argument("--orbit-depth", type=int, default=200)
    args = parser.parse_args()
    subset_count = exhaustive_subsets(args.subset_depth)
    skip_count = unit_fraction_orbits(args.max_denominator, args.orbit_depth)
    print("unit-fraction dyadic-sliver audit: PASS")
    print(f"nonempty subsets checked: {subset_count}")
    print(f"actual unit-fraction skips checked: {skip_count}")
    print("status: exact finite evidence only; integer-free theorem unproved")


if __name__ == "__main__":
    main()
