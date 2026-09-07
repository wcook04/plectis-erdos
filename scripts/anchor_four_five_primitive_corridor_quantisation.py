#!/usr/bin/env python3
"""Exact finite fatal-corridor audit for x=M(4,5)=1/465.

The all-depth primitive-coordinate theorem is proved in the companion note.
This script only checks the stated finite absence of a Boolean corridor hit.
"""

from __future__ import annotations

import argparse
import json
from fractions import Fraction


TARGET = Fraction(1, 465)


def weight(rank: int) -> Fraction:
    return Fraction(1, (1 << rank) - 1)


def maximal_sum_below(
    bound: Fraction, last_rank: int
) -> tuple[Fraction, list[int]]:
    """Lexicographically maximal Boolean Mersenne sum at the cutoff."""
    value = Fraction(0)
    support: list[int] = []
    for rank in range(1, last_rank + 1):
        candidate = value + weight(rank)
        if candidate <= bound:
            value = candidate
            support.append(rank)
    return value, support


def first_corridor_hit(depth: int) -> dict[str, object] | None:
    for rank in range(2, depth + 1):
        upper_sum = TARGET - 2 * weight(rank)
        if upper_sum < 0:
            continue
        value, support = maximal_sum_below(upper_sum, rank - 1)
        residual = TARGET - value
        if 2 * weight(rank) <= residual < weight(rank - 1):
            return {
                "rank": rank,
                "support": support,
                "residual_numerator": residual.numerator,
                "residual_denominator": residual.denominator,
            }
    return None


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--depth", type=int, default=300)
    args = parser.parse_args()
    if args.depth < 2:
        raise SystemExit("depth must be at least 2")

    hit = first_corridor_hit(args.depth)
    if args.depth == 300 and hit is not None:
        raise AssertionError(f"unexpected corridor hit through 300: {hit}")

    print(
        json.dumps(
            {
                "target": "1/465",
                "depth": args.depth,
                "first_fatal_corridor_hit": hit,
                "method": (
                    "exact rational lexicographic maximization using reverse "
                    "superincreasing Mersenne weights"
                ),
                "claim_status": "finite audit only",
            },
            indent=2,
            sort_keys=True,
        )
    )


if __name__ == "__main__":
    main()
