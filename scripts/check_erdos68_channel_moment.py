#!/usr/bin/env python3
# SPDX-FileCopyrightText: 2026 Will Cook
# SPDX-License-Identifier: Apache-2.0
"""Replay the exact D=4 factorial-channel example in the #68 short paper.

This checks finite integer arithmetic. The paper's finite tail-gcd theorem,
not this script, proves that the computed gcd controls every later index.
Neither establishes irrationality of the original factorial series.
"""

from math import factorial, gcd, lcm


def weight(d: int, n: int) -> int:
    denominator = factorial(d) ** (n // d)
    quotient, remainder = divmod(factorial(n), denominator)
    if remainder:
        raise SystemExit(f"nonintegral weight at d={d}, n={n}")
    return quotient


def first_coordinates(bound: int) -> list[int]:
    coordinates = [0] * (bound + 1)
    coordinates[2] = 2
    for n in range(3, bound + 1):
        coordinates[n] = -sum(
            weight(d, n) * coordinates[d]
            for d in range(2, n) if n % d == 0
        )
    return coordinates


def main() -> None:
    d_max, prime = 4, 3
    bound = d_max * (2 * prime - 1)
    coordinates = first_coordinates(bound)
    tail_gcd = 0
    for value in coordinates[d_max + 1:]:
        tail_gcd = gcd(tail_gcd, value)

    common_multiple = lcm(*(factorial(d) - 1 for d in range(2, d_max + 1)))
    index_one_coefficient = common_multiple - sum(
        common_multiple // (factorial(d) - 1) * coordinates[d]
        for d in range(2, d_max + 1)
    )
    minimum_moment = common_multiple * tail_gcd // gcd(
        tail_gcd, index_one_coefficient
    )

    # Paper, Section 2: 12 K_4 + 253 U_6 - 11 U_8 has no e_1 component.
    if 12 * index_one_coefficient + 253 * coordinates[6] - 11 * coordinates[8]:
        raise SystemExit("the proposed U-basis combination retains an index-one coefficient")
    vector = dict(zip(range(2, 9), (-15318, 8176, -710, 1518, -253, -88, 11)))
    moment = sum(coefficient * factorial(n) for n, coefficient in vector.items())
    channels = {
        d: sum(coefficient * weight(d, n) for n, coefficient in vector.items())
        for d in range(2, d_max + 1)
    }

    if (bound, common_multiple, index_one_coefficient, tail_gcd) != (20, 115, -55, 60):
        raise SystemExit("the finite recurrence does not reproduce the paper's D=4 inputs")
    if minimum_moment != moment or moment != 1380:
        raise SystemExit("the vector does not attain the predicted positive moment")
    if channels != {2: 0, 3: 0, 4: 0}:
        raise SystemExit("the vector does not cancel all three prescribed channels")
    print(f"D=4: H={bound}, L={common_multiple}, a={index_one_coefficient}, g={tail_gcd}")
    print(f"vector moment={moment}; channels={channels}; positive generator={minimum_moment}")


if __name__ == "__main__":
    main()
