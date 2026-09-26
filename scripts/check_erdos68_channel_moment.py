#!/usr/bin/env python3
# SPDX-FileCopyrightText: 2026 Will Cook
# SPDX-License-Identifier: Apache-2.0
"""Replay the exact D=4 factorial-channel example in the #68 short paper.

This checks finite integer arithmetic. The paper's finite tail-gcd theorem,
not this script, proves that the computed gcd controls every later index.
Neither establishes irrationality of the original factorial series.
"""

from fractions import Fraction
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


def observables(vector: dict[int, int]) -> tuple[int, dict[int, int]]:
    moment = sum(coefficient * factorial(n) for n, coefficient in vector.items())
    channels = {
        d: sum(coefficient * weight(d, n) for n, coefficient in vector.items())
        for d in (2, 3, 4)
    }
    return moment, channels


def depth_four_family(t: int, x: int, y: int) -> dict[int, int]:
    return dict(zip(range(2, 9), (
        1482 - 4200 * t, -784 + 2240 * t, -680 + 1890 * t - 5 * x,
        x, 83 - 238 * t - 7 * y, y, -1 + 3 * t,
    )))


def residual_offset(vector: dict[int, int]) -> Fraction:
    """Exact value of R(vector) - M(vector) S; higher channels cancel."""
    moment, _ = observables(vector)
    return sum((Fraction(sum(coefficient * weight(d, n)
                         for n, coefficient in vector.items()) - moment,
                         factorial(d) - 1)
                for d in range(2, max(vector) + 1)), Fraction(0))


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
    moment, channels = observables(vector)

    if (bound, common_multiple, index_one_coefficient, tail_gcd) != (20, 115, -55, 60):
        raise SystemExit("the finite recurrence does not reproduce the paper's D=4 inputs")
    if minimum_moment != moment or moment != 1380:
        raise SystemExit("the vector does not attain the predicted positive moment")
    if channels != {2: 0, 3: 0, 4: 0}:
        raise SystemExit("the vector does not cancel all three prescribed channels")

    # The paper proves the all-index divisibility; this finite check catches
    # transcription errors and records the exact small-index arithmetic.
    dual = lambda n: 11 * factorial(n) - 46 * weight(2, n) + 12 * weight(4, n)
    if any(dual(n) % 1380 for n in range(2, 201)):
        raise SystemExit("the depth-four dual arithmetic failed its regression sample")
    if [dual(n) for n in range(2, 8)] != [0, 0, 0, 0, 4140, 28980]:
        raise SystemExit("the depth-four support-horizon inputs changed")
    short = depth_four_family(0, -136, 0)
    norm_minimizer = depth_four_family(0, -136, 12)
    if {n: value for n, value in short.items() if value} != {
            2: 1482, 3: -784, 5: -136, 6: 83, 8: -1}:
        raise SystemExit("the five-term vector changed")
    for parameters in ((0, -136, 0), (0, -136, 12), (1, 2, 3), (-2, -5, 7)):
        if observables(depth_four_family(*parameters)) != (1380, {2: 0, 3: 0, 4: 0}):
            raise SystemExit("the horizon-eight family failed an exact substitution")
    if sum(abs(value) for value in norm_minimizer.values()) != 2416:
        raise SystemExit("the coefficient norm changed")
    two_channel_sparse = {3: -290, 5: -136, 6: 83, 8: -1}
    two_channel_small = {3: -290, 5: -136, 6: -1, 7: 12, 8: -1}
    for candidate, expected_norm in ((two_channel_sparse, 510), (two_channel_small, 440)):
        candidate_moment, candidate_channels = observables(candidate)
        if (candidate_moment, candidate_channels[2], candidate_channels[4]) != (1380, 0, 0):
            raise SystemExit("the two-channel witness changed")
        if sum(abs(value) for value in candidate.values()) != expected_norm:
            raise SystemExit("the two-channel coefficient norm changed")
    if (residual_offset(vector), residual_offset(short), residual_offset(norm_minimizer)) != (
            -1474, -1760, -1772):
        raise SystemExit("the exact residual offsets changed")
    print(f"D=4: H={bound}, L={common_multiple}, a={index_one_coefficient}, g={tail_gcd}")
    print(f"vector moment={moment}; channels={channels}; positive generator={minimum_moment}")
    print(f"short vector={short}; moment/channels={observables(short)}")
    print(f"horizon-eight norm minimizer={norm_minimizer}; L1=2416")
    print("two-channel horizon-eight norms: sparse=510; unrestricted minimum=440")
    print("residual offsets R - M*S: old=-1474; short=-1760; norm-minimizer=-1772")


if __name__ == "__main__":
    main()
