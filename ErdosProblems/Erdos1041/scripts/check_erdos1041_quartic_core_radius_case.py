#!/usr/bin/env python3
"""Exact replay for the Erdős #1041 quartic-core radius theorem witness."""

from __future__ import annotations

import json
from fractions import Fraction
from itertools import combinations


Point = tuple[Fraction, Fraction]


def sub(a: Point, b: Point) -> Point:
    return a[0] - b[0], a[1] - b[1]


def norm_sq(a: Point) -> Fraction:
    return a[0] ** 2 + a[1] ** 2


def add(a: Point, b: Point) -> Point:
    return a[0] + b[0], a[1] + b[1]


def mul(a: Point, b: Point) -> Point:
    return a[0] * b[0] - a[1] * b[1], a[0] * b[1] + a[1] * b[0]


def monic_coefficients(roots: list[Point]) -> list[Point]:
    """Ascending coefficients of the exact product of `(z-root)`."""

    coefficients: list[Point] = [(Fraction(1), Fraction(0))]
    for root in roots:
        updated = [(Fraction(0), Fraction(0))] * (len(coefficients) + 1)
        for degree, coefficient in enumerate(coefficients):
            updated[degree] = add(updated[degree], mul((-root[0], -root[1]), coefficient))
            updated[degree + 1] = add(updated[degree + 1], coefficient)
        coefficients = updated
    return coefficients


def main() -> None:
    h: Point = (Fraction(-3, 10), Fraction(0))
    core: list[Point] = [
        (Fraction(3, 50), Fraction(12, 25)),
        (Fraction(-39, 50), Fraction(9, 25)),
        (Fraction(-33, 50), Fraction(-12, 25)),
        (Fraction(9, 50), Fraction(-9, 25)),
    ]
    fifth: Point = (Fraction(9, 10), Fraction(0))
    roots = [*core, fifth]
    radius = Fraction(3, 5)
    fifth_distance = Fraction(6, 5)
    factor_bound = radius + fifth_distance
    budget = radius**4 * factor_bound

    assert all(norm_sq(sub(z, h)) == radius**2 for z in core)
    assert norm_sq(sub(fifth, h)) == fifth_distance**2
    assert all(norm_sq(z) < 1 for z in roots)

    pair_distances = {
        f"{i}-{j}": norm_sq(sub(roots[i], roots[j]))
        for i, j in combinations(range(5), 2)
    }
    assert all(value > Fraction(5, 9) for value in pair_distances.values())
    assert budget == Fraction(729, 3125)
    assert budget < 1
    polynomial = monic_coefficients(roots)
    assert polynomial[-1] == (Fraction(1), Fraction(0))
    assert all(coefficient != (0, 0) for coefficient in polynomial)

    # One transparent point strictly inside the uniform quintic radius class.
    uniform_test_radius = Fraction(4, 5)
    uniform_test_budget = 2 * uniform_test_radius**5
    assert uniform_test_budget == Fraction(2048, 3125)
    assert uniform_test_budget < 1

    receipt = {
        "schema": "erdos1041_quartic_core_radius_case_audit_v1",
        "status": "pass",
        "exact_witness": {
            "center": [str(value) for value in h],
            "core_radius": str(radius),
            "fifth_distance_from_center": str(fifth_distance),
            "remaining_factor_bound": str(factor_bound),
            "quartic_core_budget": str(budget),
            "path_length_bound": str(2 * radius),
            "root_norm_squares": [str(norm_sq(z)) for z in roots],
            "pair_distance_squares": {
                key: str(value) for key, value in pair_distances.items()
            },
            "polynomial_coefficients_ascending": [
                [str(real), str(imag)] for real, imag in polynomial
            ],
            "polynomial_is_dense": True,
            "close_pair_threshold_sq": "5/9",
        },
        "uniform_quintic_check": {
            "radius": str(uniform_test_radius),
            "two_times_radius_pow_five": str(uniform_test_budget),
        },
        "proof_authority": (
            "Pendyala's attributed analytic quartic theorem, the companion "
            "factor-budget proof, and the Lean kernel; this script exactly "
            "replays the rational strict-extension certificate"
        ),
    }
    print(json.dumps(receipt, indent=2, sort_keys=True))


if __name__ == "__main__":
    main()
