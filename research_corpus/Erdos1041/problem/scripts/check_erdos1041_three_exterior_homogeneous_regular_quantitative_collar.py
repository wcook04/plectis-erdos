#!/usr/bin/env python3
"""Exact replay for the homogeneous three-exterior regular collar.

The proof is deliberately self-contained.  It builds the cleared joint gap in
the three selector-cone coordinates, and uses exact multivariate Bernstein
coefficients on rational boxes for the two sign tests used in the note.
"""

from __future__ import annotations

from collections import defaultdict
from fractions import Fraction
from itertools import product
from math import comb

from sympy.polys.domains import QQ
from sympy.polys.rings import ring


DELTA = Fraction(1, 50)


def build_gap(n: int):
    """Return the cleared gap N_n in (M,U,V,X,Y,Z,t)."""
    R, M, U, V, X, Y, Z, t = ring("M,U,V,X,Y,Z,t", QQ)
    d = n - 3
    A = 3 * (1 + t)
    B = 2 * (1 - t)
    L0 = M + (U + V) / 3
    L1 = M + (-2 * U + V) / 3
    L2 = M + (U - 2 * V) / 3
    N0 = L0 - A * X
    N1 = L1 - A * Y
    N2 = L2 + A * (X + Y)
    Ba = (N0 + N1 - N2) / 2
    Bb = (N0 + N2 - N1) / 2
    q = t + Z
    radial_den = (1 + X) * (1 + Y)
    own = (1 - q * (1 + X)) ** 2
    spectator_1 = (
        B * (1 + q * (1 + Y) + q**2 * (1 + Y) ** 2)
        - 2 * q * (1 + Y) * Ba
    )
    spectator_2 = (
        B * (radial_den**2 + q * radial_den + q**2)
        - 2 * q * radial_den * Bb
    )
    regular_square = t ** (2 * d) * (1 - t**3) ** 2
    gap = 9 * (
        B**2 * regular_square * radial_den**2
        - q ** (2 * d) * own * spectator_1 * spectator_2
    )
    return R, (M, U, V, X, Y, Z, t), gap


def restrict_zero(poly, indices: tuple[int, ...]):
    return poly.ring.from_dict(
        {
            monomial: coefficient
            for monomial, coefficient in poly.items()
            if all(monomial[index] == 0 for index in indices)
        }
    )


def affine_power_coefficients(poly, boxes):
    """Power coefficients after x_i=a_i+(b_i-a_i)s_i, 0<=s_i<=1."""
    coefficients = {
        monomial: Fraction(coefficient.numerator, coefficient.denominator)
        for monomial, coefficient in poly.items()
    }
    dimensions = len(boxes)
    for axis, (left, right) in enumerate(boxes):
        width = right - left
        transformed = defaultdict(Fraction)
        for monomial, coefficient in coefficients.items():
            exponent = monomial[axis]
            for new_exponent in range(exponent + 1):
                new_monomial = list(monomial)
                new_monomial[axis] = new_exponent
                transformed[tuple(new_monomial)] += (
                    coefficient
                    * comb(exponent, new_exponent)
                    * left ** (exponent - new_exponent)
                    * width**new_exponent
                )
        coefficients = {key: value for key, value in transformed.items() if value}
    return coefficients, dimensions


def bernstein_coefficients(poly, boxes):
    """Exact tensor-product Bernstein coefficients on a rational box."""
    power, dimensions = affine_power_coefficients(poly, boxes)
    degrees = [max((key[i] for key in power), default=0) for i in range(dimensions)]
    coefficients = power
    for axis, degree in enumerate(degrees):
        grouped = defaultdict(dict)
        for monomial, coefficient in coefficients.items():
            other = monomial[:axis] + monomial[axis + 1 :]
            grouped[other][monomial[axis]] = coefficient
        transformed = {}
        for other, vector in grouped.items():
            for index in range(degree + 1):
                value = sum(
                    vector.get(power_index, Fraction(0))
                    * Fraction(comb(index, power_index), comb(degree, power_index))
                    for power_index in range(index + 1)
                )
                monomial = other[:axis] + (index,) + other[axis:]
                transformed[monomial] = value
        coefficients = transformed
    return coefficients


def rational_t_box(n: int):
    if n == 5:
        return Fraction(7368, 10000), Fraction(7369, 10000)
    return Fraction(7937, 10000), Fraction(7938, 10000)


def certify_positive(poly, boxes, label: str):
    coefficients = bernstein_coefficients(poly, boxes)
    minimum = min(coefficients.values())
    assert minimum > 0, (label, minimum)
    print(f"{label}: {len(coefficients)} Bernstein coefficients, min={minimum}")
    return minimum


def check_degree(n: int) -> None:
    R, variables, gap = build_gap(n)
    M, U, V, X, Y, Z, t = variables
    t_left, t_right = rational_t_box(n)
    d = n - 3
    assert t_left**3 < Fraction(d, n) < t_right**3

    # Exact equality and stationary-ray identities at t^3=(n-3)/n.
    modulus = t**3 - R.domain.convert(Fraction(d, n))
    base = restrict_zero(gap, (0, 1, 2, 3, 4, 5))
    assert base.rem(modulus) == 0
    for coordinate in (X, Y, Z):
        derivative = restrict_zero(gap.diff(coordinate), (0, 1, 2, 3, 4, 5))
        assert derivative.rem(modulus) == 0

    full_boxes = (
        (Fraction(0), DELTA),
        (Fraction(0), DELTA),
        (Fraction(0), DELTA),
        (-DELTA, DELTA),
        (-DELTA, DELTA),
        (-DELTA, DELTA),
        (t_left, t_right),
    )
    for coordinate, label in zip((M, U, V), ("M", "U", "V")):
        certify_positive(gap.diff(coordinate), full_boxes, f"n={n} d/d{label}")

    # The kernel slice M=U=V=0 is treated by strict convexity in X,Y,Z.
    kernel_boxes = (
        (Fraction(0), Fraction(0)),
        (Fraction(0), Fraction(0)),
        (Fraction(0), Fraction(0)),
        (-DELTA, DELTA),
        (-DELTA, DELTA),
        (-DELTA, DELTA),
        (t_left, t_right),
    )
    hessian = [
        [restrict_zero(gap.diff(row).diff(column), (0, 1, 2)) for column in (X, Y, Z)]
        for row in (X, Y, Z)
    ]
    certify_positive(hessian[0][0], kernel_boxes, f"n={n} Hessian pivot 1")
    determinant_2 = hessian[0][0] * hessian[1][1] - hessian[0][1] ** 2
    certify_positive(determinant_2, kernel_boxes, f"n={n} Hessian pivot 2")
    determinant_3 = (
        hessian[0][0] * (hessian[1][1] * hessian[2][2] - hessian[1][2] ** 2)
        - hessian[0][1]
        * (hessian[0][1] * hessian[2][2] - hessian[1][2] * hessian[0][2])
        + hessian[0][2]
        * (hessian[0][1] * hessian[1][2] - hessian[1][1] * hessian[0][2])
    )
    certify_positive(determinant_3, kernel_boxes, f"n={n} Hessian pivot 3")


def main() -> None:
    for degree in (5, 6):
        check_degree(degree)
    print("PASS exact homogeneous regular quantitative collar")


if __name__ == "__main__":
    main()
