#!/usr/bin/env python3
"""Exact checker for the concyclic smallest-gap Form-A selector counterexample."""

from fractions import Fraction as F

import sympy as sp


def unit_point(q: F) -> tuple[F, F]:
    return (1 - q * q) / (1 + q * q), 2 * q / (1 + q * q)


def cross(a: tuple[F, F], b: tuple[F, F]) -> F:
    return a[0] * b[1] - a[1] * b[0]


def dist_sq(a: tuple[F, F], b: tuple[F, F]) -> F:
    return (a[0] - b[0]) ** 2 + (a[1] - b[1]) ** 2


parameters = [F(1, 1200), F(8, 11), F(40, 13), F(-83, 27), F(-8, 11)]
roots = [unit_point(q) for q in parameters]
midpoint = ((roots[3][0] + roots[4][0]) / 2, (roots[3][1] + roots[4][1]) / 2)

assert all(x * x + y * y == 1 for x, y in roots)
assert all(cross(roots[k], roots[(k + 1) % 5]) > 0 for k in range(5))

selected_chord_sq = dist_sq(roots[3], roots[4])
other_chord_sqs = [dist_sq(roots[k], roots[(k + 1) % 5]) for k in [0, 1, 2, 4]]
assert all(selected_chord_sq < value for value in other_chord_sqs)


def product_norm_sq(z: tuple[F, F]) -> F:
    result = F(1)
    for root in roots:
        result *= dist_sq(z, root)
    return result


spoke_t = F(1, 10)
spoke_point = spoke_t * roots[4][0], spoke_t * roots[4][1]
spoke_margin = product_norm_sq(spoke_point) - 1
assert spoke_margin > 0

s = sp.symbols("s")
product = sp.Integer(1)
for x, y in roots:
    product *= (
        s * sp.Rational(midpoint[0].numerator, midpoint[0].denominator)
        - sp.Rational(x.numerator, x.denominator)
    ) ** 2 + (
        s * sp.Rational(midpoint[1].numerator, midpoint[1].denominator)
        - sp.Rational(y.numerator, y.denominator)
    ) ** 2

power_poly = sp.Poly(sp.cancel((product - 1) / s), s)
scale = sp.Rational(961, 2620148092600599198725979487928148264500000)
integer_power_poly = sp.Poly(sp.cancel(power_poly.as_expr() / scale), s)
assert integer_power_poly.degree() == 9
assert sp.expand(product - 1 - s * scale * integer_power_poly.as_expr()) == 0

degree = 10
power_coeffs = [integer_power_poly.nth(k) for k in range(10)]
bernstein_coeffs = [
    sp.factor(
        sum(
            power_coeffs[j] * sp.binomial(k, j) / sp.binomial(degree, j)
            for j in range(min(k, 9) + 1)
        )
    )
    for k in range(degree + 1)
]
assert all(value > 0 for value in bernstein_coeffs)

scale_to_integers = sp.Integer(1260)
integer_bernstein_coeffs = [sp.Integer(value * scale_to_integers) for value in bernstein_coeffs]
assert all(value > 0 for value in integer_bernstein_coeffs)
bernstein_expression = sum(
    integer_bernstein_coeffs[k]
    * sp.binomial(degree, k)
    * s**k
    * (1 - s) ** (degree - k)
    for k in range(degree + 1)
)
assert sp.expand(scale_to_integers * integer_power_poly.as_expr() - bernstein_expression) == 0

print(f"selected chord squared = {selected_chord_sq} ({float(selected_chord_sq):.12f})")
print("other-minus-selected squared chord margins:")
for value in other_chord_sqs:
    print(f"  {value - selected_chord_sq} ({float(value - selected_chord_sq):.12f})")
print(f"unsafe spoke exact margin = {spoke_margin} ({float(spoke_margin):.12f})")
print("degree-10 Bernstein coefficients are all positive")
print(f"smallest scaled coefficient = {min(integer_bernstein_coeffs)}")
print("PASS: the unique smallest gap has no admissible common radius")
