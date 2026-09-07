#!/usr/bin/env python3
"""Symbolic probe for the reflection-stationary three-active value split."""

from __future__ import annotations

import sympy as sp


a, b, x, y, c = sp.symbols("a b x y c", positive=True, real=True)


def numerator(q: sp.Expr, r: sp.Expr, cosine: sp.Expr) -> sp.Expr:
    return q**2 + r**2 - 2 * q * r * cosine


def denominator(q: sp.Expr, r: sp.Expr, cosine: sp.Expr) -> sp.Expr:
    return 1 + q**2 * r**2 - 2 * q * r * cosine


def q_atom(q: sp.Expr, r: sp.Expr, cosine: sp.Expr) -> sp.Expr:
    return sp.Rational(1, 2) * (
        (q**2 - r**2) / numerator(q, r, cosine)
        + (1 - q**2 * r**2) / denominator(q, r, cosine)
    )


def radial_atom(q: sp.Expr, r: sp.Expr, cosine: sp.Expr) -> sp.Expr:
    return (
        r
        * (1 - q**2)
        * (r * (1 + q**2) - q * (1 + r**2) * cosine)
        / (numerator(q, r, cosine) * denominator(q, r, cosine))
    )


def angular_atom(q: sp.Expr, r: sp.Expr, cosine: sp.Expr) -> sp.Expr:
    return (
        q
        * r
        * (1 - q**2)
        * (1 - r**2)
        / (numerator(q, r, cosine) * denominator(q, r, cosine))
    )


def polynomial_system(degree: int) -> tuple[sp.Expr, sp.Expr, sp.Expr, sp.Expr]:
    double_cosine = 2 * c**2 - 1
    q0 = -degree + q_atom(x, a, 1) + 2 * q_atom(x, b, c)
    q1 = (
        -degree
        + q_atom(y, b, 1)
        + q_atom(y, a, c)
        + q_atom(y, b, double_cosine)
    )

    angular_cross = angular_atom(x, b, c)
    angular_reverse = angular_atom(y, a, c)
    angular_pair = angular_atom(y, b, double_cosine)
    angular_other = angular_reverse + 4 * c * angular_pair
    weight = sp.cancel(-angular_other / (2 * angular_cross - angular_other))
    twin_weight = (1 - weight) / 2

    radial0 = weight * radial_atom(x, a, 1) + 2 * twin_weight * radial_atom(y, a, c)
    radial1 = (
        weight * radial_atom(x, b, c)
        + twin_weight * radial_atom(y, b, 1)
        + twin_weight * radial_atom(y, b, double_cosine)
    )
    radial = sp.cancel(radial0 - radial1)

    barrier0 = (
        numerator(x, a, 1)
        / denominator(x, a, 1)
        * (numerator(x, b, c) / denominator(x, b, c)) ** 2
    )
    barrier1 = (
        numerator(y, b, 1)
        / denominator(y, b, 1)
        * numerator(y, a, c)
        / denominator(y, a, c)
        * numerator(y, b, double_cosine)
        / denominator(y, b, double_cosine)
    )
    value_ratio_minus_one = sp.cancel((y / x) ** (2 * degree) * barrier0 / barrier1 - 1)
    return tuple(
        sp.expand(sp.fraction(sp.cancel(expression))[0])
        for expression in (q0, q1, radial, value_ratio_minus_one)
    )


def main() -> None:
    for degree in (5, 6):
        q0, q1, radial, value = polynomial_system(degree)
        for label, polynomial in (
            ("Q0", q0),
            ("Q1", q1),
            ("radial", radial),
            ("value", value),
        ):
            poly = sp.Poly(polynomial, x, y, c)
            print(
                f"degree-{degree} {label}: "
                f"degrees=({poly.degree(x)},{poly.degree(y)},{poly.degree(c)}), "
                f"terms={len(poly.terms())}"
            )


if __name__ == "__main__":
    main()
