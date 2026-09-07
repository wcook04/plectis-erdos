#!/usr/bin/env python3
"""Exact two-jet replay and quantitative constants for finite sextic transfer."""

from __future__ import annotations

import math

import sympy as sp


def real(expr: sp.Expr) -> sp.Expr:
    return sp.expand(sp.re(sp.expand_complex(expr)))


def bernstein_coefficients(poly: sp.Expr, variable: sp.Symbol) -> list[sp.Expr]:
    p = sp.Poly(sp.expand(poly), variable)
    degree = p.degree()
    power = [p.coeff_monomial(variable**j) for j in range(degree + 1)]
    return [
        sp.simplify(
            sum(
                power[j] * sp.binomial(k, j) / sp.binomial(degree, j)
                for j in range(k + 1)
            )
        )
        for k in range(degree + 1)
    ]


def main() -> None:
    t, beta, p, q, u = sp.symbols("t beta p q u", real=True)
    s, imaginary = sp.sqrt(3), sp.I
    omega = sp.Rational(1, 2) + imaginary * s / 2
    q0 = (7 + 4 * s) / 27
    branch_slope = sp.Rational(3, 2) * q0 * (s - 1)
    radius_slope = (21 + 11 * s) / 54
    h = (3 - s) / 2
    r0 = q0 ** sp.Rational(1, 4)

    plus_offset = -117 + sp.Rational(135, 2) * s
    minus_offset = -9 + sp.Rational(9, 2) * s
    data = [
        (0, s - 1, 1, plus_offset + p + q + u),
        (2, 2 - s, 1, plus_offset - p - q + u),
        (3, s - 1, -1, minus_offset - p + q - u),
        (5, 2 - s, -1, minus_offset + p - q - u),
    ]

    assert bool(sp.Rational(1, 2) < q0 < 1)
    assert bool(0 < branch_slope < 1)
    assert bool(0 < radius_slope < 1)

    rows = []
    for pair, contact, sign, profile in data:
        rho4 = q0 + sign * radius_slope * beta
        branch4 = q0 + branch_slope * beta
        rho = rho4 ** sp.Rational(1, 4)
        branch_radius = branch4 ** sp.Rational(1, 4)
        a1 = p * r0 / (2 * h)
        b1 = -u * r0 / (2 * h)
        theta = q / (4 * h**2)
        w = sp.expand(((1 - t) + t * omega) * omega**pair)
        normalized = sp.expand(
            -2 * real(w**2)
            - 2 * rho4 * real(w**6)
            + 6 * beta * (branch_radius / rho) * (2 - s) * real(-imaginary * w)
            + 2 * beta * (rho / branch_radius) * real(imaginary * w**3)
            + 2 * beta**2 / rho * real((a1 + imaginary * b1) * w)
            + 2 * beta**2 * theta * real(-imaginary * w**2)
        )
        n0 = sp.simplify(normalized.subs(beta, 0))
        n1 = sp.simplify(sp.diff(normalized, beta).subs(beta, 0))
        n2 = sp.simplify(sp.diff(normalized, beta, 2).subs(beta, 0) / 2)
        lam = sp.factor(sp.diff(n1, t).subs(t, contact), extension=s)
        constant = sp.simplify(n2.subs(t, contact))

        assert sp.simplify(n0.subs(t, contact)) == 0
        assert sp.simplify(sp.diff(n0, t).subs(t, contact)) == 0
        assert sp.simplify(sp.diff(n0, t, 2).subs(t, contact)) == -8
        assert sp.simplify(n1.subs(t, contact)) == 0
        assert sp.powsimp(sp.simplify(constant + lam**2 / 16 - profile), force=True) == 0

        carrier = sp.cancel(-n0 / (t - contact) ** 2 - sp.Rational(2, 5))
        carrier = sp.factor(carrier, extension=s)
        coeffs = bernstein_coefficients(carrier, t)
        assert all(bool(c > 0) for c in coeffs)

        n0_third = bernstein_coefficients(sp.diff(n0, t, 3), t)
        n1_first = bernstein_coefficients(sp.diff(n1, t), t)
        n1_second = bernstein_coefficients(sp.diff(n1, t, 2), t)
        assert max(abs(float(c)) for c in n0_third) < 240
        assert max(abs(float(c)) for c in n1_first) < 24
        assert max(abs(float(c)) for c in n1_second) < 72

        def box_bound(poly: sp.Expr) -> float:
            base = sp.expand(poly.subs({p: 0, q: 0, u: 0}))
            pieces = [sp.diff(poly, variable) for variable in (p, q, u)]
            base_bound = max(abs(float(c)) for c in bernstein_coefficients(base, t))
            piece_bounds = [
                max(abs(float(c)) for c in bernstein_coefficients(piece, t))
                for piece in pieces
            ]
            return base_bound + 78 * sum(piece_bounds)

        assert box_bound(n2) < 1000
        assert box_bound(sp.diff(n2, t)) < 1200
        rows.append((pair, contact, lam, constant, coeffs))

    average = sp.simplify((2 * plus_offset + 2 * minus_offset) / 4)
    assert average == -63 + 36 * s
    assert bool(average < -sp.Rational(3, 5))
    assert 40 * 100**3 + 36 * 100**2 + 1200 * 100 + 1000 == 40_481_000
    assert sp.Rational(40_500_000, 1_000_000_000) < sp.Rational(1, 20)
    assert -sp.Rational(2, 5) * 100**2 + 24 * 100 + 1000 + 1 < -sp.Rational(1, 2)
    assert bool(q0 - sp.Rational(1, 2) > sp.Rational(1, 64))
    assert sp.Rational(1, 64) - sp.Rational(1, 1_000_000_000) > sp.Rational(1, 70)
    assert sp.Rational(7, 10) * sp.Rational(1, 70) == sp.Rational(1, 100)
    assert sp.Rational(5, 1_000_000_000) + sp.Rational(234, 10**18) < sp.Rational(1, 200)

    # Independent floating-point stress of the exact finite family.  This is
    # evidence only; the theorem rests on the displayed analytic budgets.
    import numpy as np
    from numpy.polynomial import Polynomial

    rng = np.random.default_rng(104120260825)
    least = math.inf
    for _ in range(20_000):
        pp, qq, uu = rng.uniform(-78, 78, size=3)
        profiles = [
            float(plus_offset) + pp + qq + uu,
            float(plus_offset) - pp - qq + uu,
            float(minus_offset) - pp + qq - uu,
            float(minus_offset) + pp - qq - uu,
        ]
        least = min(least, -min(profiles))
    assert least > 0.6

    for pair, contact, lam, constant, coeffs in rows:
        print("pair/contact/lambda:", pair, contact, lam)
        print("  canonical quadratic-floor Bernstein:", coeffs)
    print("profile average:", average, "=", sp.N(average, 16))
    print("local remainder coefficient: 40481000 < 40500000")
    print("PASS: exact finite-beta sextic null-core transfer constants")


if __name__ == "__main__":
    main()
