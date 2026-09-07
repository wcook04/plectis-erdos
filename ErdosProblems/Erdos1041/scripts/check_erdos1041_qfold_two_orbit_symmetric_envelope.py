#!/usr/bin/env python3
"""Exact algebra replay for the q-fold two-orbit symmetric envelope."""

from __future__ import annotations

import sympy as sp


def main() -> None:
    x, r, rho, c, p, n_real = sp.symbols(
        "x r rho c p N", positive=True, real=True
    )

    # Angular polarization: the quotient under the spectator square root is
    # decreasing in c=cos(phi) for 0<rho<1 and x>1.
    q_ang = (1 - 2 * rho * x * c + rho**2 * x**2) / (
        x**2 - 2 * rho * x * c + rho**2
    )
    q_ang_derivative = sp.factor(sp.diff(q_ang, c))
    expected_ang = (
        2
        * rho
        * x
        * (1 - x**2)
        * (1 - rho**2)
        / (x**2 - 2 * rho * x * c + rho**2) ** 2
    )
    assert sp.simplify(q_ang_derivative - expected_ang) == 0

    # Radius polarization after rho=p/r.  The exponent x^N cancels, so this
    # identity is valid for every real N.
    rho_sub = p / r
    f_r_reduced = (1 - r * x) * (1 + rho_sub * x) / (
        (x - r) * (x + rho_sub)
    )
    f_s_reduced = (1 - p * x**2) / (x**2 - p)
    radius_difference = sp.factor(f_s_reduced - f_r_reduced)
    expected_radius = (
        x
        * (x**2 - 1)
        * (1 + p)
        * (r**2 - p)
        / ((x**2 - p) * (p + r * x) * (x - r))
    )
    assert sp.simplify(radius_difference - expected_radius) == 0

    # The critical equation of the symmetric real-exponent profile is the
    # reciprocal quadratic displayed in the theorem.
    y = sp.symbols("Y", positive=True, real=True)
    log_derivative = (
        n_real / (2 * y) - p / (1 - p * y) - 1 / (y - p)
    )
    numerator = sp.factor(
        log_derivative * 2 * y * (1 - p * y) * (y - p)
    )
    quadratic = y**2 - (((n_real + 2) * p**2 + (n_real - 2)) / (n_real * p)) * y + 1
    assert sp.simplify(numerator + n_real * p * quadratic) == 0

    # At the capacity threshold the quadratic has a double root at Y=1.
    p0 = (n_real - 2) / (n_real + 2)
    coefficient = ((n_real + 2) * p**2 + (n_real - 2)) / (n_real * p)
    assert sp.simplify(coefficient.subs(p, p0) - 2) == 0

    # Exact q-fold translations.  No integrality assumption is used by the
    # symbolic identities; the theorem later takes integer n,q with n>2q.
    n, q = sp.symbols("n q", positive=True, integer=True)
    m = 2 * q
    N = n / q
    assert sp.simplify((N - 2) / (N + 2) - (n - m) / (n + m)) == 0
    assert sp.simplify((n - m) / (n + m) - (n - m) / (2 * n - (n - m))) == 0

    coefficient_base = ((N + 2) * p**2 + (N - 2)) / (N * p)
    coefficient_lift = ((n + m) * p**2 + (n - m)) / (n * p)
    assert sp.simplify(coefficient_base - coefficient_lift) == 0
    assert sp.simplify(N / 2 - n / m) == 0

    # Logarithmic critical equation and modulus exponent under y=z^q.
    ell = sp.symbols("L", real=True)
    assert sp.simplify(n - q * y * ell - q * (N - y * ell)) == 0
    assert sp.simplify(q * N - n) == 0

    # One exact rational nonintegral-exponent audit: N=5/2 (n=5,q=2),
    # p=1/16, r=1/2, x=3/2.  Squaring removes the harmless square root in
    # the raw angular profile; the radius-polarized comparator is strictly
    # larger at this interior point.
    sample = {
        p: sp.Rational(1, 16),
        r: sp.Rational(1, 2),
        x: sp.Rational(3, 2),
    }
    assert sp.simplify(radius_difference.subs(sample)) > 0
    assert sp.Rational(5, 2) > 2
    assert sp.Rational(1, 16) < (
        sp.Rational(5, 2) - 2
    ) / (sp.Rational(5, 2) + 2)

    print("q-fold two-orbit symmetric-envelope exact replay: PASS")


if __name__ == "__main__":
    main()
