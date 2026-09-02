#!/usr/bin/env python3
"""Exact replay for exterior radial water-filling and saturation rigidity."""

from __future__ import annotations

import sympy as sp


def main() -> None:
    x, rho, c, r, p = sp.symbols("x rho c r p", positive=True, real=True)

    # Angular polarization.
    q_ang = (1 - 2 * rho * x * c + rho**2 * x**2) / (
        x**2 - 2 * rho * x * c + rho**2
    )
    expected_ang = (
        2
        * rho
        * x
        * (1 - x**2)
        * (1 - rho**2)
        / (x**2 - 2 * rho * x * c + rho**2) ** 2
    )
    assert sp.simplify(sp.diff(q_ang, c) - expected_ang) == 0

    # Convexity and monotonicity in logarithmic radius of the antipodal
    # spectator factor g=(1+rho*x)/(x+rho).
    g_log = sp.log((1 + rho * x) / (x + rho))
    first_log_radius = sp.factor(rho * sp.diff(g_log, rho))
    second_log_radius = sp.factor(rho * sp.diff(first_log_radius, rho))
    expected_first = rho * (x**2 - 1) / ((1 + rho * x) * (x + rho))
    expected_second = (
        -rho
        * x
        * (rho - 1)
        * (rho + 1)
        * (x - 1)
        * (x + 1)
        / ((rho + x) ** 2 * (rho * x + 1) ** 2)
    )
    assert sp.simplify(first_log_radius - expected_first) == 0
    assert sp.simplify(second_log_radius - expected_second) == 0

    # Saturation Riccati equation reduces to zY'=mY.
    n, m, Y, zY = sp.symbols("n m Y zY", positive=True, real=True)
    p0 = (n - m) / (n + m)
    B = (Y - p0) / (1 - p0 * Y)
    zB = (1 - p0**2) * zY / (1 - p0 * Y) ** 2
    riccati = sp.factor(n * B - zB + n * p0 * (B - 1) ** 2 / (1 + p0) ** 2)
    assert sp.factor(riccati) == sp.factor(
        4 * m * n * (m * Y - zY) / (m * Y - n * Y + m + n) ** 2
    )

    # Capacity endpoint, Kovalev--Yang endpoint, and their exact gap.
    d = n - m
    p_k = d * (d + 1) / (n * (n + 1))
    expected_gap = d * m * (m - 1) / ((n + m) * n * (n + 1))
    assert sp.simplify(p0 - p_k - expected_gap) == 0
    assert sp.simplify(n - m / (d + 1) - d * (n + 1) / (d + 1)) == 0

    # Exact d=2 obstruction.
    xr = sp.Rational(3, 2)
    pr = sp.Rational(1, 8)
    rr = sp.Rational(1, 2)
    ur = rr
    water_5 = sp.factor(
        xr**5
        * (1 - rr * xr)
        / (xr - rr)
        * ((1 + rr * xr) / (xr + rr)) ** 2
    )
    assert water_5 == sp.Rational(11907, 8192)
    assert water_5 > sp.Rational(11, 8)
    assert 3 * (1 + pr) / (1 - pr) == sp.Rational(27, 7) < 5

    y5 = (sp.Rational(17) + 3 * sp.sqrt(21)) / 10
    b5_cubed = sp.simplify(y5**5 * ((1 - pr * y5) / (y5 - pr)) ** 3)
    assert b5_cubed == sp.Rational(9059, 6250) + sp.Rational(1431, 6250) * sp.sqrt(21)
    assert 1840271**2 - 21 * 366336**2 == 568353990625 > 0
    assert sp.N(b5_cubed - sp.Rational(11, 8) ** 3, 80) < 0

    # Exact d=3 obstruction.
    water_6 = sp.factor(
        xr**6
        * (1 - rr * xr)
        / (xr - rr)
        * ((1 + ur * xr) / (xr + ur)) ** 2
    )
    assert water_6 == sp.Rational(35721, 16384)
    assert water_6 > sp.Rational(17, 8)
    assert sp.Rational(27, 7) < 6

    y6 = (sp.Rational(67, 16) + sp.sqrt(sp.Rational(3465, 256))) / 2
    b6_cubed = sp.simplify(y6**6 * ((1 - pr * y6) / (y6 - pr)) ** 3)
    expected_b6 = sp.Rational(76623025309, 17179869184) + sp.Rational(
        3805648605, 17179869184
    ) * sp.sqrt(385)
    assert sp.simplify(b6_cubed - expected_b6) == 0
    assert 88229899107**2 - 385 * 3805648605**2 == 2208574994107097677824 > 0
    assert sp.N(b6_cubed - sp.Rational(17, 8) ** 3, 80) < 0

    print("exterior radial water-filling and saturation rigidity: PASS")


if __name__ == "__main__":
    main()
