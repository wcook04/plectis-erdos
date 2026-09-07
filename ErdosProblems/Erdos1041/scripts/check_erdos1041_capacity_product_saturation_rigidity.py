#!/usr/bin/env python3
"""Exact algebra replay for CapacityProductSaturationRigidity.md."""

from fractions import Fraction

import sympy as sp


def symbolic_replay() -> None:
    n, m, p, b, y, c2 = sp.symbols("n m p b y c2", positive=True)

    p0 = (n - m) / (n + m)
    assert sp.factor((1 - p0) / (1 + p0) - m / n) == 0

    A = n * p / (1 + p) ** 2
    assert sp.factor(A * (1 / p - p) - n * (1 - p) / (1 + p)) == 0
    assert sp.factor((A * (1 / p - p) - m).subs(p, p0)) == 0

    ode_rhs = n * b + n * p * (b - 1) ** 2 / (1 + p) ** 2
    ode_factored = A * (b + p) * (b + 1 / p)
    assert sp.factor(ode_rhs - ode_factored) == 0

    log_ratio_derivative = 1 / (b + p) - 1 / (b + 1 / p)
    assert sp.factor(log_ratio_derivative - (1 / p - p) / ((b + p) * (b + 1 / p))) == 0

    # If (B+p)/(B+1/p)=c z^m and y=c z^m, solving gives (12).
    Bsol = (y / p - p) / (1 - y)
    assert sp.factor((Bsol + p) / (Bsol + 1 / p) - y) == 0

    # On |z|=1, |y|^2=|c|^2.  Re(y) cancels exactly.
    re_y = sp.symbols("re_y", real=True)
    lhs_sq = c2 / p**2 + p**2 - 2 * re_y
    rhs_sq = 1 + c2 - 2 * re_y
    asserted = (1 - p**2) * (c2 / p**2 - 1)
    assert sp.factor(lhs_sq - rhs_sq - asserted) == 0


def rational_regular_regressions() -> None:
    # At a fibre point z^m=1 the regular endpoint model has |B'|=n.
    for n, m in [(5, 3), (6, 3), (8, 2), (11, 4)]:
        p = Fraction(n - m, n + m)
        fibre_speed = Fraction(m) * (1 + p) / (1 - p)
        assert fibre_speed == n

        clark_mass = (1 - p) / (1 + p)
        assert clark_mass == Fraction(m, n)
        assert Fraction(m, 1) / fibre_speed == clark_mass

        A = Fraction(n) * p / (1 + p) ** 2
        exponent = A * (1 / p - p)
        assert exponent == m


def main() -> None:
    symbolic_replay()
    rational_regular_regressions()
    print("capacity-product saturation rigidity: exact replay PASS")
    print("checked: endpoint ratio, ODE factorization, exponent, inner modulus, regular models")


if __name__ == "__main__":
    main()
