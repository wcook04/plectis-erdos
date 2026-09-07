#!/usr/bin/env python3
"""Exact replay for the GP3 endpoint switch-square reduction."""

from fractions import Fraction as Q

import sympy as sp


def main() -> None:
    a, b, c, R = sp.symbols("a b c R", positive=True)
    F = b * c - a * (b + c)
    m_stat = -sp.Rational(1, 2) * (a * b / c + a * c / b + b * c / a)
    m_end = a - b - c
    square = F**2 / (2 * a * b * c)

    assert sp.factor(m_end - m_stat - square) == 0
    lhs = sp.expand(2 * a * b * c * (m_end - m_stat))
    assert sp.factor(lhs - F**2) == 0

    s_stat = R + (a + b + c) / 2 + m_stat
    s_end = R + (a + b + c) / 2 + m_end
    assert sp.factor(s_end - s_stat - square) == 0

    # Strict endpoint specimen: 1/a > 1/b+1/c and positive correction.
    av, bv, cv = Q(1, 3), Q(1), Q(2)
    fv = bv * cv - av * (bv + cv)
    assert fv == 1 > 0
    correction = fv * fv / (2 * av * bv * cv)
    assert correction == Q(3, 4)

    # Exact switch specimen: 1/a=1/b+1/c, so both formulae coincide.
    av, bv, cv = Q(6, 5), Q(2), Q(3)
    fv = bv * cv - av * (bv + cv)
    assert fv == 0
    msv = -Q(1, 2) * (av * bv / cv + av * cv / bv + bv * cv / av)
    mev = av - bv - cv
    assert msv == mev == Q(-19, 5)

    print("three-exterior endpoint switch square: exact replay PASS")
    print("checked: symbolic perfect square, surplus lift, strict endpoint and switch specimens")


if __name__ == "__main__":
    main()
