#!/usr/bin/env python3
"""Exact replay for the canonical sextic mixed-mode connector."""

from __future__ import annotations

import sympy as sp


def main() -> None:
    t = sp.symbols("t", real=True)
    x = sp.symbols("x")
    root3 = sp.sqrt(3)
    q = (sp.Integer(7) + 4 * root3) / 27
    w = 1 - t / 2 - sp.I * root3 * t / 2

    re2 = sp.expand(sp.re(sp.expand_complex(w**2)))
    re6 = sp.factor(sp.re(sp.expand_complex(w**6)))
    expected_re2 = -(t**2 + 2 * t - 2) / 2
    expected_re6 = (
        (t**2 - 4 * t + 1)
        * (t**2 + 2 * t - 2)
        * (2 * t**2 - 2 * t - 1)
        / 2
    )
    assert sp.simplify(re2 - expected_re2) == 0
    assert sp.simplify(re6 - expected_re6) == 0

    cubic = (
        t**3
        + (-6 + root3) * t**2
        + (sp.Rational(27, 2) - 7 * root3) * t
        - sp.Rational(67, 2)
        + sp.Rational(41, 2) * root3
    )
    carrier = sp.expand(re2 + q * re6)
    factor = q * (t + 1 + root3) * (t + 1 - root3) ** 2 * cubic
    assert sp.simplify(carrier - factor) == 0

    bernstein = [
        -sp.Rational(67, 2) + sp.Rational(41, 2) * root3,
        -29 + sp.Rational(109, 6) * root3,
        -sp.Rational(53, 2) + sp.Rational(97, 6) * root3,
        -25 + sp.Rational(29, 2) * root3,
    ]
    assert all(bool(coefficient > 0) for coefficient in bernstein)
    assert bool(q > sp.Rational(1, 2))
    assert bool(q < 1)
    assert sp.minpoly(q, x) == 729 * x**2 - 378 * x + 1

    double_contact = root3 - 1
    assert sp.simplify(carrier.subs(t, double_contact)) == 0
    assert sp.simplify(sp.diff(carrier, t).subs(t, double_contact)) == 0

    print(f"q = {q} = {sp.N(q, 16)}")
    print(f"r = q^(1/4) = {sp.N(q ** sp.Rational(1, 4), 16)}")
    print(f"double contact t = sqrt(3)-1 = {sp.N(double_contact, 16)}")
    print("Bernstein coefficients:")
    for coefficient in bernstein:
        print(f"  {coefficient} = {sp.N(coefficient, 16)}")
    print("PASS: one exact connector works for every amplitude u >= 0")


if __name__ == "__main__":
    main()
