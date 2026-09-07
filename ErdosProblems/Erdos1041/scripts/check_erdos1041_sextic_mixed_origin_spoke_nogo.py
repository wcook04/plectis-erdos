#!/usr/bin/env python3
"""Exact replay for the mixed spoke obstruction and its truncated repair."""

from __future__ import annotations

import sympy as sp


def main() -> None:
    lam, t = sp.symbols("lam t", real=True)
    s2, s3 = sp.sqrt(2), sp.sqrt(3)
    a = [-s3 * lam / 2, -s3 * lam / 2, 0, s3 * lam / 2, s3 * lam / 2, 0]
    b = [
        -s2 * (s3 + 1) / 4,
        s2 / 2,
        s2 * (s3 - 1) / 4,
    ] * 2

    alpha, beta = 5 * sp.pi / 6, 13 * sp.pi / 12
    for j in range(6):
        assert sp.simplify(a[j] - lam * sp.cos(alpha + j * sp.pi / 3)) == 0
        assert sp.simplify(b[j] - sp.cos(beta + 2 * j * sp.pi / 3)) == 0

    def ray(j: int, x: sp.Expr) -> sp.Expr:
        return sp.expand((x - x**5) * a[j] + (x**2 - x**4) * b[j] - x**6)

    v1 = sp.simplify(ray(1, sp.Rational(1, 2)).subs(lam, sp.Rational(1, 4)))
    v2 = sp.simplify(ray(2, sp.Rational(1, 4)))
    v4 = sp.simplify(ray(4, sp.Rational(1, 2)).subs(lam, 0))
    assert v1 == (24 * s2 - 15 * s3 - 4) / 256
    assert all(bool(sp.N(v) > 0) for v in (v1, v2, v4))

    escaping = {1, 2, 4, 5}
    for j in range(6):
        for gap in (1, 2):
            assert j in escaping or (j + gap) % 6 in escaping

    # At lambda=1/4, the adjacent pair (0,1) is repaired by truncating at
    # radius 2/3.  Reconstruct the exact chord and all degree-six Bernstein
    # controls directly from the complex paired model.
    u = sp.symbols("u", real=True)
    I = sp.I
    A = -s3 / 8 + I / 8
    B = -(sp.sqrt(6) + s2) / 4 + I * (s2 - sp.sqrt(6)) / 4
    omega = sp.Rational(1, 2) + I * s3 / 2
    z = sp.Rational(2, 3) * ((1 - u) + u * omega)
    chord = sp.simplify(
        sp.re(sp.expand_complex(A * z + B * z**2 - sp.conjugate(B) * z**4
                                - sp.conjugate(A) * z**5 - z**6))
    )
    poly = sp.Poly(sp.expand(chord), u)
    power = [poly.nth(i) for i in range(7)]
    bernstein = [
        sp.simplify(
            sum(power[i] * sp.binomial(k, i) / sp.binomial(6, i)
                for i in range(k + 1))
        )
        for k in range(7)
    ]
    expected = [
        -(180 * s2 + 256 + 195 * s3 + 180 * sp.sqrt(6)) / 2916,
        (-276 * sp.sqrt(6) - 235 * s3 - 128 + 132 * s2) / 2916,
        (-1752 * sp.sqrt(6) - 1375 * s3 + 640 + 1536 * s2) / 14580,
        (-1872 * sp.sqrt(6) - 1455 * s3 + 1280 + 1872 * s2) / 14580,
        (-1644 * sp.sqrt(6) - 1375 * s3 + 640 + 1860 * s2) / 14580,
        (-204 * sp.sqrt(6) - 235 * s3 - 128 + 348 * s2) / 2916,
        (-195 * s3 - 256 + 360 * s2) / 2916,
    ]
    assert all(sp.simplify(x - y) == 0 for x, y in zip(bernstein, expected))
    assert all(bool(sp.N(x) < 0) for x in bernstein)

    # The rational radical bounds used in Lean reduce direction one's tail
    # to -t Q(t)/24.  Its shifted expansion has only positive coefficients.
    q = 24 * t**5 - 5 * t**4 + 18 * t**3 - 18 * t + 5
    shifted = sp.expand(81 * q.subs(t, (u + 2) / 3))
    assert shifted == 8 * u**5 + 75 * u**4 + 334 * u**3 + 844 * u**2 + 642 * u + 41

    print("exact endpoint witnesses:", v1, v2, v4)
    print("exact chord Bernstein controls:", *bernstein)
    print("EXACT PASS: complete spokes fail, while radius 2/3 repairs pair (0,1)")


if __name__ == "__main__":
    main()
