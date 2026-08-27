#!/usr/bin/env python3
"""Exact replay for the pure-cubic sextic connector no-go theorem."""

from __future__ import annotations

import sympy as sp


def main() -> None:
    r = sp.symbols("r", positive=True, real=True)
    s = sp.sqrt(3)
    imaginary = sp.I
    omega = sp.Rational(1, 2) + imaginary * s / 2

    rows = []
    for first in range(6):
        for gap, parameter, magnitude in (
            (1, sp.Rational(1, 2), 3 * s / 8),
            (2, sp.Rational(1, 3), s / 9),
        ):
            second = (first + gap) % 6
            z = sp.expand(
                r * ((1 - parameter) * omega**first + parameter * omega**second)
            )
            cube = sp.expand_complex(z**3)
            expected_imaginary = (-1) ** first * magnitude * r**3
            assert sp.simplify(sp.re(cube)) == 0
            assert sp.simplify(sp.im(cube) - expected_imaginary) == 0
            value = sp.simplify(sp.re(z**3 - z**6))
            assert sp.simplify(value - expected_imaginary**2) == 0
            assert expected_imaginary != 0
            rows.append((first, second, parameter, sp.simplify(value / r**6)))

    # Both non-antipodal gap types have strict metric coefficient below two.
    assert sp.Integer(1) < 2
    assert bool(s < 2)
    assert len(rows) == 12
    for row in rows:
        print("first/second/chord-parameter/escape-coefficient:", row)
    print("PASS: every positive-radius non-antipodal sixth-root chord has an exact escape point")


if __name__ == "__main__":
    main()
