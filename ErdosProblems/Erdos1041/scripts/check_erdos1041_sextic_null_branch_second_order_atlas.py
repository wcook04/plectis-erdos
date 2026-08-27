#!/usr/bin/env python3
"""Exact replay for the sextic null-branch second-order atlas."""

from __future__ import annotations

import random

import sympy as sp


def real(expr: sp.Expr) -> sp.Expr:
    return sp.expand(sp.re(sp.expand_complex(expr)))


def main() -> None:
    t, k = sp.symbols("t k", real=True)
    s, imaginary = sp.sqrt(3), sp.I
    omega = sp.Rational(1, 2) + imaginary * s / 2
    q0 = (7 + 4 * s) / 27
    branch_slope = sp.Rational(3, 2) * q0 * (s - 1)
    radius_slope = (21 + 11 * s) / 54

    slope_factor = 648 - 378 * s
    base_factor = -sp.Rational(9963, 2) + sp.Rational(5751, 2) * s
    square_factor = sp.Rational(212139, 4) - 30618 * s
    plus_offset = -117 + sp.Rational(135, 2) * s
    minus_offset = -9 + sp.Rational(9, 2) * s

    assert sp.simplify(square_factor - sp.Rational(2187, 4) * (97 - 56 * s)) == 0
    assert square_factor.is_positive

    plus_raw = sp.expand(
        base_factor * (k - branch_slope)
        + (slope_factor * (k - branch_slope)) ** 2 / 16
    )
    minus_raw = sp.expand(
        -base_factor * (k - branch_slope)
        + (slope_factor * (k + branch_slope)) ** 2 / 16
    )
    assert sp.simplify(
        plus_raw - plus_offset - square_factor * (k - radius_slope) ** 2
    ) == 0
    assert sp.simplify(
        minus_raw - minus_offset - square_factor * (k + radius_slope) ** 2
    ) == 0

    rows = []
    contacts = {0: s - 1, 2: 2 - s, 3: s - 1, 5: 2 - s}
    for pair, contact in contacts.items():
        w = sp.expand((1 - t) * omega**pair + t * omega ** ((pair + 1) % 6))
        n0 = sp.expand(-2 * real(w**2) - 2 * q0 * real(w**6))
        n1 = sp.expand(
            -2 * k * real(w**6)
            + 6 * (2 - s) * real(-imaginary * w)
            + 2 * real(imaginary * w**3)
        )
        curvature = sp.simplify(-sp.diff(n0, t, 2).subs(t, contact) / 2)
        slope = sp.factor(sp.diff(n1, t).subs(t, contact), extension=s)
        assert curvature == 4
        expected_center = branch_slope if pair in (0, 2) else -branch_slope
        expected_sign = 1 if pair in (0, 3) else -1
        expected_slope = expected_sign * slope_factor * (k - expected_center)
        assert sp.simplify(slope - expected_slope) == 0
        rows.append((pair, contact, curvature, slope))

    average = sp.simplify((2 * plus_offset + 2 * minus_offset) / 4)
    assert average == -63 + 36 * s
    assert bool(average < -sp.Rational(3, 5))

    rng = random.Random(104120260825)
    least_margin = None
    for _ in range(100_000):
        p, q, r = [sp.Rational(rng.randint(-100_000, 100_000), 1009) for _ in range(3)]
        contact_values = [p + q + r, -p - q + r, -p + q - r, p - q - r]
        profiles = [
            plus_offset + contact_values[0],
            plus_offset + contact_values[1],
            minus_offset + contact_values[2],
            minus_offset + contact_values[3],
        ]
        margin = -sp.Rational(3, 5) - min(profiles)
        assert margin > 0
        if least_margin is None or margin < least_margin:
            least_margin = margin

    print(f"radius slopes: +/-({radius_slope}) = +/-{sp.N(radius_slope, 16)}")
    print(f"plus offset:  {plus_offset} = {sp.N(plus_offset, 16)}")
    print(f"minus offset: {minus_offset} = {sp.N(minus_offset, 16)}")
    print(f"profile average: {average} = {sp.N(average, 16)}")
    for row in rows:
        print("pair/contact/curvature/slope:", row)
    print("least sampled symbolic margin above 3/5:", sp.N(least_margin, 16))
    print("PASS: exact optimized second-order four-connector atlas")


if __name__ == "__main__":
    main()
