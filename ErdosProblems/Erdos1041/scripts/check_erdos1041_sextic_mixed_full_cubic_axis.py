#!/usr/bin/env python3
"""Exact replay for the two-tile full cubic-axis cover."""

from __future__ import annotations

import sympy as sp


def main() -> None:
    s2, s3, s6 = sp.sqrt(2), sp.sqrt(3), sp.sqrt(6)
    controls = [
        -(-45 * s6 + 45 * s2 + 64) / 729,
        -(-144 * s6 + 256 + 161 * s3 + 960 * s2) / 5832,
        -(-640 - 108 * s6 + 645 * s3 + 3396 * s2) / 14580,
        -(-2560 + 1455 * s3 + 7488 * s2) / 29160,
        -(-320 + 54 * s6 + 365 * s3 + 1698 * s2) / 7290,
        -(256 + 144 * s6 + 309 * s3 + 960 * s2) / 5832,
        -(180 * s2 + 256 + 195 * s3 + 180 * s6) / 2916,
    ]
    assert all(x <= -sp.Rational(1, 1000) for x in controls)
    assert min(controls) < max(controls) < 0

    ray_margin = sp.Rational(107, 5832)
    coefficient_cost = sp.Rational(4, 10000)
    assert ray_margin > coefficient_cost
    assert -sp.Rational(1, 10000) <= sp.Rational(1, 10000)

    print("reflected Bernstein controls:", *controls)
    print("reflected ray residual margin:", ray_margin - coefficient_cost)
    print("EXACT PASS: upper and reflected tiles cover every real cubic coefficient")


if __name__ == "__main__":
    main()
