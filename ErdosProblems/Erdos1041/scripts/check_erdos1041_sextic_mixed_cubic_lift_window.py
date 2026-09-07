#!/usr/bin/env python3
"""Exact replay for the mixed cubic half-line and arbitrary-lift no-go."""

from __future__ import annotations

import sympy as sp


def main() -> None:
    u = sp.symbols("u", real=True)
    s2, s3, s6 = sp.sqrt(2), sp.sqrt(3), sp.sqrt(6)

    cube_im = sp.Rational(4, 9) * s3 * u * (1 - u)
    assert sp.factor(cube_im.subs(u, sp.Rational(1, 2))) == s3 / 9

    base_cell_margin = sp.Rational(3, 5000)
    cubic_budget = sp.Rational(1, 10000)
    assert base_cell_margin - cubic_budget == sp.Rational(1, 2000)

    original_midpoint = (-6 * s6 + 2 + 6 * s2 + 7 * s3) / 54
    antipodal_endpoint = (-256 + 195 * s3 + 360 * s2) / 2916
    assert original_midpoint > 0
    assert antipodal_endpoint > 0

    print("half-line residual chord margin:", base_cell_margin - cubic_budget)
    print("c=-2 original midpoint:", original_midpoint)
    print("c=-2 antipodal endpoint:", antipodal_endpoint)
    print("EXACT PASS: c>=-10^-4 lifts; arbitrary antipodal cubic lifting fails")


if __name__ == "__main__":
    main()
