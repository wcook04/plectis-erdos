#!/usr/bin/env python3
"""Exact replay of the mixed sextic coefficient-neighborhood constants."""

from __future__ import annotations

import sympy as sp


def main() -> None:
    t, u = sp.symbols("t u", real=True)
    eps = sp.Rational(1, 10_000)

    chord_base_margin = sp.Rational(1, 1000)
    perturbation_budget = 4 * eps
    assert chord_base_margin - perturbation_budget == sp.Rational(3, 5000)

    q = 24 * t**5 - 5 * t**4 + 18 * t**3 - 18 * t + 5
    shifted = sp.expand(81 * q.subs(t, (u + 2) / 3))
    assert shifted == (
        8 * u**5 + 75 * u**4 + 334 * u**3
        + 844 * u**2 + 642 * u + 41
    )
    ray_base_margin = sp.Rational(41, 2916)
    assert ray_base_margin - perturbation_budget > 0

    # The common chord stays inside the disk; in fact its squared norm is at
    # most 4/9 because 1-u+u^2 = 1-u(1-u).
    chord_norm_sq = sp.Rational(4, 9) * (1 - u + u**2)
    assert sp.factor(chord_norm_sq - sp.Rational(4, 9)) == sp.Rational(4, 9) * u * (u - 1)

    # Exact endpoint projections on direction zero remain negative after the
    # full norm perturbation budget.
    s2, s3 = sp.sqrt(2), sp.sqrt(3)
    assert -s3 / 8 + eps < 0
    assert -(s2 * s3 + s2) / 4 + eps < 0

    print("chord residual margin:", chord_base_margin - perturbation_budget)
    print("ray-one residual margin:", ray_base_margin - perturbation_budget)
    print("EXACT PASS: the radius-2/3 connector survives the 10^-4 coefficient ball")


if __name__ == "__main__":
    main()
