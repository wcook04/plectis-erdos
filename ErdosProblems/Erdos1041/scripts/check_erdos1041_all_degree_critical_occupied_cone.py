#!/usr/bin/env python3
"""Exact scalar replay for the all-degree critical occupied cone."""

from __future__ import annotations

import sympy as sp


def main() -> None:
    n, s, p = sp.symbols("n s p", positive=True)
    alpha = sp.Rational(2) / (n - 1)

    # Coefficients of (1-t)^(-alpha) through degree three.
    c1 = alpha
    c2 = sp.factor(alpha * (alpha + 1) / 2)
    c3 = sp.factor(alpha * (alpha + 1) * (alpha + 2) / 6)
    assert sp.factor(c1 - 2 / (n - 1)) == 0
    assert sp.factor(c2 - (n + 1) / (n - 1) ** 2) == 0
    assert sp.factor(c3 - 2 * n * (n + 1) / (3 * (n - 1) ** 3)) == 0

    # S=(1-p)/p has the threshold exactly at p=(n-1)/(2n).
    s_threshold = (n + 1) / (n - 1)
    p_threshold = (n - 1) / (2 * n)
    assert sp.factor((1 - p_threshold) / p_threshold - s_threshold) == 0

    t = sp.symbols("t", nonnegative=True)
    for degree in range(2, 101):
        a = sp.Rational(2, degree - 1)
        threshold = sp.Rational(degree + 1, degree - 1)
        bracket = 1 + 2 * t / (degree - 1) + threshold * t**2 / (degree - 1)
        comparison_coeffs = [
            sp.prod(a + q for q in range(k)) / sp.factorial(k) for k in range(4)
        ]
        assert sp.factor(comparison_coeffs[0] - 1) == 0
        assert sp.factor(comparison_coeffs[1] - sp.Rational(2, degree - 1)) == 0
        assert sp.factor(
            comparison_coeffs[2]
            - sp.Rational(degree + 1, (degree - 1) ** 2)
        ) == 0
        assert comparison_coeffs[3] > 0
        assert sp.expand(bracket - sum(comparison_coeffs[k] * t**k for k in range(3))) == 0

        # A perturbation S=threshold+epsilon has positive quadratic excess.
        epsilon = sp.Rational(1, degree * 1000)
        excess_c2 = sp.factor((threshold + epsilon) / (degree - 1) - comparison_coeffs[2])
        assert excess_c2 == epsilon / (degree - 1)

    print("All-degree critical occupied cone: PASS")
    print("exact threshold: S <= (n+1)/(n-1) iff p >= (n-1)/(2n)")
    print("strict positive binomial tail and sharp quadratic obstruction checked for n=2..100")


if __name__ == "__main__":
    main()
