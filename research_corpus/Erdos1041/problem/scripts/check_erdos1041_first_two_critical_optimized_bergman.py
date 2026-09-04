#!/usr/bin/env python3
"""Deterministic checks for the optimized first-merge Bergman theorem.

The symbolic checks verify the derivative and threshold identities exactly.
The decimal sweep is only a regression check for strict monotonicity and
dominance; the analytic proof in the companion note remains authority.
"""

from __future__ import annotations

import math

import sympy as sp


def check_symbolic_derivative() -> None:
    t, b, a = sp.symbols("t b a", positive=True)
    cost = t**a * sp.log((t + b) / (t - b))
    expected = t ** (a - 1) * (
        a * sp.log((t + b) / (t - b)) - 2 * b * t / (t**2 - b**2)
    )
    assert sp.simplify(sp.diff(cost, t) - expected) == 0


def check_artanh_barrier_derivative() -> None:
    q = sp.symbols("q", positive=True)
    gap = q / (1 - q**2) - sp.atanh(q)
    assert sp.simplify(sp.diff(gap, q) - 2 * q**2 / (1 - q**2) ** 2) == 0
    assert sp.simplify(gap.subs(q, 0)) == 0


def cost(n: int, beta: float, level: float) -> float:
    return level ** (2.0 / n) * math.log((level + beta) / (level - beta))


def check_monotonicity_and_dominance() -> None:
    for n in range(3, 81):
        degree_factor = (n - 1) ** (-2.0 / n)
        for beta in (0.01, 0.1, 0.49, 0.9, 0.999):
            levels = [beta + (1.0 - beta) * j / 64 for j in range(1, 65)]
            values = [cost(n, beta, level) for level in levels]
            assert all(left > right for left, right in zip(values, values[1:]))
            # Raising the allowed level to one can only improve the exact
            # first-merge scalar cost used by the theorem.
            assert degree_factor * values[-1] < degree_factor * values[0]


def check_direct_ratio_corollary() -> None:
    for n in range(3, 81):
        threshold = math.tanh((n - 1) ** (2.0 / n))
        for scale in (0.1, 0.5, 0.9, 0.999999):
            q = scale * threshold
            barrier = math.log((1 + q) / (1 - q))
            assert (n - 1) ** (-2.0 / n) * barrier < 2


def main() -> None:
    check_symbolic_derivative()
    check_artanh_barrier_derivative()
    check_monotonicity_and_dominance()
    check_direct_ratio_corollary()
    print("PASS: exact derivative and artanh-barrier identities")
    print("PASS: optimized-level monotonicity regression through degree 80")
    print("PASS: direct-ratio sufficient threshold regression through degree 80")


if __name__ == "__main__":
    main()
