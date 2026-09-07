#!/usr/bin/env python3
"""Exact checks for the polynomial-shift gcd identity and Wilson witnesses.

Usage:
  ./repo-python formal_math/erdos257_period_noncollapse/ErdosProblems/Erdos68/scripts/check_polynomial_perturbation_gcd.py --quick
"""

from __future__ import annotations

import argparse
from math import factorial, gcd


def wilson_reflect(q: int, n: int) -> int:
    return q - n - 1


def poly_collision_divides(eval_P, i: int, j: int) -> bool:
    Q = factorial(j) // factorial(i)
    a = factorial(i) + eval_P(i)
    b = factorial(j) + eval_P(j)
    g = gcd(abs(a), abs(b))
    rhs = eval_P(j) - Q * eval_P(i)
    return rhs % g == 0


def run_quick() -> None:
    assert wilson_reflect(23, 11) == 11
    assert factorial(11) % 23 == 1
    assert wilson_reflect(5, 3) == 1
    assert factorial(3) % 5 == 1
    assert wilson_reflect(5, 3) < 2

    pairs = [(3, 6), (4, 9), (5, 8), (6, 10)]
    for i, j in pairs:
        assert poly_collision_divides(lambda n: -1, i, j)
        assert poly_collision_divides(lambda n: 1, i, j)
        assert poly_collision_divides(lambda n: n, i, j)
        assert poly_collision_divides(lambda n: n * n - 3, i, j)
        assert poly_collision_divides(lambda n: 0, i, j)
    print("check_polynomial_perturbation_gcd: PASS")


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--quick", action="store_true")
    args = parser.parse_args()
    run_quick()
    if not args.quick:
        run_quick()


if __name__ == "__main__":
    main()
