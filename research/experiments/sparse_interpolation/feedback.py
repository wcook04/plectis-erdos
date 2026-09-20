#!/usr/bin/env python3
# SPDX-FileCopyrightText: 2026 Will Cook
# SPDX-License-Identifier: Apache-2.0
"""Exact finite checks of residue feedback, in scaled-tail coordinates.

These are checks of the selector and sharpness examples, not proofs of
infinite convergence, nullity, or the support classification.
"""
from fractions import Fraction
from math import factorial, gcd, isqrt
import json


def residue_step(u, cumulative, modulus):
    residue = (-cumulative) % modulus
    digit = residue + modulus * ((u - modulus - residue) // modulus)
    residual = u - digit
    assert digit >= 0
    assert modulus <= residual < 2 * modulus
    assert (cumulative + digit) % modulus == 0
    return digit, residual


def largest_factorial(limit):
    value, k = 1, 2
    while value * k <= limit:
        value *= k
        k += 1
    return value


def run_feedback(gap, exponent, stages=400):
    # Explicit finite admissibility checks, independent of asymptotic claims.
    # Working with n! times the residual avoids constructing giant factorials.
    n, modulus = 100, 1
    outputs = []
    for initial in (Fraction(1), Fraction(7, 6), Fraction(3, 2), Fraction(2)):
        n, modulus, total, residual = 100, 1, 0, initial
        maximum_modulus = 1
        for _ in range(stages):
            next_n = n + gap
            ratio = 1
            for k in range(n + 1, next_n + 1):
                ratio *= k
            cap = next_n ** exponent
            next_modulus = largest_factorial(min(isqrt(ratio) // 2,
                                                cap // (2 * ratio)))
            assert next_modulus % modulus == 0
            assert 2 * next_modulus <= modulus * ratio
            assert 2 * modulus * ratio <= cap
            digit, residual = residue_step(residual * ratio, total, next_modulus)
            assert digit <= cap and digit % modulus == 0
            total += digit
            maximum_modulus = max(maximum_modulus, next_modulus)
            n, modulus = next_n, next_modulus
        outputs.append({"initial_scaled_target": str(initial),
                        "stages": stages, "last_index": n,
                        "maximum_modulus": maximum_modulus,
                        "final_scaled_residual": str(residual)})
    return {"gap": gap, "allowance_exponent": exponent, "targets": outputs}


def rational_cantor_counterexample(stages=25):
    denominator, partial, cumulative = 1, Fraction(0), 0
    for n in range(1, stages + 1):
        correction = 2 if n == 1 else n * factorial(n)
        base = correction + 2
        denominator *= base
        partial += Fraction(correction + 1, denominator)
        cumulative += correction
        assert cumulative == factorial(n + 1)
        assert partial == 1 - Fraction(1, denominator)
        assert gcd(base, correction) <= 2
    return {"stages": stages, "identity": "partial = 1 - 1/Q_n",
            "cumulative_identity": "sum(e_k,k<=n) = (n+1)!",
            "gcd_bound": 2}


def support_density_trap(limit=4096):
    support = [n for n in range(1, limit + 1) if n & (n - 1)]
    gaps = [b-a for a,b in zip(support,support[1:])]
    assert max(gaps) == 2
    return {"description": "all positive integers except powers of two",
            "cutoff": limit, "permitted_positions": len(support),
            "gaps_of_length_two": gaps.count(2),
            "infinite_conclusion": "proved in paper, not inferred from this sample"}


if __name__ == "__main__":
    result = {"evidence": "exact finite arithmetic",
              "feedback": [run_feedback(1, 2), run_feedback(2, 3), run_feedback(3, 4)],
              "rational_counterexample": rational_cantor_counterexample(),
              "density_trap": support_density_trap()}
    print(json.dumps(result, indent=2))
