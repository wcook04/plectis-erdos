#!/usr/bin/env python3
"""Deterministic discovery audit for the tetranomial L2 selector.

The numerical root checks replay the coefficient-extraction formula that led
to the theorem.  Proof authority is the analytic derivation and Lean kernel,
not floating-point agreement.
"""

from __future__ import annotations

import cmath
from fractions import Fraction
from math import comb
import json
import random

import numpy as np


def newton_moment(m: int, r: int, s: int, a: complex, b: complex) -> complex:
    """Coefficient of t^s in -s*log(1+a*t^(m-r)+b*t^(m-s))."""
    d, e = m - r, m - s
    answer = 0j
    for alpha in range(s // d + 1):
        for beta in range(s // e + 1):
            if alpha * d + beta * e != s:
                continue
            total = alpha + beta
            assert total > 0
            answer += (
                s
                * ((-1) ** total)
                * comb(total, alpha)
                / total
                * a**alpha
                * b**beta
            )
    return answer


def roots_of_tetranomial(
    m: int, r: int, s: int, a: complex, b: complex, c: complex
) -> np.ndarray:
    coefficients = np.zeros(m + 1, dtype=complex)
    coefficients[0] = 1
    coefficients[m - r] = a
    coefficients[m - s] = b
    coefficients[m] = c
    return np.roots(coefficients)


def phase(rng: random.Random) -> complex:
    return cmath.exp(2j * np.pi * rng.random())


def coefficient_formula_audit() -> dict[str, object]:
    rng = random.Random(10412026)
    comparison_count = 0
    maximum_error = 0.0
    worst: tuple[object, ...] | None = None

    for m in range(4, 13):
        for r in range(2, m):
            for s in range(1, r):
                a = 0.45 * rng.random() * phase(rng)
                b = 0.45 * rng.random() * phase(rng)
                c = 0.30 * rng.random() * phase(rng)
                roots = roots_of_tetranomial(m, r, s, a, b, c)
                measured = complex(np.sum(roots**s))
                predicted = newton_moment(m, r, s, a, b)
                error = abs(measured - predicted)
                comparison_count += 1
                if error > maximum_error:
                    maximum_error = error
                    worst = (m, r, s, measured, predicted)

    assert comparison_count == 219
    assert maximum_error < 1e-8
    return {
        "seed": 10412026,
        "comparison_count": comparison_count,
        "maximum_absolute_error": maximum_error,
        "worst_case": worst,
    }


def exponent_scope_audit() -> dict[str, object]:
    total = 0
    simple_gap = 0
    semigroup_gap = 0

    for m in range(4, 81):
        for r in range(2, m):
            for s in range(1, r):
                total += 1
                d, e = m - r, m - s
                simple_gap += int(s < d)
                represented = any(
                    alpha * d + beta * e == s
                    for alpha in range(s // d + 1)
                    for beta in range(s // e + 1)
                )
                semigroup_gap += int(not represented)

    assert (total, simple_gap, semigroup_gap) == (82159, 40300, 68299)
    return {
        "maximum_degree": 80,
        "exponent_triple_count": total,
        "simple_gap_count": simple_gap,
        "semigroup_gap_count": semigroup_gap,
        "additional_semigroup_gap_count": semigroup_gap - simple_gap,
    }


def exact_resonant_quintic_certificate() -> dict[str, object]:
    U = Fraction(1, 2)
    q = Fraction(4, 5)
    a, b, c = -U, q, -U * q
    l1 = abs(b) + abs(c)
    zero_moment_l2 = 5 * (b * b + c * c)
    signed_l2 = zero_moment_l2 - 4 * (c * b * a)

    assert l1 == Fraction(6, 5)
    assert zero_moment_l2 == 4
    assert signed_l2 == Fraction(84, 25)
    assert signed_l2 < 4
    return {
        "polynomial": "w^5-(1/2)w^3+(4/5)w^2-2/5",
        "factorization": "(w^2-1/2)(w^3+4/5)",
        "l1_budget": str(l1),
        "zero_moment_l2_budget": str(zero_moment_l2),
        "signed_l2_budget": str(signed_l2),
        "target": "4",
    }


def main() -> None:
    print(
        json.dumps(
            {
                "schema": "erdos1041_tetranomial_l2_selector_audit_v1",
                "status": "pass",
                "coefficient_formula_audit": coefficient_formula_audit(),
                "exponent_scope_audit": exponent_scope_audit(),
                "exact_resonant_quintic_certificate": exact_resonant_quintic_certificate(),
                "proof_authority": "analytic note and Lean kernel, not this computation",
            },
            indent=2,
            sort_keys=True,
            default=str,
        )
    )


if __name__ == "__main__":
    main()
