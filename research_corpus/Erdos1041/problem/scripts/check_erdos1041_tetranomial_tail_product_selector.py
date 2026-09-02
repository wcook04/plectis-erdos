#!/usr/bin/env python3
"""Deterministic coverage audit for the tail-resultant bonus selector.

Floating-point roots measure theorem coverage and apply falsification pressure.
The analytic note and Lean kernel, not this computation, are proof authority.
"""

from __future__ import annotations

import cmath
from math import comb, gcd
import json
import random

import numpy as np


def phase(rng: random.Random) -> complex:
    return cmath.exp(2j * np.pi * rng.random())


def roots_of_tetranomial(
    m: int, r: int, s: int, a: complex, b: complex, c: complex
) -> np.ndarray:
    coefficients = np.zeros(m + 1, dtype=complex)
    coefficients[0] = 1
    coefficients[m - r] = a
    coefficients[m - s] = b
    coefficients[m] = c
    return np.roots(coefficients)


def newton_moment(m: int, r: int, s: int, a: complex, b: complex) -> complex:
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


def tail_product_formula(
    m: int, r: int, s: int, a: complex, b: complex, c: complex
) -> float:
    q = gcd(s, m - r)
    reduced_s = s // q
    reduced_d = (m - r) // q
    binomial_resultant = (-a) ** reduced_s * b**reduced_d - (-c) ** reduced_d
    return abs(c) ** (2 * r) * abs(binomial_resultant) ** (2 * q)


def coverage_audit() -> dict[str, object]:
    rng = random.Random(331041)
    accepted = 0
    old_selector = 0
    tail_product_selector = 0
    gained = 0
    certified_safe = 0
    residual_safe_counts: list[int] = []
    maximum_resultant_formula_error = 0.0

    for m in range(4, 11):
        for _ in range(2500):
            s = rng.randrange(1, m - 1)
            r = rng.randrange(s + 1, m)

            def coefficient(bound: float) -> complex:
                return bound * (rng.random() ** 1.4) * phase(rng)

            a, b, c = coefficient(1.8), coefficient(1.8), coefficient(0.99)
            roots = roots_of_tetranomial(m, r, s, a, b, c)
            if float(np.max(np.abs(roots))) >= 1 - 1e-9:
                continue

            accepted += 1
            moment = newton_moment(m, r, s, a, b)
            cross = 2 * (np.conj(c) * b * moment).real
            upper_energy = (
                m * abs(c) ** 2
                + (m - 1 + abs(c) ** (2 * s)) * abs(b) ** 2
                + cross
            )
            tails_sq = np.abs(c + b * roots**s) ** 2
            root_tail_product = float(np.prod(tails_sq))
            tail_product = tail_product_formula(m, r, s, a, b, c)
            resultant_error = abs(root_tail_product - tail_product) / max(
                1.0, root_tail_product, tail_product
            )
            maximum_resultant_formula_error = max(
                maximum_resultant_formula_error, resultant_error
            )
            old_holds = upper_energy < m - 1
            new_holds = tail_product <= 1 + 1e-12 and upper_energy < m - 1 + tail_product
            safe_count = int(np.sum(tails_sq < 1 - 1e-9))

            old_selector += int(old_holds)
            tail_product_selector += int(new_holds)
            gained += int(new_holds and not old_holds)
            certified_safe += int(new_holds and safe_count >= 2)
            if not new_holds:
                residual_safe_counts.append(safe_count)

    assert accepted == 3204
    assert old_selector == 3187
    assert tail_product_selector == 3201
    assert gained == 14
    assert certified_safe == tail_product_selector
    assert sorted(residual_safe_counts) == [4, 4, 6]
    assert maximum_resultant_formula_error < 1e-10
    return {
        "seed": 331041,
        "accepted_configuration_count": accepted,
        "old_product_sensitive_selector_count": old_selector,
        "tail_product_selector_count": tail_product_selector,
        "strict_gain_count": gained,
        "certified_two_tail_safe_count": certified_safe,
        "remaining_residual_count": len(residual_safe_counts),
        "remaining_residual_safe_counts": sorted(residual_safe_counts),
        "maximum_resultant_formula_relative_error": maximum_resultant_formula_error,
    }


def main() -> None:
    print(
        json.dumps(
            {
                "schema": "erdos1041_tetranomial_tail_product_audit_v1",
                "status": "pass",
                "coverage_audit": coverage_audit(),
                "proof_authority": "analytic note and Lean kernel, not this computation",
            },
            indent=2,
            sort_keys=True,
        )
    )


if __name__ == "__main__":
    main()
