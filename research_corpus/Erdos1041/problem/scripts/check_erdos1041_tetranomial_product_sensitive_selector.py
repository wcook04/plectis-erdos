#!/usr/bin/env python3
"""Deterministic coverage audit for the product-sensitive L2 selector.

Floating-point root calculations measure theorem coverage and apply
falsification pressure.  The product-sum inequality, Newton formula, and Lean
kernel are proof authority.
"""

from __future__ import annotations

import cmath
from math import comb
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


def coverage_audit() -> dict[str, object]:
    rng = random.Random(331041)
    accepted = 0
    crude_signed = 0
    product_sensitive = 0
    product_beyond_crude = 0
    product_beyond_l1 = 0
    product_safe = 0
    minimum_slack = float("inf")

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
            crude_energy = m * (abs(b) ** 2 + abs(c) ** 2) + cross
            product_energy = (
                m * abs(c) ** 2
                + (m - 1 + abs(c) ** (2 * s)) * abs(b) ** 2
                + cross
            )
            crude_holds = crude_energy < m - 1
            product_holds = product_energy < m - 1
            crude_signed += int(crude_holds)
            product_sensitive += int(product_holds)
            product_beyond_crude += int(product_holds and not crude_holds)
            product_beyond_l1 += int(product_holds and abs(b) + abs(c) > 1)

            if product_holds:
                tails = np.abs(c + b * roots**s)
                safe_count = int(np.sum(tails < 1 - 1e-9))
                product_safe += int(safe_count >= 2)
                exact_energy = float(np.sum(tails**2))
                minimum_slack = min(minimum_slack, (m - 1) - exact_energy)

    assert accepted == 3204
    assert crude_signed == 3161
    assert product_sensitive == 3187
    assert product_beyond_crude == 26
    assert product_beyond_l1 == 113
    assert product_safe == product_sensitive
    return {
        "seed": 331041,
        "accepted_configuration_count": accepted,
        "crude_signed_selector_count": crude_signed,
        "product_sensitive_selector_count": product_sensitive,
        "product_sensitive_beyond_crude_count": product_beyond_crude,
        "product_sensitive_beyond_l1_count": product_beyond_l1,
        "product_sensitive_two_tail_safe_count": product_safe,
        "minimum_exact_energy_slack": minimum_slack,
    }


def main() -> None:
    print(
        json.dumps(
            {
                "schema": "erdos1041_tetranomial_product_sensitive_audit_v1",
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
