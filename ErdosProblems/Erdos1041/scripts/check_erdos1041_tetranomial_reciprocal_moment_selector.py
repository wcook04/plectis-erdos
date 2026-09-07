#!/usr/bin/env python3
"""Deterministic audit for the reciprocal-moment radius selector."""

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
    factor = (-a) ** reduced_s * b**reduced_d - (-c) ** reduced_d
    return abs(c) ** (2 * r) * abs(factor) ** (2 * q)


def coverage_audit() -> dict[str, object]:
    rng = random.Random(331041)
    accepted = 0
    reciprocal_selector = 0
    tail_product_selector = 0
    close_pair_selector = 0
    two_selector_union = 0
    three_selector_union = 0
    three_selector_safe = 0
    maximum_reciprocal_moment_error = 0.0
    maximum_second_radius_bound_violation = 0.0
    survivor_rows: list[dict[str, object]] = []

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
            upper_energy = (
                m * abs(c) ** 2
                + (m - 1 + abs(c) ** (2 * s)) * abs(b) ** 2
                + 2 * (np.conj(c) * b * moment).real
            )
            tail_product = tail_product_formula(m, r, s, a, b, c)
            tail_holds = tail_product <= 1 + 1e-12 and upper_energy < m - 1 + tail_product

            reciprocal_holds = False
            radius_cap = None
            if s >= 2 and abs(c) > 0:
                k = s - 1
                reciprocal_error = abs(np.sum(roots ** (-k)))
                maximum_reciprocal_moment_error = max(
                    maximum_reciprocal_moment_error, float(reciprocal_error)
                )
                radius_cap = ((m - 1) * abs(c) ** k) ** (1 / (m * k))
                radii = np.sort(np.abs(roots))
                radius_bound_violation = max(
                    0.0,
                    float(radii[1] ** (m * k) - (m - 1) * abs(c) ** k),
                )
                maximum_second_radius_bound_violation = max(
                    maximum_second_radius_bound_violation,
                    radius_bound_violation,
                )
                reciprocal_holds = (
                    radius_cap < 1
                    and radius_cap**r
                    * (radius_cap ** (m - r) + abs(a))
                    < 1
                )

            tails = np.abs(c + b * roots**s)
            safe_count = int(np.sum(tails < 1 - 1e-9))
            minimum_pair_square = float(min(
                abs(roots[i] - roots[j]) ** 2
                for i in range(m)
                for j in range(i)
            ))
            close_pair_holds = bool(2 ** (m - 2) * minimum_pair_square < 4)
            two_selector_holds = tail_holds or reciprocal_holds
            three_selector_holds = two_selector_holds or close_pair_holds
            reciprocal_selector += int(reciprocal_holds)
            tail_product_selector += int(tail_holds)
            close_pair_selector += int(close_pair_holds)
            two_selector_union += int(two_selector_holds)
            three_selector_union += int(three_selector_holds)
            three_selector_safe += int(three_selector_holds and safe_count >= 2)
            if not two_selector_holds:
                survivor_rows.append(
                    {
                        "m": m,
                        "r": r,
                        "s": s,
                        "abs_a": abs(a),
                        "abs_b": abs(b),
                        "abs_c": abs(c),
                        "radius_cap": radius_cap,
                        "safe_tail_count": safe_count,
                        "minimum_pair_square": minimum_pair_square,
                        "close_pair_factor_budget": 2 ** (m - 2) * minimum_pair_square,
                        "close_pair_holds": close_pair_holds,
                    }
                )

    assert accepted == 3204
    assert reciprocal_selector == 1683
    assert tail_product_selector == 3201
    assert two_selector_union == 3203
    assert three_selector_union == accepted
    assert three_selector_safe == accepted
    assert maximum_reciprocal_moment_error < 1e-7
    assert maximum_second_radius_bound_violation < 1e-10
    assert len(survivor_rows) == 1
    assert (survivor_rows[0]["m"], survivor_rows[0]["r"], survivor_rows[0]["s"]) == (7, 5, 2)
    assert survivor_rows[0]["safe_tail_count"] == 4
    assert survivor_rows[0]["close_pair_holds"]
    return {
        "seed": 331041,
        "accepted_configuration_count": accepted,
        "reciprocal_selector_count": reciprocal_selector,
        "tail_product_selector_count": tail_product_selector,
        "close_pair_selector_count": close_pair_selector,
        "two_selector_union_count": two_selector_union,
        "three_selector_union_count": three_selector_union,
        "three_selector_two_tail_safe_count": three_selector_safe,
        "maximum_reciprocal_moment_absolute_error": maximum_reciprocal_moment_error,
        "maximum_second_radius_bound_violation": maximum_second_radius_bound_violation,
        "survivors": survivor_rows,
    }


def main() -> None:
    print(
        json.dumps(
            {
                "schema": "erdos1041_tetranomial_reciprocal_moment_audit_v1",
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
