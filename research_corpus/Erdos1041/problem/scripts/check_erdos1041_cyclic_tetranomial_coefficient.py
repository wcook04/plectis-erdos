#!/usr/bin/env python3
"""Deterministic discovery audit for CyclicTetranomialCoefficientCase.

Floating-point output is evidence only.  The theorem is proved analytically
and its load-bearing identities are checked in Lean.
"""

from __future__ import annotations

import cmath
import json
import random

import numpy as np


def polynomial_roots(m: int, r: int, s: int, a: complex, b: complex, c: complex) -> np.ndarray:
    coefficients = np.zeros(m + 1, dtype=complex)
    coefficients[0] = 1
    coefficients[m - r] = a
    coefficients[m - s] = b
    coefficients[m] = c
    return np.roots(coefficients)


def phase(rng: random.Random) -> complex:
    return cmath.exp(2j * np.pi * rng.random())


def in_two_generator_semigroup(target: int, d: int, e: int) -> bool:
    """Whether target=alpha*d+beta*e for nonnegative integers alpha,beta."""
    return any((target - alpha * d) % e == 0 for alpha in range(target // d + 1))


def theorem_falsification_probe() -> dict[str, object]:
    rng = random.Random(1041)
    accepted = 0
    spoke_count = 0
    worst_value = 0.0
    worst_data: tuple[object, ...] | None = None
    parameters = np.linspace(0.0, 1.0, 401)

    for m in range(4, 11):
        for _ in range(500):
            s = rng.randrange(1, m - 1)
            r = rng.randrange(s + 1, m)
            b_modulus = 0.98 * rng.random()
            c_allowance = 0.98 - b_modulus
            b = b_modulus * phase(rng)
            c = c_allowance * rng.random() * phase(rng)
            a = 0.8 * rng.random() * phase(rng)
            roots = polynomial_roots(m, r, s, a, b, c)
            if float(np.max(np.abs(roots))) >= 1 - 1e-10:
                continue

            accepted += 1
            for root in roots:
                spoke_count += 1
                values = np.abs(
                    (parameters * root) ** m
                    + a * (parameters * root) ** r
                    + b * (parameters * root) ** s
                    + c
                )
                maximum = float(np.max(values))
                if maximum > worst_value:
                    worst_value = maximum
                    worst_data = (m, r, s, float(abs(b) + abs(c)), float(abs(root)))

    assert accepted == 1707
    assert worst_value < 1
    return {
        "seed": 1041,
        "accepted_configuration_count": accepted,
        "sampled_spoke_count": spoke_count,
        "parameter_count_per_spoke": len(parameters),
        "maximum_sampled_modulus": worst_value,
        "worst_case": worst_data,
        "violation_count": 0,
    }


def two_smallest_condition_coverage_probe() -> dict[str, object]:
    rng = random.Random(331041)
    accepted = 0
    covered = 0
    two_tail_safe = 0
    newton_semigroup_gap_count = 0
    l2_covered = 0
    l2_beyond_l1 = 0
    l2_two_tail_safe = 0

    for m in range(4, 11):
        for _ in range(2500):
            s = rng.randrange(1, m - 1)
            r = rng.randrange(s + 1, m)

            def coefficient(bound: float) -> complex:
                return bound * (rng.random() ** 1.4) * phase(rng)

            a, b, c = coefficient(1.8), coefficient(1.8), coefficient(0.99)
            roots = polynomial_roots(m, r, s, a, b, c)
            if float(np.max(np.abs(roots))) >= 1 - 1e-9:
                continue

            accepted += 1
            second_radius = sorted(abs(root) for root in roots)[1]
            if abs(c) + abs(b) * second_radius**s < 1:
                covered += 1
            tails = np.abs(c + b * roots**s)
            if int(np.sum(tails < 1 - 1e-10)) >= 2:
                two_tail_safe += 1
            if not in_two_generator_semigroup(s, m - r, m - s):
                newton_semigroup_gap_count += 1
                if m * (abs(b) ** 2 + abs(c) ** 2) < m - 1:
                    l2_covered += 1
                    if abs(b) + abs(c) > 1:
                        l2_beyond_l1 += 1
                    if int(np.sum(tails < 1 - 1e-10)) >= 2:
                        l2_two_tail_safe += 1

    assert accepted == 3204
    assert covered == 3173
    assert two_tail_safe == accepted
    assert l2_two_tail_safe == l2_covered
    return {
        "seed": 331041,
        "accepted_configuration_count": accepted,
        "proved_condition_coverage_count": covered,
        "proved_condition_coverage_fraction": covered / accepted,
        "two_tail_safe_count": two_tail_safe,
        "residual_count": accepted - covered,
        "newton_semigroup_gap_configuration_count": newton_semigroup_gap_count,
        "l2_selector_coverage_count": l2_covered,
        "l2_selector_beyond_l1_count": l2_beyond_l1,
        "l2_selector_two_tail_safe_count": l2_two_tail_safe,
    }


def unrestricted_tail_selector_probe() -> dict[str, object]:
    rng = random.Random(41041)
    accepted = 0
    minimum_safe_tail_count = 1_000_000

    for m in range(4, 11):
        for _ in range(4000):
            s = rng.randrange(1, m - 1)
            r = rng.randrange(s + 1, m)

            def coefficient(bound: float) -> complex:
                return bound * (rng.random() ** 1.5) * phase(rng)

            a, b, c = coefficient(1.8), coefficient(1.8), coefficient(0.95)
            roots = polynomial_roots(m, r, s, a, b, c)
            if float(np.max(np.abs(roots))) >= 1 - 1e-9:
                continue

            accepted += 1
            safe_count = int(np.sum(np.abs(c + b * roots**s) < 1 - 1e-10))
            minimum_safe_tail_count = min(minimum_safe_tail_count, safe_count)

    assert accepted == 6348
    assert minimum_safe_tail_count == 2
    return {
        "seed": 41041,
        "accepted_configuration_count": accepted,
        "minimum_tail_safe_root_count": minimum_safe_tail_count,
        "claim_ceiling": "conjecture evidence only; not proof authority",
    }


def main() -> None:
    receipt = {
        "schema": "erdos1041_cyclic_tetranomial_coefficient_audit_v1",
        "status": "pass",
        "theorem_falsification_probe": theorem_falsification_probe(),
        "two_smallest_condition_coverage_probe": two_smallest_condition_coverage_probe(),
        "unrestricted_tail_selector_probe": unrestricted_tail_selector_probe(),
        "proof_authority": "analytic note and Lean kernel, not this computation",
    }
    print(json.dumps(receipt, indent=2, sort_keys=True))


if __name__ == "__main__":
    main()
