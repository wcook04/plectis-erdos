#!/usr/bin/env python3
"""Deterministic regression checks for return 004's exact scalar interfaces.

This checker is falsifier evidence for the ordinary proofs in
LowCriticalTwoRootReduction20260826.md.  It does not certify the parent theorem.
"""

from __future__ import annotations

import cmath
import math
import random


def polyval_from_roots(z: complex, roots: list[complex]) -> complex:
    out = 1.0 + 0.0j
    for root in roots:
        out *= z - root
    return out


def radial_product(t: float, roots: list[complex]) -> float:
    out = 1.0
    for root in roots:
        out *= abs(polyval_from_roots(t * root, roots))
    return out


def boundary_fourier_product(t: float, roots: list[complex], cutoff: int) -> float:
    exponent = 0.0
    for m in range(1, cutoff + 1):
        power_sum = sum(root**m for root in roots)
        exponent -= (t**m / m) * abs(power_sum) ** 2
    return math.exp(exponent)


def segment_envelope(n: int, t: float) -> float:
    return (1.0 - t) * (1.0 + t * t + 2.0 * t / (n - 1)) ** ((n - 1) / 2)


def segment_constant(n: int) -> float:
    return 2.0 / (n - 1) * (2.0 * (n - 2) / (n - 1)) ** ((n - 1) / 2)


def second_nearest_crude_envelope(n: int, t: float) -> float:
    return (1.0 - t) * (1.0 + (n - 1) * t) * (1.0 + t) ** (n - 2)


def main() -> None:
    rng = random.Random(20260826)

    worst_product = 0.0
    for n in range(2, 13):
        for _ in range(200):
            roots = [
                math.sqrt(rng.random()) * cmath.exp(2j * math.pi * rng.random())
                for _ in range(n)
            ]
            for t in (0.0, 0.01, 0.1, 0.33, 0.7, 0.95, 1.0):
                value = radial_product(t, roots)
                worst_product = max(worst_product, value)
                assert value <= 1.0 + 2e-11, (n, t, value)

    worst_fourier_error = 0.0
    for n in range(2, 10):
        roots = [cmath.exp(2j * math.pi * rng.random()) for _ in range(n)]
        for t in (0.1, 0.4, 0.75):
            direct = radial_product(t, roots)
            fourier = boundary_fourier_product(t, roots, cutoff=1200)
            error = abs(direct - fourier)
            worst_fourier_error = max(worst_fourier_error, error)
            assert error <= 2e-11, (n, t, direct, fourier, error)

    worst_envelope_relative_excess = 0.0
    worst_two_spoke_budget_ratio = 0.0
    for n in range(3, 101):
        constant = segment_constant(n)
        sampled = max(segment_envelope(n, k / 20000) for k in range(20001))
        relative_excess = (sampled - constant) / max(1.0, constant)
        worst_envelope_relative_excess = max(
            worst_envelope_relative_excess, relative_excess
        )
        assert relative_excess <= 2e-12, (n, sampled, constant)
        common_budget = n * 2.0 ** (n - 2)
        second_sampled = max(
            second_nearest_crude_envelope(n, k / 20000) for k in range(20001)
        )
        budget_ratio = second_sampled / common_budget
        worst_two_spoke_budget_ratio = max(worst_two_spoke_budget_ratio, budget_ratio)
        assert budget_ratio <= 1.0 + 2e-12, (n, second_sampled, common_budget)

    print(
        {
            "status": "pass",
            "claim_boundary": "regression evidence only; ordinary proof is authority",
            "worst_radial_product": worst_product,
            "worst_boundary_fourier_error": worst_fourier_error,
            "worst_segment_envelope_relative_excess": worst_envelope_relative_excess,
            "worst_two_spoke_budget_ratio": worst_two_spoke_budget_ratio,
        }
    )


if __name__ == "__main__":
    main()
