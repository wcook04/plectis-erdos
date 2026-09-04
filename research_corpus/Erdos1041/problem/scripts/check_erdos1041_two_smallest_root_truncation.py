#!/usr/bin/env python3
"""Verification for the two-smallest-root truncated path theorem."""

from __future__ import annotations

import itertools
import math

import numpy as np


def threshold(n: int) -> float:
    lo, hi = 0.0, 1.0
    for _ in range(100):
        q = (lo + hi) / 2
        if q * q * (1 + q) ** (n - 2) <= 1:
            lo = q
        else:
            hi = q
    return lo


def polynomial_value(roots: np.ndarray, z: complex) -> float:
    return float(abs(np.prod(z - roots)))


def path_audit(roots: np.ndarray, samples: int = 401) -> tuple[float, float, float]:
    order = np.argsort(np.abs(roots))
    a, b = roots[order[0]], roots[order[1]]
    r, q = abs(a), abs(b)
    if r < 1e-15:
        points = np.linspace(0, 1, samples) * b
    else:
        u, v = a / r, b / q
        chord = np.array([r * ((1 - t) * u + t * v)
                          for t in np.linspace(0, 1, samples)])
        arm = np.array([x * v for x in np.linspace(r, q, samples)])
        points = np.concatenate((chord, arm[1:]))
    value = max(polynomial_value(roots, z) for z in points)
    tail_moduli = np.abs(roots[order[2:]])
    exact_budget = ((r + q) ** 2 / 4) * float(np.prod(q + tail_moduli))
    uniform_budget = ((r + q) ** 2 / 4) * (1 + q) ** (len(roots) - 2)
    return value, exact_budget, uniform_budget


def main() -> int:
    # The algebraic defects are identities and nonnegative on their domains.
    for r in np.linspace(0, 1, 31):
        for q in np.linspace(r, 1, 31):
            for x in np.linspace(0, r, 31):
                chord_defect = (q + r) ** 2 - 8 * x * (q + r - 2 * x)
                expected = (q + r - 4 * x) ** 2
                assert abs(chord_defect - expected) < 2e-14
                assert chord_defect >= -2e-14
            for x in np.linspace(r, q, 31):
                arm_defect = (q + r) ** 2 - 4 * (q - x) * (x + r)
                expected = (q - r - 2 * x) ** 2
                assert abs(arm_defect - expected) < 2e-14
                assert arm_defect >= -2e-14

    expected = {
        2: 1.0,
        3: 0.754877666247,
        4: 0.618033988750,
        5: 0.528946354520,
        6: 0.465571231877,
        8: 0.380277569098,
        10: 0.324717957245,
        12: 0.285199033245,
    }
    for n, want in expected.items():
        got = threshold(n)
        assert abs(got - want) < 1e-12, (n, got, want)

    rng = np.random.default_rng(1041_20260825)
    worst_ratio = 0.0
    checked = 0
    for n in range(2, 13):
        cap = threshold(n) * 0.995
        for _ in range(400):
            radii = np.sort(rng.uniform(0.02, 0.999999, n))
            radii[1] = min(radii[1], cap)
            radii[0] = min(radii[0], radii[1])
            # Preserve ordering after forcing the second radius below the cap.
            radii[2:] = np.maximum(radii[2:], radii[1])
            roots = radii * np.exp(2j * np.pi * rng.random(n))
            value, exact_budget, budget = path_audit(roots)
            assert exact_budget <= budget + 2e-14
            assert budget < 1
            assert value < 1 + 2e-12, (n, value, budget, roots)
            worst_ratio = max(worst_ratio, value / exact_budget if exact_budget else 0.0)
            checked += 1

    print("two-smallest-root truncation verification PASS")
    print(f"configurations={checked} worst_sampled_value_over_budget={worst_ratio:.12f}")
    print("thresholds=" + ", ".join(
        f"n={n}:{threshold(n):.12f}" for n in expected))
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
