#!/usr/bin/env python3
"""Replay GroupedCriticalClusterMonodromy.md.

The ordinary complex-analytic proof is authoritative.  This checker uses
exact rational upper bounds for pi in the small-degree scalar margins, then
tracks a deterministic family of near-regular grouped lollipops as a
falsifier-oriented numerical check of the stability mechanism.
"""

from __future__ import annotations

from fractions import Fraction

import numpy as np
from scipy.optimize import linear_sum_assignment


PI_UPPER = Fraction(355, 113)


def exact_scalar_checks() -> None:
    r = Fraction(99, 100)
    s = Fraction(1, 100)
    for n in (2, 3):
        # ell <= 2r + 2(pi/n-1)s, with pi < 355/113.
        upper = 2 * r + 2 * (PI_UPPER / n - 1) * s
        assert upper < 2, (n, upper)
        q = s**n
        assert q < r**n
        assert q < 1 - r**n

    # For n>=4, pi<n, hence every admissible q improves on 2r.
    assert PI_UPPER < 4
    assert 2 * r < 2


def _track_grouped_loop(
    roots: np.ndarray,
    *,
    stem_steps: int,
    circle_steps: int,
    inflate: float = 1.08,
) -> dict[str, object]:
    roots = np.asarray(roots, dtype=complex)
    n = len(roots)
    coefficients = np.poly(roots)
    critical_points = np.roots(np.polyder(coefficients))
    critical_values = np.polyval(coefficients, critical_points)

    center = np.mean(critical_values)
    radius = inflate * float(np.max(np.abs(critical_values - center))) + 1e-10
    start_angle = float(np.angle(-center)) if abs(center) else 0.0
    base = center + radius * np.exp(1j * start_angle)

    stem_parameter = np.linspace(0.0, 1.0, stem_steps + 1) ** 1.7
    stem = stem_parameter * base
    circle = center + radius * np.exp(
        1j * (start_angle + np.linspace(0.0, 2.0 * np.pi, circle_steps + 1))
    )
    values = np.concatenate((stem, circle[1:], stem[-2::-1]))

    current = roots.copy()
    lengths = np.zeros(n)
    tail = coefficients[:-1]
    for value in values[1:]:
        candidates = np.roots(
            np.concatenate((tail, [coefficients[-1] - value]))
        )
        _, assignment = linear_sum_assignment(
            np.abs(current[:, None] - candidates[None, :])
        )
        following = candidates[assignment]
        lengths += np.abs(following - current)
        current = following

    _, permutation = linear_sum_assignment(
        np.abs(current[:, None] - roots[None, :])
    )
    return {
        "mean_length": float(np.mean(lengths)),
        "max_value_modulus": float(np.max(np.abs(values))),
        "permutation": tuple(int(index) for index in permutation),
    }


def _is_full_cycle(permutation: tuple[int, ...]) -> bool:
    seen: set[int] = set()
    current = 0
    while current not in seen:
        seen.add(current)
        current = permutation[current]
    return current == 0 and len(seen) == len(permutation)


def continuation_checks() -> list[tuple[int, float, float]]:
    rng = np.random.default_rng(20260827)
    rows: list[tuple[int, float, float]] = []
    for n in range(3, 11):
        r = 0.995
        epsilon = 1e-5
        angles = (
            2.0 * np.pi * np.arange(n) / n
            + epsilon * rng.normal(size=n)
        )
        radii = r * (1.0 + 0.2 * epsilon * rng.normal(size=n))
        roots = radii * np.exp(1j * angles)

        coarse = _track_grouped_loop(
            roots, stem_steps=220, circle_steps=500
        )
        fine = _track_grouped_loop(
            roots, stem_steps=440, circle_steps=1000
        )
        permutation = fine["permutation"]
        assert isinstance(permutation, tuple)
        assert _is_full_cycle(permutation), (n, permutation)
        assert fine["max_value_modulus"] < 1.0, (n, fine)
        assert fine["mean_length"] < 1.999, (n, fine)
        assert abs(fine["mean_length"] - coarse["mean_length"]) < 2e-3, (
            n,
            coarse,
            fine,
        )
        rows.append(
            (
                n,
                float(fine["mean_length"]),
                float(fine["max_value_modulus"]),
            )
        )
    return rows


def main() -> None:
    exact_scalar_checks()
    rows = continuation_checks()
    print("GROUPED CRITICAL-CLUSTER MONODROMY: PASS")
    print("pi upper bound and n=2,3 margins: exact Fraction arithmetic")
    for n, mean_length, max_value in rows:
        print(
            f"degree {n}: mean lift {mean_length:.9f}, "
            f"max |value| {max_value:.9f}, full cycle"
        )


if __name__ == "__main__":
    main()
