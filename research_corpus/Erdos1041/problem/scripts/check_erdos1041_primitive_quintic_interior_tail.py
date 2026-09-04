#!/usr/bin/env python3
"""Deterministic audit for the primitive-quintic closed-disk tail theorem.

The analytic proof and Lean kernel are authority.  This script checks the
algebraic identities exactly with SymPy and stress-tests the theorem on a
fixed family of Schur-stable quartic cores.
"""

from __future__ import annotations

import json

import numpy as np
import sympy as sp


def exact_audit() -> dict[str, str]:
    r, x, s, d, u = sp.symbols("r x s d u", real=True)
    q = (-r / 2 - x) * (1 - x) ** 2
    harmonic = (
        1
        - 3 * r / 4
        + (r - sp.Rational(7, 4)) * x
        + (1 - r / 4) * (2 * x**2 - s)
        - sp.Rational(1, 4) * (4 * x**3 - 3 * s * x)
    )
    coordinate = q + (1 - s) * (1 - r / 4 - 3 * x / 4)
    assert sp.expand(harmonic - coordinate) == 0

    a = 1 - r / 4 - 3 * x / 4
    p = -u**2 + 2 * r * a / 5
    substitutions = {r: 2 * (d + u - 1), x: 1 - u}
    completed = (
        sp.Rational(2, 5)
        * (d - sp.Rational(38, 31) + (u - sp.Rational(3, 31)) / 4) ** 2
        + sp.Rational(31, 40) * (u - sp.Rational(3, 31)) ** 2
    )
    assert sp.expand((sp.Rational(1, 31) - p).subs(substitutions) - completed) == 0

    return {
        "harmonic_coordinate_identity": "exact",
        "one_over_31_completion": "exact",
        "zero_a_case": "tail energy is s^5 <= 1 for 0 <= s <= 1",
    }


def schur_probe() -> dict[str, int | float]:
    rng = np.random.default_rng(1041)
    accepted = 0
    roots_checked = 0
    minimum_safe_count = 5
    maximum_unsafe_score = -np.inf
    moment_error = 0.0

    for _ in range(12_000):
        alpha = (rng.random() - 0.5 + 1j * (rng.random() - 0.5)) * 0.72
        delta = (rng.random() - 0.5 + 1j * (rng.random() - 0.5)) * 0.72
        q_roots = np.roots([1.0, alpha, 0.0, 0.0, delta])
        if np.max(np.abs(q_roots)) >= 0.985:
            continue

        rho = 0.995 * np.sqrt(rng.random())
        c = rho * np.exp(2j * np.pi * rng.random())
        a = alpha + c * np.conjugate(delta)
        b = delta + c * np.conjugate(alpha)
        roots = np.roots([1.0, a, 0.0, 0.0, b, c])
        if np.max(np.abs(roots)) >= 1.0 + 2e-8:
            raise AssertionError("Schur parametrization escaped the unit disk")

        tails = np.abs(b * roots + c)
        safe_count = int(np.count_nonzero(tails < 1.0 - 2e-8))
        if safe_count < 2:
            raise AssertionError((a, b, c, roots, tails))

        if abs(a) > 1e-10:
            phase = a / abs(a)
            z = roots / phase
            r = abs(a)
            x = z.real
            s = np.abs(z) ** 2
            h = (
                1
                - 3 * r / 4
                + (r - 7 / 4) * x
                + (1 - r / 4) * (2 * x**2 - s)
                - (4 * x**3 - 3 * s * x) / 4
            )
            energy = s**4 * (s + r**2 + 2 * r * x)
            unsafe = energy >= 1.0 - 2e-8
            if np.any(unsafe):
                maximum_unsafe_score = max(maximum_unsafe_score, float(np.max(h[unsafe])))
                if np.max(h[unsafe]) > 2 / 31 + 2e-7:
                    raise AssertionError("unsafe-score cap failed")
            moment_error = max(moment_error, abs(float(np.sum(h)) - (5 - 2 * r)))

        accepted += 1
        roots_checked += 5
        minimum_safe_count = min(minimum_safe_count, safe_count)
        if accepted == 1_200:
            break

    if accepted != 1_200:
        raise AssertionError(f"only {accepted} Schur-stable samples accepted")

    return {
        "accepted_configurations": accepted,
        "roots_checked": roots_checked,
        "minimum_safe_tail_count": minimum_safe_count,
        "maximum_observed_unsafe_separator_score": float(maximum_unsafe_score),
        "maximum_separator_sum_error": moment_error,
    }


def main() -> None:
    payload = {
        "status": "PASS",
        "exact": exact_audit(),
        "probe": schur_probe(),
        "authority": "analytic proof plus Lean kernel; numerical probe is falsifier evidence only",
    }
    print(json.dumps(payload, indent=2, sort_keys=True))


if __name__ == "__main__":
    main()
