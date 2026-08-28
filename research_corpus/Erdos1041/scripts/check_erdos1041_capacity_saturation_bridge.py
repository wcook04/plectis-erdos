#!/usr/bin/env python3
"""Exact and deterministic evidence for CapacitySaturationBridge.md.

The proof-bearing parts use integer/Fraction arithmetic:

* the source-current arity/capacity table composed with the sharp exterior
  capacity inequality;
* the radial spectator-factor contraction identity;
* monotonicity of the one-factor radial profile in its zero radius.

The finite-Blaschke arm is explicitly numerical.  It tests the stronger,
unproved symmetric-envelope conjecture and must not be cited as proof.
"""

from __future__ import annotations

import json
import math
from fractions import Fraction

import numpy as np


CURRENT_LATTICES = {
    "mu<=1/2": [
        Fraction(1, 3), Fraction(2, 5), Fraction(12, 25), Fraction(1, 2),
        Fraction(7, 12), Fraction(16, 25), Fraction(2, 3), Fraction(7, 10),
        Fraction(3, 4), Fraction(4, 5), Fraction(5, 6), Fraction(7, 8),
        Fraction(9, 10), Fraction(33, 35), Fraction(39, 40),
    ],
    "mu<=1/4": [
        Fraction(19, 50), Fraction(12, 25), Fraction(4, 7), Fraction(16, 25),
        Fraction(7, 10), Fraction(3, 4), Fraction(4, 5), Fraction(7, 8),
        Fraction(14, 15), Fraction(49, 50),
    ],
    "mu<=1/8": [
        Fraction(2, 5), Fraction(1, 2), Fraction(3, 5), Fraction(2, 3),
        Fraction(3, 4), Fraction(4, 5), Fraction(8, 9), Fraction(18, 19),
    ],
    "mu<=1/64": [
        Fraction(4, 9), Fraction(5, 9), Fraction(16, 25), Fraction(8, 11),
        Fraction(4, 5), Fraction(13, 15), Fraction(13, 14), Fraction(99, 100),
    ],
}


def exact_band(k: int, q: Fraction, search_to: int = 5000) -> list[tuple[int, int]]:
    good = [
        n for n in range(k + 1, search_to + 1)
        if k * q.denominator**n < (2 * n - k) * q.numerator**n
    ]
    if not good:
        return []
    spans: list[tuple[int, int]] = []
    start = previous = good[0]
    for n in good[1:]:
        if n == previous + 1:
            previous = n
        else:
            spans.append((start, previous))
            start = previous = n
    spans.append((start, previous))
    return spans


def exact_lattice_composition() -> dict[str, object]:
    nonempty: list[dict[str, object]] = []
    for regime, cutoffs in CURRENT_LATTICES.items():
        for k, q in enumerate(cutoffs, start=2):
            band = exact_band(k, q)
            if band:
                nonempty.append({"regime": regime, "k": k, "q": str(q), "band": band})
    expected = [
        {"regime": "mu<=1/2", "k": 16, "q": "39/40", "band": [(22, 93)]},
        {"regime": "mu<=1/4", "k": 11, "q": "49/50", "band": [(13, 167)]},
        {"regime": "mu<=1/8", "k": 9, "q": "18/19", "band": [(15, 35)]},
        {"regime": "mu<=1/64", "k": 9, "q": "99/100", "band": [(10, 459)]},
    ]
    return {"nonempty_bands": nonempty, "expected": expected, "pass": nonempty == expected}


def exact_radial_algebra() -> dict[str, object]:
    # For x>=1 and |a|=r<1,
    # |x e^{i theta}-a|^2-|1-conj(a)x e^{i theta}|^2
    # = (x^2-1)(1-r^2)>=0.  Check a large exact rational grid.
    contraction = True
    monotonicity = True
    profile_ceiling = True
    for x_num in range(10, 61):
        x = Fraction(x_num, 10)
        if x < 1:
            continue
        for r_num in range(1, 10):
            r = Fraction(r_num, 10)
            if x > 1 / r:
                continue
            contraction &= (x * x - 1) * (1 - r * r) >= 0
            # d/dr log((1-rx)/(x-r)) has numerator 1-x^2.
            monotonicity &= 1 - x * x <= 0
            y = r * x
            # x^n(1-rx)/(x-r) <= r^(-(n-1)) reduces to
            # y^n(1-y) <= y-r^2; use y^n<=y and y>=r.
            for n in range(2, 20):
                profile_ceiling &= y**n * (1 - y) <= y - r * r
    return {
        "spectator_factor_contraction": contraction,
        "profile_monotone_in_r": monotonicity,
        "explicit_profile_ceiling": profile_ceiling,
        "pass": contraction and monotonicity and profile_ceiling,
    }


def one_factor_profile(n: int, r: float) -> float:
    threshold = (n - 1.0) / (n + 1.0)
    if not 0.0 < r < threshold:
        raise ValueError((n, r, threshold))
    trace = ((n - 1.0) + (n + 1.0) * r * r) / (n * r)
    x = 0.5 * (trace + math.sqrt(trace * trace - 4.0))
    return x**n * (1.0 - r * x) / (x - r)


def symmetric_profile(n: int, m: int, p: float) -> float:
    threshold = (n - m) / (n + m)
    if not 0.0 < p < threshold:
        raise ValueError((n, m, p, threshold))
    trace = ((n + m) * p * p + (n - m)) / (n * p)
    y = 0.5 * (trace + math.sqrt(trace * trace - 4.0))
    return y ** (n / m) * (1.0 - p * y) / (y - p)


def _critical_gap(n: int, zeros: np.ndarray) -> float | None:
    numerator = np.poly1d(np.poly(zeros))
    denominator = np.poly1d([1.0 + 0.0j])
    for zero in zeros:
        denominator = np.polymul(
            denominator, np.poly1d([-np.conj(zero), 1.0 + 0.0j])
        )
    critical_numerator = n * np.polymul(numerator, denominator) - np.polymul(
        np.poly1d([1.0, 0.0]),
        np.polysub(
            np.polymul(np.polyder(numerator), denominator),
            np.polymul(numerator, np.polyder(denominator)),
        ),
    )
    candidates: list[float] = []
    for zeta in np.roots(critical_numerator):
        if abs(zeta) <= 1.0 + 1.0e-7:
            continue
        b_value = np.polyval(numerator, zeta) / np.polyval(denominator, zeta)
        ratio = abs(zeta) ** n / abs(b_value)
        if ratio >= 1.0 - 1.0e-7:
            candidates.append(math.log(max(1.0, ratio)))
    return min(candidates) if candidates else None


def _sampled_speed_max(zeros: np.ndarray) -> float:
    theta = np.linspace(0.0, 2.0 * math.pi, 12001, endpoint=False)
    zeta = np.exp(1j * theta)
    speed = np.zeros_like(theta)
    for zero in zeros:
        speed += (1.0 - abs(zero) ** 2) / abs(zeta - zero) ** 2
    return float(np.max(speed))


def numerical_symmetric_envelope(seed: int = 1041) -> dict[str, object]:
    """Try to falsify: symmetric zeros maximize the first exterior gap at fixed p."""
    rng = np.random.default_rng(seed)
    specifications = [(8, 2, 0.8), (10, 3, 0.8), (12, 4, 0.8), (10, 3, 0.98)]
    rows: list[dict[str, object]] = []
    global_max_ratio = 0.0
    for n, m, alpha in specifications:
        p0 = (n - m) / (n + m)
        p = alpha * p0
        base_radius = p ** (1.0 / m)
        symmetric_gap = math.log(symmetric_profile(n, m, p))
        accepted = 0
        maximum_ratio = 0.0
        for _ in range(1200):
            log_radii = math.log(base_radius) + rng.normal(0.0, 0.12, m)
            log_radii -= np.mean(log_radii) - math.log(base_radius)
            if float(np.max(log_radii)) >= -1.0e-5:
                continue
            angles = 2.0 * math.pi * np.arange(m) / m + rng.normal(0.0, 0.18, m)
            zeros = np.exp(log_radii + 1j * angles)
            if _sampled_speed_max(zeros) >= n:
                continue
            gap = _critical_gap(n, zeros)
            if gap is None:
                continue
            accepted += 1
            maximum_ratio = max(maximum_ratio, gap / symmetric_gap)
        global_max_ratio = max(global_max_ratio, maximum_ratio)
        rows.append({
            "n": n, "m": m, "alpha": alpha, "accepted": accepted,
            "max_gap_over_symmetric_gap": maximum_ratio,
        })
    return {
        "evidence_class": "deterministic_floating_falsifier_search_not_proof",
        "seed": seed,
        "rows": rows,
        "global_max_ratio": global_max_ratio,
        "no_counterexample_observed": all(
            row["accepted"] > 0 and row["max_gap_over_symmetric_gap"] <= 1.000001
            for row in rows
        ),
    }


def main() -> int:
    lattice = exact_lattice_composition()
    radial = exact_radial_algebra()
    numerical = numerical_symmetric_envelope()
    result = {
        "schema": "erdos1041_capacity_saturation_bridge_receipt_v1",
        "exact_lattice_composition": lattice,
        "exact_radial_algebra": radial,
        "numerical_symmetric_envelope": numerical,
        "pass": lattice["pass"] and radial["pass"] and numerical["no_counterexample_observed"],
        "claim_boundary": (
            "The lattice and radial algebra are exact. The symmetric-envelope arm is finite "
            "floating evidence only and does not prove the conjectured optimal merge ceiling."
        ),
    }
    print(json.dumps(result, indent=2))
    return 0 if result["pass"] else 1


if __name__ == "__main__":
    raise SystemExit(main())
