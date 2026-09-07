#!/usr/bin/env python3
"""Exact algebra and deterministic stress replay for the quintic radial cone."""

from __future__ import annotations

import json

import numpy as np
import sympy as sp


SAMPLES = 400_000


def main() -> None:
    s, t = sp.symbols("s t", nonnegative=True, real=True)
    factor_identity = sp.expand(
        t**5 - 5 * s**4 * t + 4 * s**5
        - (t - s) ** 2 * (t**3 + 2 * s * t**2 + 3 * s**2 * t + 4 * s**3)
    ) == 0

    rng = np.random.default_rng(1041_5)
    delta = 10 ** rng.uniform(-12, np.log10(1 / 4096), SAMPLES)
    rho_cap = (delta / 4) ** (1 / 3)
    rho = rho_cap * rng.random(SAMPLES)
    e1_norm = rng.random(SAMPLES) * rho**4
    e2_norm = rng.random(SAMPLES) * rho**3
    e3_norm = rng.random(SAMPLES) * (e2_norm + 2 * delta)
    e4_norm = rng.random(SAMPLES) * (e1_norm + 2 * delta)
    phases = rng.uniform(-np.pi, np.pi, (4, SAMPLES))
    coefficients = np.vstack((e1_norm, e2_norm, e3_norm, e4_norm)) * np.exp(1j * phases)

    root_index = rng.integers(0, 5, SAMPLES)
    omega = np.exp(2j * np.pi * root_index / 5)
    ray_t = rng.random(SAMPLES)
    ray_z = ray_t * omega
    ray_value = -delta.copy()
    for exponent in range(1, 5):
        ray_value += np.real(coefficients[exponent - 1] * ray_z**exponent)
    ray_value -= np.real(ray_z**5)
    ray_margin = ray_value + delta / 2
    normalized_ray_margin = ray_margin / delta

    disk_radius = (delta / 10) * np.sqrt(rng.random(SAMPLES))
    disk_z = disk_radius * np.exp(1j * rng.uniform(-np.pi, np.pi, SAMPLES))
    disk_value = -delta.copy()
    for exponent in range(1, 5):
        disk_value += np.real(coefficients[exponent - 1] * disk_z**exponent)
    disk_value -= np.real(disk_z**5)
    disk_margin = disk_value + 2 * delta / 5
    normalized_disk_margin = disk_margin / delta

    coefficient_ratio = (e1_norm + e2_norm + e3_norm + e4_norm) / delta
    result = {
        "schema": "erdos1041_quintic_radial_dominant_cone_check_v1",
        "exact_factor_identity": factor_identity,
        "sample_count": SAMPLES,
        "max_coefficient_budget_ratio": float(np.max(coefficient_ratio)),
        "max_normalized_ray_margin_against_minus_delta_over_two": float(np.max(normalized_ray_margin)),
        "max_normalized_disk_margin_against_minus_two_delta_over_five": float(np.max(normalized_disk_margin)),
        "dominance_constant": 4,
        "delta_upper": 1 / 4096,
    }
    passed = (
        factor_identity
        and float(np.max(coefficient_ratio)) <= 5 + 1e-12
        and float(np.max(normalized_ray_margin)) <= 1e-10
        and float(np.max(normalized_disk_margin)) <= 1e-10
    )
    result["status"] = "PASS" if passed else "FAIL"
    print(json.dumps(result, indent=2, sort_keys=True))
    if not passed:
        raise SystemExit(1)


if __name__ == "__main__":
    main()
