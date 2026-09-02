#!/usr/bin/env python3
"""Exact and directional replay of the quintic equality cubic extension."""

from __future__ import annotations

import json

import numpy as np
import sympy as sp


DIRECTIONS = 1_000_000


def main() -> None:
    s3, s5, y = sp.symbols("s3 s5 y", positive=True, real=True)
    contacts = [
        y * (s5 + sp.I),
        sp.I * y * (s3 - 1),
        y * (-s5 + sp.I),
        -sp.I * y * (s3 + 1),
    ]
    cubic = [sp.expand(sp.re(sp.I * z**3)) for z in contacts]
    expected = [
        -14 * y**3,
        (s3 - 1) ** 3 * y**3,
        -14 * y**3,
        -(s3 + 1) ** 3 * y**3,
    ]
    contact_values_exact = all(
        sp.rem(sp.expand(actual - target), s5**2 - 5, s5) == 0
        for actual, target in zip(cubic, expected, strict=True)
    )
    cubic_sum_reduced = sp.rem(sp.expand(sum(expected) + 48 * y**3), s3**2 - 3, s3)
    cubic_sum_exact = cubic_sum_reduced == 0

    sqrt3, sqrt5 = np.sqrt(3.0), np.sqrt(5.0)
    y_value = 0.29240177382128685
    gradients = np.array([
        [sqrt5 * y_value, -y_value, -4 * y_value**2],
        [0, -(sqrt3 - 1) * y_value, (sqrt3 - 1) ** 2 * y_value**2],
        [-sqrt5 * y_value, -y_value, -4 * y_value**2],
        [0, (sqrt3 + 1) * y_value, (sqrt3 + 1) ** 2 * y_value**2],
    ])
    cubic_values = y_value**3 * np.array([
        -14,
        (sqrt3 - 1) ** 3,
        -14,
        -(sqrt3 + 1) ** 3,
    ])
    rng = np.random.default_rng(1041_48)
    vectors = rng.normal(size=(DIRECTIONS, 4))
    vectors[:, 3] = np.abs(vectors[:, 3])
    vectors /= np.linalg.norm(vectors, axis=1)[:, None]
    variations = vectors[:, :3] @ gradients.T + vectors[:, 3, None] * cubic_values
    selected = np.min(variations, axis=1)
    average_residual = np.max(np.abs(np.mean(variations, axis=1) + 12 * vectors[:, 3] * y_value**3))

    result = {
        "schema": "erdos1041_quintic_equality_cubic_extension_check_v1",
        "contact_values_exact": contact_values_exact,
        "cubic_sum_exact_minus_48_y_cubed": cubic_sum_exact,
        "direction_count": DIRECTIONS,
        "largest_best_extended_variation": float(np.max(selected)),
        "average_identity_max_residual": float(average_residual),
        "normalized_cubic_values": [float(value) for value in cubic_values / y_value**3],
    }
    passed = (
        contact_values_exact
        and cubic_sum_exact
        and float(np.max(selected)) < 0
        and float(average_residual) < 1e-14
    )
    result["status"] = "PASS" if passed else "FAIL"
    print(json.dumps(result, indent=2, sort_keys=True))
    if not passed:
        raise SystemExit(1)


if __name__ == "__main__":
    main()
