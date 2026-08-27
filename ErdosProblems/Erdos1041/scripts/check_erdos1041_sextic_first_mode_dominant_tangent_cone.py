#!/usr/bin/env python3
"""Replay the first-mode-dominant sextic tangent cone."""

from __future__ import annotations

import cmath
from fractions import Fraction
import json
import math


def main() -> int:
    ray_rows = 0
    for a_num in range(-64, 1):
        a = Fraction(a_num, 64)
        for b_num in range(-64, 65):
            b = Fraction(b_num, 64)
            if a > -Fraction(1, 2) or b > 1:
                continue
            for t_num in range(65):
                t = Fraction(t_num, 64)
                value = (t - t**5) * a + (t**2 - t**4) * b - t**6
                assert value <= 0
                ray_rows += 1

    kernel_rows = 0
    for c in (Fraction(-1), Fraction(-1, 2), Fraction(1, 2), Fraction(1)):
        for t_num in range(64):
            t = Fraction(t_num, 64)
            numerator = (1 - t**6) * (1 - t * c)
            denominator = 1 - 2 * t * c + t**2
            assert numerator > 0 and denominator > 0
            assert numerator / denominator > 0
            kernel_rows += 1

    chord_rows = 0
    u = Fraction(1, 64)
    for a_num in range(1, 65):
        A = Fraction(a_num, 64)
        for c_num in range(65):
            C = Fraction(c_num, 16)
            assert 8 * C * u**2 <= A
            assert 8 * u**5 <= A
            upper = -A * u / 2 + A * u**2 + C * u**3 + A * u**4 + A * u**5 + u**6
            assert upper < 0
            chord_rows += 1

    # Non-authoritative phase-sector calibration.
    omega = cmath.exp(1j * math.pi / 3)
    phase_rows = 100_001
    min_adjacent_pairs = 7
    for index in range(phase_rows):
        phi = 2 * math.pi * index / (phase_rows - 1)
        projections = [(cmath.exp(1j * phi) * omega**j).real for j in range(6)]
        pairs = sum(
            projections[j] <= -0.5 + 1e-12
            and projections[(j + 1) % 6] <= -0.5 + 1e-12
            for j in range(6)
        )
        assert pairs >= 1
        min_adjacent_pairs = min(min_adjacent_pairs, pairs)

    receipt = {
        "schema": "erdos1041_sextic_first_mode_dominant_tangent_cone_check_v1",
        "verdict": "PASS",
        "exact_ray_rows": ray_rows,
        "exact_kernel_rows": kernel_rows,
        "exact_chord_rows": chord_rows,
        "phase_sector_rows": phase_rows,
        "minimum_adjacent_selected_pairs": min_adjacent_pairs,
        "claim_boundary": (
            "Checks the homogeneous first-mode-dominant tangent chart and radial "
            "kernel sign, not the nonlinear remainder transfer or second-mode chart."
        ),
    }
    print(json.dumps(receipt, indent=2))
    return 0


if __name__ == "__main__":
    raise SystemExit(main())

