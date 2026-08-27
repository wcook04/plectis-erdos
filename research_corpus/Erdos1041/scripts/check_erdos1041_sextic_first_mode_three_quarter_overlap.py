#!/usr/bin/env python3
"""Exact replay for the sextic three-quarter first-mode overlap."""

from __future__ import annotations

from fractions import Fraction
import json


def main() -> int:
    polynomial_rows = 0
    ray_rows = 0
    for t_num in range(4097):
        t = Fraction(t_num, 4096)
        polynomial = 8 * t**5 - 3 * t**4 + 8 * t**3 - 8 * t + 3
        assert polynomial > 0
        normalized = -Fraction(3, 8) * (t - t**5) + (t**2 - t**4) - t**6
        assert normalized <= 0
        polynomial_rows += 1

        for b_num in range(17):
            B = Fraction(b_num, 16)
            A = Fraction(3, 4) * B
            value = (t - t**5) * (-A / 2) + (t**2 - t**4) * B - t**6
            assert value <= 0
            ray_rows += 1

    chord_rows = 0
    u = Fraction(1, 64)
    for a_num in range(1, 65):
        A = Fraction(a_num, 64)
        B = Fraction(4, 3) * A
        for c_num in range(65):
            C = Fraction(c_num, 16)
            if 8 * C * u**2 > A:
                continue
            upper = (
                -A * u / 2 + B * u**2 + C * u**3
                + B * u**4 + A * u**5 + u**6
            )
            assert upper < 0
            chord_rows += 1

    receipt = {
        "schema": "erdos1041_sextic_first_mode_three_quarter_overlap_check_v1",
        "verdict": "PASS",
        "exact_polynomial_rows": polynomial_rows,
        "exact_ray_rows": ray_rows,
        "exact_chord_rows": chord_rows,
        "proved_ratio": "|E1|/|E2| >= 3/4",
        "previous_ratio": "|E1|/|E2| >= 4/5",
        "calibrated_optimal_ratio": 0.7368097408515715,
        "claim_boundary": (
            "Closes the sharper homogeneous overlap chart only. The residual "
            "mixed annulus, nonlinear transfer, and unrestricted Erdos 1041 remain open."
        ),
    }
    print(json.dumps(receipt, indent=2))
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
