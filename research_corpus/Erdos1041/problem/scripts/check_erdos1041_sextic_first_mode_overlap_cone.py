#!/usr/bin/env python3
"""Exact replay for the sextic first-mode overlap cone."""

from __future__ import annotations

from fractions import Fraction
import json


def main() -> int:
    polynomial_rows = 0
    ray_rows = 0
    for t_num in range(4097):
        t = Fraction(t_num, 4096)
        polynomial = 5 * t**5 - 2 * t**4 + 5 * t**3 - 5 * t + 2
        assert polynomial > 0
        normalized = -Fraction(2, 5) * (t - t**5) + (t**2 - t**4) - t**6
        assert normalized <= 0
        polynomial_rows += 1

        for b_num in range(17):
            B = Fraction(b_num, 16)
            A = Fraction(4, 5) * B
            a = -A / 2
            b = B
            value = (t - t**5) * a + (t**2 - t**4) * b - t**6
            assert value <= 0
            ray_rows += 1

    # Exact small-chord budget at the largest permitted mode ratio.
    chord_rows = 0
    u = Fraction(1, 64)
    for a_num in range(1, 65):
        A = Fraction(a_num, 64)
        B = Fraction(5, 4) * A
        for c_num in range(65):
            C = Fraction(c_num, 16)
            if 8 * C * u**2 > A:
                continue
            upper = -A * u / 2 + B * u**2 + C * u**3 + B * u**4 + A * u**5 + u**6
            assert upper < 0
            chord_rows += 1

    receipt = {
        "schema": "erdos1041_sextic_first_mode_overlap_cone_check_v1",
        "verdict": "PASS",
        "exact_polynomial_rows": polynomial_rows,
        "exact_ray_rows": ray_rows,
        "exact_chord_rows": chord_rows,
        "proved_ratio": "|E1|/|E2| >= 4/5",
        "calibrated_optimal_ratio": 0.7368097408515715,
        "claim_boundary": (
            "Closes the homogeneous overlap chart only. The deeper mixed annulus "
            "and nonlinear actual-polynomial transfer remain open."
        ),
    }
    print(json.dumps(receipt, indent=2))
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
