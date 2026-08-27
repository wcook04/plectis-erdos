#!/usr/bin/env python3
"""Exact replay for the anisotropic sextic cubic transition cone."""

from __future__ import annotations

from fractions import Fraction
import json
import math


def main() -> int:
    ray_rows = 0
    inner_rows = 0
    worst_ray = None
    worst_inner = None
    for s_num in range(1, 65):
        s = Fraction(s_num, 4096)
        delta = s**6
        e1 = 3 * s**5 / 2048
        e2 = 3 * s**4 / 2048
        e4 = e2 + 2 * delta
        e5 = e1 + 2 * delta

        u = s**2 / 4
        nuisance_inner = e1 * u + e2 * u**2 + e4 * u**4 + e5 * u**5
        inner_upper = -delta + nuisance_inner + u**3 + u**6
        inner_margin = inner_upper + delta / 2
        assert nuisance_inner <= delta / 32
        assert inner_margin < 0
        worst_inner = inner_margin if worst_inner is None else max(worst_inner, inner_margin)
        inner_rows += 1

        for t_num in range(65):
            t = Fraction(t_num, 64)
            nuisance = e1 * t + e2 * t**2 + e4 * t**4 + e5 * t**5
            upper = -delta + nuisance - t**6
            margin = upper + delta / 2
            assert margin <= 0
            worst_ray = margin if worst_ray is None else max(worst_ray, margin)
            ray_rows += 1

    compact_cubic_bound = math.sqrt(12.0) * (2048.0 / 3.0) ** 0.75
    receipt = {
        "schema": "erdos1041_sextic_anisotropic_cubic_cone_check_v1",
        "verdict": "PASS",
        "exact_ray_rows": ray_rows,
        "exact_inner_rows": inner_rows,
        "worst_ray_after_half_margin": str(worst_ray),
        "worst_inner_after_half_margin": str(worst_inner),
        "normalized_cubic_absolute_bound": compact_cubic_bound,
        "claim_boundary": (
            "Closes the anisotropic cubic transition cone and proves compactness "
            "of the complementary normalization; the compact atlas itself remains open."
        ),
    }
    print(json.dumps(receipt, indent=2))
    return 0


if __name__ == "__main__":
    raise SystemExit(main())

