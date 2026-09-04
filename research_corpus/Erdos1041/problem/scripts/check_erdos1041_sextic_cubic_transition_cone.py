#!/usr/bin/env python3
"""Exact rational replay for the sextic cubic transition cone."""

from __future__ import annotations

from fractions import Fraction
import json


def main() -> int:
    budget_rows = 0
    ray_rows = 0
    inner_rows = 0
    worst_ray = None
    worst_inner = None

    for s_num in range(1, 65):
        s = Fraction(s_num, 4096)  # 0 < s <= 1/64
        delta = s**6
        low = s**5 / 16
        total = 2 * low + 4 * delta
        cap = 3 * s**5 / 16
        assert total <= cap
        assert cap == 6 * (s / 2) ** 5
        budget_rows += 1

        u = s**2 / 4
        inner_upper = -delta + cap * u + u**3 + u**6
        inner_margin = inner_upper + delta / 2
        assert inner_margin < 0
        if worst_inner is None or inner_margin > worst_inner:
            worst_inner = inner_margin
        inner_rows += 1

        for t_num in range(65):
            t = Fraction(t_num, 64)
            young_gap = t**6 - 6 * (s / 2) ** 5 * t + 5 * (s / 2) ** 6
            assert young_gap >= 0
            upper = -delta + cap * t - t**6
            margin = upper + delta / 2
            assert margin <= 0
            if worst_ray is None or margin > worst_ray:
                worst_ray = margin
            ray_rows += 1

    receipt = {
        "schema": "erdos1041_sextic_cubic_transition_cone_check_v1",
        "verdict": "PASS",
        "budget_rows": budget_rows,
        "ray_rows": ray_rows,
        "inner_rows": inner_rows,
        "worst_ray_after_half_margin": str(worst_ray),
        "worst_inner_after_half_margin": str(worst_inner),
        "transition_threshold": "|E1|+|E2| <= Delta^(5/6)/16",
        "claim_boundary": (
            "Checks the cubic transition cone only. The quantitatively transverse "
            "compact atlas and actual-polynomial transfer remain open."
        ),
    }
    print(json.dumps(receipt, indent=2))
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
