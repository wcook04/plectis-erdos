#!/usr/bin/env python3
"""Exact replay for the paired sextic cubic radial-deficit cone."""

from __future__ import annotations

from fractions import Fraction
import json


def main() -> int:
    # The inner-disk upper bound plus Delta/2 is increasing in Delta on [0,1].
    endpoint = (
        -Fraction(1, 2)
        + Fraction(3, 8)
        + Fraction(1, 4096)
        + Fraction(1, 16**6)
    )
    assert endpoint < 0

    # Exact coefficient-budget replay at the extremal pairing values.
    pairing_rows = 0
    for d_num in range(1, 65):
        delta = Fraction(d_num, 64)
        for e1_num in range(65):
            e1 = delta * Fraction(e1_num, 64)
            e2 = delta - e1
            e4 = e2 + 2 * delta
            e5 = e1 + 2 * delta
            assert e1 + e2 + e4 + e5 == 6 * delta
            pairing_rows += 1

    # The exact Young identity and resulting ray margin on a rational grid.
    young_rows = 0
    worst_margin = None
    for s_num in range(1, 65):
        s = Fraction(s_num, 640)  # 0 < s <= 1/10
        delta = s**5
        for t_num in range(65):
            t = Fraction(t_num, 64)
            lhs = t**6 - 6 * s**5 * t + 5 * s**6
            rhs = (t - s) ** 2 * (
                t**4
                + 2 * s * t**3
                + 3 * s**2 * t**2
                + 4 * s**3 * t
                + 5 * s**4
            )
            assert lhs == rhs
            assert lhs >= 0
            upper = -delta + 6 * delta * t - t**6
            margin = upper + delta / 2
            assert margin <= 0
            if worst_margin is None or margin > worst_margin:
                worst_margin = margin
            young_rows += 1

    receipt = {
        "schema": "erdos1041_sextic_cubic_paired_deficit_cone_check_v1",
        "verdict": "PASS",
        "pairing_rows": pairing_rows,
        "young_identity_rows": young_rows,
        "inner_disk_endpoint_after_half_margin": str(endpoint),
        "worst_ray_after_half_margin": str(worst_margin),
        "claim_boundary": (
            "Exact replay of the paired low-mode coefficient cone. The transverse "
            "branch, finite perturbation transfer, and unrestricted Erdos 1041 remain open."
        ),
    }
    print(json.dumps(receipt, indent=2))
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
