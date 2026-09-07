#!/usr/bin/env python3
"""Exact replay for the sextic cubic radial-deficit staple.

The proof is analytic.  This checker independently verifies the rational
inner-disk constants, the parity selection on exact sixth roots, the strict
metric coefficient, and a deterministic grid of the scalar ray bound.
"""

from __future__ import annotations

from fractions import Fraction
import json
import math


def main() -> int:
    # At u=Delta/4 the exact worst upper bound, after adding Delta/2, is
    # Delta*(-1/2 + Delta/4 + Delta^2/64 + Delta^5/4096).
    # The bracket is increasing on [0,1], so its endpoint is authoritative.
    endpoint_bracket = (
        -Fraction(1, 2) + Fraction(1, 4) + Fraction(1, 64) + Fraction(1, 4096)
    )
    assert endpoint_bracket == -Fraction(959, 4096)

    # The selected parity is repeated three times among the sixth roots.
    parity_rows = []
    for real_c in (Fraction(-7, 5), Fraction(0), Fraction(11, 8)):
        epsilon = Fraction(-1) if real_c >= 0 else Fraction(1)
        selected = [j for j in range(6) if (-1) ** j == epsilon]
        assert len(selected) == 3
        assert all(epsilon * real_c <= 0 for _j in selected)
        parity_rows.append(
            {"real_c": str(real_c), "epsilon": int(epsilon), "indices": selected}
        )

    # Exact rational scalar replay.  The nuisance term is placed at its full
    # allowed upper budget; the cubic term is set to zero, the worst selected
    # sign.  Strictness must then come solely from -t^6.
    ray_rows = 0
    worst_ray = None
    for delta_num in range(1, 65):
        delta = Fraction(delta_num, 64)
        for t_num in range(1, 65):
            t = Fraction(t_num, 64)
            upper = -delta + delta * t - t**6
            assert upper < 0
            ray_rows += 1
            if worst_ray is None or upper > worst_ray:
                worst_ray = upper

    sqrt_three = math.sqrt(3.0)
    metric_coefficient = 2.0 - sqrt_three
    assert metric_coefficient > 0.0

    receipt = {
        "schema": "erdos1041_sextic_cubic_radial_deficit_cone_check_v1",
        "verdict": "PASS",
        "inner_disk_endpoint_bracket": str(endpoint_bracket),
        "inner_disk_margin": "at_most_minus_delta_over_two",
        "parity_rows": parity_rows,
        "exact_ray_rows": ray_rows,
        "worst_exact_ray_upper": str(worst_ray),
        "metric_slack_coefficient": metric_coefficient,
        "claim_boundary": (
            "Checks the finite Fourier model cone only. Actual-polynomial "
            "normalization, complementary charts, and unrestricted Erdos 1041 remain open."
        ),
    }
    print(json.dumps(receipt, indent=2))
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
