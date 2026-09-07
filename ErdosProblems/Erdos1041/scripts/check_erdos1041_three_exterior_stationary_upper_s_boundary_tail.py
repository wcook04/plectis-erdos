#!/usr/bin/env python3
"""Exact replay for the stationary GP3 upper-s high-w tail."""

from __future__ import annotations

from fractions import Fraction as F
import json


def ell(x: F) -> F:
    return (1 - x * x) / (1 + x + x * x) ** 2


def main() -> int:
    umax = F(1, 16)
    vmax = F(1, 2)
    pmax = F(1, 32)
    sigma_max = F(25, 16)
    lu = ell(umax)
    lv = ell(vmax)
    pair_loss = 3 * (umax * vmax + umax + vmax)
    charge_one = 3 * sigma_max / (1 - pmax)
    charge_two = 3 * sigma_max * pmax / (1 - pmax)
    correction_loss = 8 * (umax**2 / lv + vmax**2 / lu + 1 / (lu + lv))
    total_loss = correction_loss + pair_loss + charge_one + charge_two
    margin = 31 - total_loss
    identities = {
        "lu": lu == F(21760, 24843),
        "lv": lv == F(12, 49),
        "pair_loss": pair_loss == F(57, 32),
        "charge_one": charge_one == F(150, 31),
        "charge_two": charge_two == F(75, 496),
        "correction_loss": correction_loss == F(1084769987, 113603520),
        "total_loss": total_loss == F(57473958467, 3521709120),
        "margin": margin == F(51699024253, 3521709120),
        "strict": margin > 0,
    }
    passed = all(identities.values())
    result = {
        "schema": "erdos1041_three_exterior_stationary_upper_s_boundary_tail_receipt_v1",
        "certified_box": {"t": ["0", "1"], "r": ["0", "1/8"],
                          "s": ["3/8", "1/2"], "w": ["31/32", "1 (open)"]},
        "lower_L_u": str(lu),
        "lower_L_v": str(lv),
        "pair_loss": str(pair_loss),
        "charge_one_loss": str(charge_one),
        "charge_two_loss": str(charge_two),
        "correction_loss": str(correction_loss),
        "total_negative_budget": str(total_loss),
        "uniform_positive_margin": str(margin),
        "identity_checks": identities,
        "stationary_upper_s_boundary_tail_positive": passed,
        "claim_boundary": ("Exact analytic proof on r in [0,1/8], "
                           "s in [3/8,1/2], and w in [31/32,1). It does not "
                           "cover finite w, prove GP3, or prove Erdos 1041."),
        "pass": passed,
    }
    print(json.dumps(result, indent=2))
    return 0 if passed else 1


if __name__ == "__main__":
    raise SystemExit(main())
