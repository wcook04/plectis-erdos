#!/usr/bin/env python3
"""Exact rational replay for the stationary GP3 high-w tail theorem."""

from __future__ import annotations

from fractions import Fraction as F
import json


def ell(x: F) -> F:
    return (1 - x * x) / (1 + x + x * x) ** 2


def main() -> int:
    umax = F(3, 64)
    vmax = F(3, 8)
    pmax = F(9, 512)
    sigma_max = F(91, 64)

    lu = ell(umax)
    lv = ell(vmax)
    pair_loss = 3 * (umax * vmax + umax + vmax)
    charge_one = 3 * sigma_max / (1 - pmax)
    charge_two = 3 * sigma_max * pmax / (1 - pmax)
    correction_loss = 8 * (umax**2 / lv + vmax**2 / lu + 1 / (lu + lv))
    total_loss = correction_loss + pair_loss + charge_one + charge_two
    margin = 31 - total_loss

    identities = {
        "lu": lu == F(16740352, 18464209),
        "lv": lv == F(3520, 9409),
        "pair_loss": pair_loss == F(675, 512),
        "charge_one": charge_one == F(2184, 503),
        "charge_two": charge_two == F(2457, 32192),
        "correction_loss": correction_loss == F(96467582307569032337, 12803983069044654080),
        "total_loss": total_loss == F(85469412147568185075271, 6440403483729461002240),
        "margin": margin == F(114183095848045105994169, 6440403483729461002240),
        "strict": margin > 0,
    }
    passed = all(identities.values())
    result = {
        "schema": "erdos1041_three_exterior_stationary_boundary_tail_receipt_v1",
        "certified_box": {"t": ["0", "1"], "r": ["0", "1/8"],
                          "s": ["1/4", "3/8"], "w": ["31/32", "1 (open)"]},
        "lower_L_u": str(lu),
        "lower_L_v": str(lv),
        "pair_loss": str(pair_loss),
        "charge_one_loss": str(charge_one),
        "charge_two_loss": str(charge_two),
        "correction_loss": str(correction_loss),
        "total_negative_budget": str(total_loss),
        "uniform_positive_margin": str(margin),
        "identity_checks": identities,
        "stationary_boundary_tail_positive": passed,
        "claim_boundary": ("Exact analytic proof for the stationary residual "
                           "on r in [0,1/8], s in [1/4,3/8], and "
                           "w in [31/32,1). It does not cover the ordered-cone "
                           "complement, prove GP3, or prove Erdos 1041."),
        "pass": passed,
    }
    print(json.dumps(result, indent=2))
    return 0 if passed else 1


if __name__ == "__main__":
    raise SystemExit(main())
