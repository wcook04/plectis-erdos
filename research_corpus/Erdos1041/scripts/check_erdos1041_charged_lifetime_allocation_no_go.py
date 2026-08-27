#!/usr/bin/env python3
"""Exact rational replay for the charged-lifetime scalar allocation no-go."""

from __future__ import annotations

import json
from fractions import Fraction


def pointwise_max_excess(x: Fraction, y: Fraction) -> Fraction:
    assert x >= 0 and y >= 0
    excess = max(x, y) - y
    assert 0 <= excess <= x
    return excess


def main() -> int:
    pointwise_rows = []
    for x in [Fraction(0), Fraction(1, 37), Fraction(5, 9), Fraction(7, 3)]:
        for y in [Fraction(0), Fraction(1, 19), Fraction(2, 7), Fraction(11, 6)]:
            excess = pointwise_max_excess(x, y)
            pointwise_rows.append(
                {"x": str(x), "y": str(y), "max_excess": str(excess)}
            )

    # Exact finite-tree witness: base lifetime 17/10 has target n/4=2,
    # so slack is 3/10.  Positive node and leaf aggregates retain strictness.
    base = Fraction(17, 10)
    target = Fraction(2)
    slack = target - base
    node_charge = slack / 2
    leaf_charge = slack
    charged = base + node_charge / 2 + leaf_charge / 4
    assert node_charge > 0 and leaf_charge > 0
    assert charged == Fraction(37, 20) < target

    energy_rows = []
    for k in range(2, 17):
        margin = Fraction(1, k + 3)
        energy = margin / k
        ceiling = Fraction(k) * energy / 2
        assert 0 < energy and ceiling < margin
        energy_rows.append(
            {
                "k": k,
                "margin": str(margin),
                "energy": str(energy),
                "kE_over_2": str(ceiling),
            }
        )

    receipt = {
        "schema": "erdos1041_charged_lifetime_allocation_no_go_check_v1",
        "status": "pass",
        "pointwise_max_domination_rows": pointwise_rows,
        "finite_tree_charge_fixture": {
            "base": str(base),
            "target": str(target),
            "slack": str(slack),
            "node_charge": str(node_charge),
            "leaf_charge": str(leaf_charge),
            "charged_total": str(charged),
        },
        "arbitrarily_small_energy_rows": energy_rows,
        "claim_boundary": (
            "exact scalar abstraction no-go; actual polynomial energies are not "
            "asserted to be independently prescribable"
        ),
    }
    print(json.dumps(receipt, indent=2, sort_keys=True))
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
