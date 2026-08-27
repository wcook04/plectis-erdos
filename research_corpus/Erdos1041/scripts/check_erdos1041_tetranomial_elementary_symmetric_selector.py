#!/usr/bin/env python3
"""Exact replay for the sharp second tail-energy selector witness."""

from __future__ import annotations

import json
from fractions import Fraction
from math import gcd

import numpy as np


def hierarchy_boundary_probe() -> dict[str, object]:
    """Replay a valid three-safe-tail row missed by every symmetric layer."""

    a = complex(-1.40969554, -0.11378447)
    b = complex(1.40714865, 0.14107251)
    c = complex(-0.98363525, -0.17947812)
    roots = np.roots([1, a, 0, 0, b, c])
    tails = np.sort(np.abs(c + b * roots) ** 2)
    product = float(np.prod(tails))
    defects: dict[str, float] = {}
    from itertools import combinations
    from math import comb

    for k in range(1, 5):
        energy = float(sum(np.prod(tails[list(indices)]) for indices in combinations(range(5), k)))
        threshold = float(comb(4, k) + product * comb(4, k - 1))
        defects[str(k)] = energy - threshold

    assert float(np.max(np.abs(roots))) < 1
    assert product < 1
    assert int(np.sum(tails < 1)) == 3
    assert all(defect > 1 for defect in defects.values())
    return {
        "coefficients": {
            "a": [a.real, a.imag],
            "b": [b.real, b.imag],
            "c": [c.real, c.imag],
        },
        "max_root_modulus": float(np.max(np.abs(roots))),
        "tail_energy_product": product,
        "sorted_tail_energies": [float(value) for value in tails],
        "safe_tail_count": int(np.sum(tails < 1)),
        "sharp_layer_defects": defects,
        "claim_ceiling": "falsifies hierarchy exhaustiveness only; all selector theorems survive"
    }


def main() -> None:
    r = Fraction(63, 64)
    u = Fraction(41, 100)
    q = r**4

    pair_energy = q**4 * (6 * r**4 + 8 * r**2 * u**2 + 6 * u**4)
    total_energy = 4 * q**2 * (r**2 + u**2)
    l1_budget = q * (1 + u)
    distance_lower = r**2 + u**2 - Fraction(10, 7) * r * u
    quartic_pair_distance_sq = 2 * r**2

    assert 0 < r < 1
    assert 0 < u < 1
    assert gcd(gcd(5, 4), 1) == 1
    assert pair_energy < 6
    assert total_energy > 4
    assert l1_budget > 1
    assert Fraction(10, 7) ** 2 > 2  # sqrt(2) < 10/7
    assert distance_lower > Fraction(5, 9)
    assert quartic_pair_distance_sq > Fraction(5, 9)

    receipt = {
        "schema": "erdos1041_tetranomial_elementary_symmetric_selector_audit_v1",
        "status": "pass",
        "exact_family": {
            "r": str(r),
            "u": str(u),
            "q_equals_r_pow_four": str(q),
            "polynomial": "(z-u)(z^4+q)=z^5-u*z^4+q*z-u*q",
            "primitive_exponent_pattern": [5, 4, 1, 0],
            "tail_energy_product": "0",
            "pair_energy": str(pair_energy),
            "pair_threshold": "6",
            "pair_margin": str(Fraction(6) - pair_energy),
            "total_energy": str(total_energy),
            "old_total_threshold": "4",
            "old_total_excess": str(total_energy - 4),
            "l1_budget": str(l1_budget),
            "root_pair_distance_sq_rational_lower": str(distance_lower),
            "quartic_fibre_pair_distance_sq": str(quartic_pair_distance_sq),
            "close_pair_threshold_sq": "5/9"
        },
        "hierarchy_boundary_probe": hierarchy_boundary_probe(),
        "proof_authority": "analytic compression theorem and Lean kernel; this script exactly replays the rational strict-extension inequalities"
    }
    print(json.dumps(receipt, indent=2, sort_keys=True))


if __name__ == "__main__":
    main()
