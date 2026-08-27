#!/usr/bin/env python3
"""Adversarial scalar replay for the critical Blaschke pair theorem.

This verifies the exact one-variable inversion and the implications used by the
analytic proof.  It is not a checker for Riemann maps or the unrestricted
Erdős problem.
"""
from __future__ import annotations

import argparse
import json
import math


def q(r: float) -> float:
    return 1 / r - r


def q_inverse(y: float) -> float:
    return 2 / (math.sqrt(y * y + 4) + y)


def x_k(k: int, r: float) -> float:
    return q_inverse((k - 1) * q(r))


def product_floor(k: int, r: float) -> float:
    return x_k(k, r) * r ** (k - 1)


def sharp_radius(k: int, P: float) -> float:
    lo, hi = 0.0, 1.0
    for _ in range(120):
        mid = (lo + hi) / 2
        if product_floor(k, mid) < P:
            lo = mid
        else:
            hi = mid
    return hi


def main() -> int:
    ap = argparse.ArgumentParser()
    ap.add_argument("--max-k", type=int, default=40)
    ap.add_argument("--grid", type=int, default=400)
    args = ap.parse_args()
    worst_inverse = 0.0
    worst_floor = 0.0
    worst_explicit_gap = 0.0
    threshold_monotone = True
    fired = 0
    total = 0
    for k in range(2, args.max_k + 1):
        previous = -1.0
        for j in range(1, args.grid):
            r = j / args.grid
            x = x_k(k, r)
            worst_inverse = max(worst_inverse, abs(q(x) - (k - 1) * q(r)))
            floor = product_floor(k, r)
            threshold_monotone &= floor > previous
            previous = floor
            P = max(1e-14, min(1 - 1e-14, floor))
            rs = sharp_radius(k, P)
            worst_floor = max(worst_floor, abs(product_floor(k, rs) - P))
            re = min(1.0, ((k - 1) * P) ** (1 / k))
            worst_explicit_gap = max(worst_explicit_gap, rs - re)
            if rs < 1 and math.log((1 + rs * rs) / (1 - rs * rs)) <= 2:
                fired += 1
            total += 1
    failures = {}
    if worst_inverse > 2e-11:
        failures["q_inverse_error"] = worst_inverse
    if worst_floor > 2e-12:
        failures["implicit_product_error"] = worst_floor
    if worst_explicit_gap > 2e-12:
        failures["sharp_radius_exceeds_explicit_radius"] = worst_explicit_gap
    if not threshold_monotone:
        failures["product_floor_monotonicity"] = False
    receipt = {
        "schema": "erdos1041_critical_blaschke_pair_bound_probe_v1",
        "status": "pass" if not failures else "fail",
        "range": {"max_k": args.max_k, "grid": args.grid, "rows": total},
        "max_errors": {"q_inverse": worst_inverse, "implicit_product": worst_floor,
                       "sharp_minus_explicit": worst_explicit_gap},
        "bergman_threshold_rows": fired,
        "failures": failures,
        "evidence_boundary": "scalar floating-point replay; the polygon and Bergman arguments are ordinary proofs",
    }
    print(json.dumps(receipt, indent=2, sort_keys=True))
    return 0 if not failures else 1


if __name__ == "__main__":
    raise SystemExit(main())
