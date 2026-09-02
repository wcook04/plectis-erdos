#!/usr/bin/env python3
"""Numerical and exact regression for CriticalSpokeMomentSweep20260826."""

from __future__ import annotations

import argparse
import cmath
from fractions import Fraction
import json
import math
import random


def exact_witness() -> dict[str, object]:
    # Gaussian integers represented by pairs.
    u = [(-3, -2), (0, 3), (3, -1)]
    assert (sum(x for x, _ in u), sum(y for _, y in u)) == (0, 0)
    values = [complex(x, y) for x, y in u]
    s2 = sum(value * value for value in values)
    assert s2 == complex(4, 6)
    signs = [Fraction(92, 169), -Fraction(4, 9), -Fraction(1, 25)]
    for value, expected in zip(values, signs, strict=True):
        measured = (s2 / (value * value)).real
        assert abs(measured - float(expected)) < 1e-14
    assert sum(value > 0 for value in signs) == 1
    return {"u": u, "S2": [4, 6], "real_coefficients": [str(row) for row in signs], "positive_count": 1}


def polynomial_value(roots: list[complex], z: complex) -> complex:
    out = 1 + 0j
    for root in roots:
        out *= z - root
    return out


def random_sweep(seed: int, trials: int) -> float:
    rng = random.Random(seed)
    worst = 0.0
    for _ in range(trials):
        # Choose n-1 reciprocal vectors and close S1=0; reject zero entries.
        n = rng.randrange(3, 9)
        u = [complex(rng.uniform(-3, 3), rng.uniform(-3, 3)) for _ in range(n - 1)]
        u.append(-sum(u))
        if min(abs(value) for value in u) < 1e-5:
            continue
        roots = [1 / value for value in u]  # c=0 is critical because sum u_i=0.
        p0 = polynomial_value(roots, 0j)
        r = rng.uniform(0.0, 0.95 / max(abs(value) ** 2 for value in u))
        log_product = sum(
            cmath.log(abs(polynomial_value(roots, r * value.conjugate()) / p0)).real
            for value in u
        )
        # Independent truncated power-sum reconstruction.
        series = 0.0
        scaled = [math.sqrt(r) * value for value in u]
        for m in range(1, 1000):
            # r^m |sum u_i^m|^2 = |sum (sqrt(r)u_i)^m|^2.  This
            # form cannot overflow because max |sqrt(r)u_i| < 1.
            sm = sum(value ** m for value in scaled)
            term = -(abs(sm) ** 2) / m
            series += term
            if m > 100 and abs(term) < 1e-16:
                break
        error = abs(log_product - series)
        worst = max(worst, error)
        assert log_product <= 2e-11
        assert error < 2e-9
    return worst


def main() -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument("--json", action="store_true")
    parser.add_argument("--trials", type=int, default=500)
    args = parser.parse_args()
    payload = {
        "schema": "erdos1041_critical_spoke_moment_sweep_check_v1",
        "exact_one_descending_witness": exact_witness(),
        "random_trial_count": args.trials,
        "maximum_series_error": random_sweep(20260826, args.trials),
        "pass": True,
    }
    print(json.dumps(payload, indent=2) if args.json else "PASS " + json.dumps(payload, sort_keys=True))
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
