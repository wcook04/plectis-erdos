#!/usr/bin/env python3
"""Exact audit for the induced Stern--Brocot continuant defect.

This is falsification tooling, not proof authority.  It checks the closed
ordered-subset coefficient formula against the integer recurrence and emits
compact bit-length receipts for the pressure majorants.  It intentionally
never converts giant exact fractions to decimal strings.
"""

from __future__ import annotations

import argparse
import itertools
import json
from fractions import Fraction


def fib(n: int) -> int:
    a, b = 0, 1
    for _ in range(n):
        a, b = b, a + b
    return a


def run_height(lengths: tuple[int, ...]) -> int:
    a, b = 1, 1
    for n in reversed(lengths):
        a, b = n * a + b, a
    return a + b


def subset_coefficient(r: int, positions: tuple[int, ...]) -> int:
    if not positions:
        return fib(r + 3)
    value = fib(positions[0] + 2)
    for left, right in itertools.pairwise(positions):
        value *= fib(right - left)
    return value * fib(r - positions[-1] + 1)


def defect_expansion(defects: tuple[int, ...]) -> int:
    r = len(defects)
    total = fib(r + 3)
    for size in range(1, r + 1):
        for positions in itertools.combinations(range(r), size):
            monomial = subset_coefficient(r, positions)
            for i in positions:
                monomial *= defects[i]
            total += monomial
    return total


def one_site_weights(r: int) -> list[int]:
    return [fib(i + 2) * fib(r - i + 1) for i in range(r)]


def fraction_receipt(value: Fraction) -> dict[str, int]:
    return {
        "numerator_bits": value.numerator.bit_length(),
        "denominator_bits": value.denominator.bit_length(),
    }


def pressure_receipt(r: int) -> dict[str, object]:
    weights = one_site_weights(r)
    product = Fraction(1)
    for weight in weights:
        product *= Fraction(1 << weight, (1 << weight) - 1)
    sharp_factor = product - 1
    weak_factor = Fraction(1 << fib(r + 1), (1 << fib(r + 1)) - 1) ** r - 1
    return {
        "r": r,
        "weights": weights,
        "weight_sum": sum(weights),
        "base_height": fib(r + 3),
        "sharp_product_minus_one": fraction_receipt(sharp_factor),
        "weak_product_minus_one": fraction_receipt(weak_factor),
        "boundary_ray_mersenne_bits": ((1 << fib(r + 1)) - 1).bit_length(),
    }


def main() -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument("--max-r", type=int, default=7)
    parser.add_argument("--max-defect", type=int, default=3)
    args = parser.parse_args()
    if args.max_r < 0 or args.max_defect < 0:
        parser.error("bounds must be nonnegative")

    checked = 0
    for r in range(args.max_r + 1):
        for defects in itertools.product(range(args.max_defect + 1), repeat=r):
            actual = run_height(tuple(e + 1 for e in defects))
            expanded = defect_expansion(defects)
            if actual != expanded:
                raise AssertionError(
                    f"defect formula failed: r={r} defects={defects} "
                    f"actual={actual} expanded={expanded}"
                )
            checked += 1

    weight_rows = []
    for r in range(1, args.max_r + 1):
        weights = one_site_weights(r)
        additive = [fib(r + 1) + fib(i) * fib(r - i - 1) for i in range(r)]
        if weights != additive:
            raise AssertionError(f"weight identity failed at r={r}")
        weight_rows.append(pressure_receipt(r))

    counterexamples = {
        "F_r_plus_2_floor": {
            "r": 2,
            "defects": [1, 0],
            "actual_defect": run_height((2, 1)) - fib(5),
            "false_floor": fib(4),
        },
        "strict_above_F_r_plus_1": {
            "r": 2,
            "defects": [1, 0],
            "actual_defect": run_height((2, 1)) - fib(5),
            "attained_boundary_floor": fib(3),
        },
    }
    print(
        json.dumps(
            {
                "schema": "continuant_defect_pressure_probe_v1",
                "status": "pass",
                "checked_vectors": checked,
                "max_r": args.max_r,
                "max_defect": args.max_defect,
                "pressure": weight_rows,
                "smallest_false_strengthening_counterexamples": counterexamples,
                "claim_ceiling": "exact_integer_probe_not_proof",
            },
            indent=2,
            sort_keys=True,
        )
    )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
