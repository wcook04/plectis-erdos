#!/usr/bin/env python3
"""Verify exact finite cancellation-free negative-state blocks for Erdős #243.

PURPOSE: Exhibit why arbitrarily long tail-gcd-constant blocks do not by
themselves contradict normalized centered-state vanishing or near-Sylvester
growth.  All checks use Python integers and ``fractions.Fraction``.

INTERFACE: ``--height H --tail-start C --vanish-scale K`` prints a compact JSON
receipt after checking H exact transitions.  ``C > K`` certifies
``K * |E_n| < C_n`` throughout because every centered state is ``-1``.

CONSTRAINTS: This is finite exact evidence, not Lean proof authority and not an
infinite counterexample to Erdős #243.
"""

from __future__ import annotations

import argparse
import json
import math
from fractions import Fraction
from functools import reduce
from operator import mul


def build_and_verify(height: int, tail_start: int, vanish_scale: int) -> dict[str, object]:
    if height < 1:
        raise ValueError("height must be positive")
    if tail_start < 2:
        raise ValueError("tail-start must be at least 2")
    if vanish_scale < 0:
        raise ValueError("vanish-scale must be nonnegative")
    if tail_start <= vanish_scale:
        raise ValueError("tail-start must exceed vanish-scale")

    c = tail_start
    k = reduce(mul, (c + j for j in range(2, height + 2)), 1)
    a = 1 + (c + 1) * k
    d = (a - 1) * c - 1

    max_relative_defect = Fraction(0)
    rows: list[dict[str, object]] = []

    for n in range(height):
        x = c
        assert a - 1 == (x + 1) * k
        assert d == (a - 1) * x - 1
        assert c + 1 + d == a * c
        assert d - (a - 1) * c == -1
        assert math.gcd(c, d) == 1
        assert math.gcd(a, d) == 1
        assert vanish_scale < c

        divisor = x + 2
        assert k % divisor == 0
        k_next = (k // divisor) * ((x - 1) + k * x * (x + 1))
        c_next = x + 1
        a_next = 1 + divisor * k_next
        d_next = a * d

        assert d_next == (a_next - 1) * c_next - 1
        assert c_next + d == a * c
        assert d_next == a * d
        assert a_next > a

        sylvester_defect = a * a - a + 1 - a_next
        assert sylvester_defect == (a * a - 1) // (c + 1)
        assert (a * a - 1) % (c + 1) == 0
        relative_defect = Fraction(a * a - a_next, a * a)
        assert 0 < relative_defect < Fraction(2, c + 1)
        max_relative_defect = max(max_relative_defect, relative_defect)

        rows.append(
            {
                "n": n,
                "C": c,
                "centered_state": -1,
                "tail_gcd": 1,
                "gcd_a_D": 1,
                "a_digits": len(str(a)),
                "relative_defect_bound_verified": True,
            }
        )
        c, k, a, d = c_next, k_next, a_next, d_next

    return {
        "schema": "erdos243-cancellation-free-block-receipt/1",
        "status": "verified",
        "height": height,
        "tail_start": tail_start,
        "vanish_scale": vanish_scale,
        "invariants": {
            "centered_state": -1,
            "tail_gcd": 1,
            "gcd_a_D": 1,
            "normalized_bound": "vanish_scale * |E_n| < C_n",
            "ratio_bound": "0 < (a_n^2-a_(n+1))/a_n^2 < 2/(C_n+1)",
        },
        "max_relative_defect": {
            "numerator": max_relative_defect.numerator,
            "denominator": max_relative_defect.denominator,
        },
        "first_row": rows[0],
        "last_row": rows[-1],
        "claim_ceiling": (
            "finite exact counterexample to a block-length-only contradiction; "
            "not an infinite orbit and not a counterexample to Erdős #243"
        ),
    }


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--height", type=int, default=8)
    parser.add_argument("--tail-start", type=int, default=50)
    parser.add_argument("--vanish-scale", type=int, default=10)
    args = parser.parse_args()
    receipt = build_and_verify(args.height, args.tail_start, args.vanish_scale)
    print(json.dumps(receipt, indent=2, sort_keys=True))
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
