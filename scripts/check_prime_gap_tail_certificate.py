#!/usr/bin/env python3
# SPDX-FileCopyrightText: 2026 Will Cook
# SPDX-License-Identifier: Apache-2.0
"""Replay the actual #251 adjacent-tail certificates using integer arithmetic.

The manuscript proves the infinite-tail radius from prime0_le_polynomial.
This script checks the finite prime lists, weighted gap blocks, polynomial
identity, and strict integer margins. It is not a Lean proof or cofinal supply.
"""
from __future__ import annotations

import json
from fractions import Fraction
from math import comb, isqrt


def primes(count: int) -> list[int]:
    result = []
    candidate = 2
    while len(result) < count:
        if all(candidate % divisor for divisor in range(2, isqrt(candidate) + 1)):
            result.append(candidate)
        candidate += 1
    return result


def fourth_moment(m: int) -> int:
    return m**4 + 8 * m**3 + 36 * m**2 + 104 * m + 150


def certificate(gaps: list[int], shift: int, base: int, depth: int) -> dict:
    denominator = 2**depth
    block = sum((gaps[base + shift + j] - gaps[base + j]) * 2**(depth - j)
                for j in range(1, depth + 1))
    radius = 1250 * (fourth_moment(base + shift + depth + 2)
                     + fourth_moment(base + depth + 2))
    residue = block % denominator
    distance = min(residue, denominator - residue)
    return {
        "shift": shift, "base": base, "depth": depth,
        "block_numerator": block, "denominator": denominator,
        "radius_numerator": radius,
        "integer_separation_margin": distance - radius,
        "open_unit_interval_margin": denominator - abs(block) - radius,
        "enclosure": [str(Fraction(block - radius, denominator)),
                      str(Fraction(block + radius, denominator))],
    }


def main() -> int:
    # Coefficientwise verification of 2P(m) = (m+1)^4 + P(m+1).
    coefficients = (150, 104, 36, 8, 1)
    if any(2 * coefficients[i] != comb(4, i) +
           sum(coefficients[j] * comb(j, i) for j in range(i, 5))
           for i in range(5)):
        raise RuntimeError("fourth-moment polynomial identity failed")
    ps = primes(46)
    gaps = [right - left for left, right in zip(ps, ps[1:])]
    rows = [certificate(gaps, 1, base, 40) for base in (2, 3)]
    expected = ((-662838684750, 11764181250), (873345886050, 12805761250))
    for row, (block, radius) in zip(rows, expected):
        if (row["block_numerator"], row["radius_numerator"]) != (block, radius):
            raise RuntimeError("paper certificate numerals do not match the prime gaps")
        if min(row["integer_separation_margin"], row["open_unit_interval_margin"]) <= 0:
            raise RuntimeError("the claimed strict tail certificate failed")
    if not (gaps[4] == 2 and gaps[3] == 4):
        raise RuntimeError("the adjacent pair's gap mismatch failed")
    print(json.dumps({
        "evidence": "exact integer replay with the manuscript's analytic tail bound",
        "boundary": "two finite actual-tail certificates, not cofinal supply or a Lean proof",
        "certificates": rows,
        "mismatched_gaps": {"g4": gaps[4], "g3": gaps[3]},
    }, indent=2))
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
