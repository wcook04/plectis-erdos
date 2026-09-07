#!/usr/bin/env python3
"""Exact tests for the delta_3 = w_2 - 2 w_3 defect coordinate.

This is deliberately a falsifier for simple positive/statistical readings of
the denominator-21 defect.  It uses only integers and Fraction.
"""

from __future__ import annotations

import json
from fractions import Fraction


def w(n: int) -> Fraction:
    return Fraction(1, (1 << n) - 1)


def epsilon(n: int) -> int:
    return int(n % 6 in {2, 4, 5})


def row_data(depth: int) -> list[dict[str, object]]:
    remainder = Fraction(1, 21)
    selected: list[int] = []
    prefix = 0
    rows = []
    for n in range(1, depth + 1):
        bit = remainder >= w(n)
        if bit:
            remainder -= w(n)
            selected.append(n)
        coefficient = sum(n % d == 0 for d in selected)
        prefix = 2 * prefix + coefficient
        target = (1 << n) // 21
        q = target - prefix
        floor_identity_rhs = (1 << n) // 3 - 2 * ((1 << n) // 7) - epsilon(n)
        assert target == floor_identity_rhs
        residue_counts = tuple(sum(d % 3 == r for d in selected) for r in range(3))
        suffix6 = tuple(int(d in selected) for d in range(max(1, n - 5), n + 1))
        rows.append({
            "N": n,
            "Q": q,
            "selected": tuple(selected),
            "residue_counts_mod_3": residue_counts,
            "suffix6": suffix6,
        })
    return rows


def main() -> None:
    rows = row_data(128)
    by_n = {row["N"]: row for row in rows}
    # Exact counterexample to Q being a nondecreasing cumulative count after
    # subtracting any six-periodic baseline.
    assert (by_n[19]["Q"], by_n[25]["Q"]) == (2, 1)
    assert 19 % 6 == 25 % 6
    # Even all three selected-residue counts plus the denominator period do
    # not determine Q; no new selected index occurs in this six-rank gap.
    assert by_n[93]["residue_counts_mod_3"] == by_n[99]["residue_counts_mod_3"]
    assert by_n[93]["selected"] == by_n[99]["selected"]
    assert (by_n[93]["Q"], by_n[99]["Q"]) == (1, 2)
    # The natural six-bit suffix state also fails.
    assert 40 % 6 == 94 % 6
    assert by_n[40]["suffix6"] == by_n[94]["suffix6"]
    assert (by_n[40]["Q"], by_n[94]["Q"]) == (0, 1)
    print(json.dumps({
        "method": "exact integer floors plus Fraction greedy orbit; no floating point",
        "floor_identity": "floor(2^N/21)=floor(2^N/3)-2*floor(2^N/7)-epsilon(N)",
        "epsilon_residues_mod_6": [2, 4, 5],
        "cumulative_count_no_go": {"N": [19, 25], "Q": [2, 1]},
        "mod3_count_no_go": {"N": [93, 99], "Q": [1, 2]},
        "suffix6_no_go": {"N": [40, 94], "Q": [0, 1]},
    }, indent=2, sort_keys=True))


if __name__ == "__main__":
    main()
