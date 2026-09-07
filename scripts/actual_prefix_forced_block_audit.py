#!/usr/bin/env python3
"""Exact forced-doubling-block audit for actual 1/21 greedy prefixes.

At an actual skipped L, retain the genuine prefix through L and force every
rank in (L,2L] selected.  A genuine final skip would make that forced word the
actual word, hence its quotient defect at 2L must be nonnegative (and the
stronger boundary bridge asks for at least one).
"""

from __future__ import annotations

import argparse
import json
from fractions import Fraction


def w(n: int) -> Fraction:
    return Fraction(1, (1 << n) - 1)


def greedy_bits(depth: int) -> list[int]:
    remainder = Fraction(1, 21)
    bits = [0]
    for n in range(1, depth + 1):
        take = remainder >= w(n)
        if take:
            remainder -= w(n)
        bits.append(int(take))
    return bits


def defect(bits: list[int], n: int, forced_after: int | None = None) -> int:
    prefix = 0
    for k in range(1, n + 1):
        coefficient = sum(
            (bits[d] if forced_after is None or d <= forced_after else 1)
            for d in range(1, k + 1)
            if k % d == 0
        )
        prefix = 2 * prefix + coefficient
    return (1 << n) // 21 - prefix


def block_load(bits: list[int], l: int) -> int:
    return sum(
        (1 << (2 * l - n))
        * sum(bits[d] for d in range(1, l + 1) if n % d == 0)
        for n in range(l + 1, 2 * l + 1)
    )


def target_lift(l: int) -> int:
    return (1 << (2 * l)) // 21 - (1 << l) * ((1 << l) // 21)


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--max-l", type=int, default=384)
    args = parser.parse_args()
    if args.max_l < 2:
        raise SystemExit("require --max-l >= 2")
    bits = greedy_bits(2 * args.max_l)
    rows = []
    for l in range(2, args.max_l + 1):
        if bits[l]:
            continue
        q_l = defect(bits, l)
        j_l = block_load(bits, l)
        b_l = target_lift(l)
        q_forced = defect(bits, 2 * l, forced_after=l)
        assert q_forced == (1 << l) * (q_l - 1) + b_l + 1 - j_l
        rows.append({"L": l, "Q_L": q_l, "J_L": j_l, "B_L": b_l,
                     "Q_2L_forced": q_forced})
    nonnegative = [r for r in rows if r["Q_2L_forced"] >= 0]
    positive = [r for r in rows if r["Q_2L_forced"] >= 1]
    assert nonnegative == [{"L": 6, "Q_L": 1, "J_L": 4, "B_L": 3,
                            "Q_2L_forced": 0}]
    assert positive == []
    print(json.dumps({
        "method": "exact Fraction greedy bits; integer divisor counts and quotient floors",
        "max_l": args.max_l,
        "skip_count": len(rows),
        "forced_block_identity": "Q_2L=2^L*(Q_L-1)+B_L+1-J_L",
        "nonnegative_forced_Q_2L": nonnegative,
        "positive_forced_Q_2L": positive,
    }, indent=2, sort_keys=True))


if __name__ == "__main__":
    main()
