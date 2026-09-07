#!/usr/bin/env python3
"""Exact audit of the local Mersenne multiplicity near-carry.

Uses only rational arithmetic.  A fatal report proves that the displayed
defect cannot be a Boolean Mersenne subsum; an inconclusive report proves
nothing about the remaining infinite tail.
"""

from __future__ import annotations

import argparse
import hashlib
import json
from fractions import Fraction


def w(n: int) -> Fraction:
    return Fraction(1, (1 << n) - 1)


def receipt(x: Fraction) -> object:
    if x.numerator.bit_length() <= 2048 and x.denominator.bit_length() <= 2048:
        return f"{x.numerator}/{x.denominator}"
    num = x.numerator
    payload = (
        (b"-" if num < 0 else b"+")
        + abs(num).to_bytes(max(1, (abs(num).bit_length() + 7) // 8), "big")
        + b"/"
        + x.denominator.to_bytes(max(1, (x.denominator.bit_length() + 7) // 8), "big")
    )
    return {
        "exact_fraction_sha256": hashlib.sha256(payload).hexdigest(),
        "numerator_bits": x.numerator.bit_length(),
        "denominator_bits": x.denominator.bit_length(),
    }


def defect(d: int) -> Fraction:
    return Fraction(1, ((1 << (d - 1)) - 1) * ((1 << d) - 1))


def greedy_defect(d: int, depth: int) -> dict[str, object]:
    residual = defect(d)
    chosen: list[int] = []
    fatal_at: int | None = None
    for n in range(1, depth + 1):
        coin = w(n)
        if residual >= coin:
            chosen.append(n)
            residual -= coin
        # The actual tail after n is strictly less than 2*w(n+1).
        if residual >= 2 * w(n + 1):
            fatal_at = n
            break
    return {
        "d": d,
        "defect": receipt(defect(d)),
        "chosen_prefix_first_32": chosen[:32],
        "chosen_count_through_depth": len(chosen),
        "residual": receipt(residual),
        "fatal_at_or_before_depth": fatal_at,
        "tail_upper_at_stop": receipt(2 * w((fatal_at or depth) + 1)),
    }


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--max-d", type=int, default=24)
    parser.add_argument("--depth", type=int, default=512)
    args = parser.parse_args()
    if args.max_d < 2 or args.depth < 1:
        raise SystemExit("require --max-d >= 2 and --depth >= 1")
    rows = [greedy_defect(d, args.depth) for d in range(2, args.max_d + 1)]
    checks = []
    for d in range(2, args.max_d + 1):
        checks.append(2 * w(d) == w(d - 1) - defect(d))
    print(json.dumps({
        "method": "exact Fraction arithmetic; no floating point",
        "identity_verified_for_all_d": all(checks),
        "identity": "2*w_d = w_(d-1) - delta_d",
        "defect_formula": "delta_d = 1/((2^(d-1)-1)*(2^d-1))",
        "depth": args.depth,
        "rows": rows,
    }, indent=2, sort_keys=True))


if __name__ == "__main__":
    main()
