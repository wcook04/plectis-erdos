#!/usr/bin/env python3
# SPDX-FileCopyrightText: 2026 Will Cook
# SPDX-License-Identifier: Apache-2.0
"""Exact greedy expansion of 1/2 in the weights 1/(2^n - 1).

Every decision uses exact rational arithmetic.  A skip at rank n is safe when
the remainder is at most 2^-n, because 2^-n < R_n = sum_{m>n} 1/(2^m - 1); it
is fatal when the remainder exceeds 2^-n + (2/3) 4^-n >= R_n.  The program
stops if a remainder falls between these bounds.

Usage: exact_half_greedy.py DEPTH PREFIX_LENGTH
Prints one JSON object: the selected count, the digit string eps_1 ... eps_P
of the prefix used by hong_c2_process.c, and the FNV-1a 64-bit hash of the
digits eps_1 ... eps_DEPTH, the same hash that hong_c2_process.c prints.
"""

from __future__ import annotations

import json
import sys
from fractions import Fraction


def main() -> int:
    depth, plen = int(sys.argv[1]), int(sys.argv[2])
    remainder = Fraction(1, 2)
    digits: list[int] = []
    status = "survived"
    for n in range(1, depth + 1):
        weight = Fraction(1, 2**n - 1)
        if remainder >= weight:
            digits.append(1)
            remainder -= weight
            continue
        digits.append(0)
        low = Fraction(1, 2**n)
        high = low + Fraction(2, 3) / 4**n
        if remainder > high:
            status = f"fatal skip at {n}"
            break
        if remainder > low:
            status = f"undecided skip at {n}"
            break
    h = 1469598103934665603
    for e in digits:
        h ^= e
        h = (h * 1099511628211) & 0xFFFFFFFFFFFFFFFF
    print(json.dumps({
        "target": "1/2",
        "depth": len(digits),
        "status": status,
        "selected": sum(digits),
        "first_selected": [i + 1 for i, e in enumerate(digits) if e][:30],
        "prefix_digits": "".join(map(str, digits[:plen])),
        "fnv1a64_of_digits_1_to_depth": format(h, "016x"),
    }))
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
