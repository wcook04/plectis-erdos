#!/usr/bin/env python3
# SPDX-FileCopyrightText: 2026 Will Cook
# SPDX-License-Identifier: Apache-2.0
"""Check the quotient-row remainder identity (I) of the Erdős #257 record.

For a row n >= 6 the integer weights are w(n,d) = floor(4^n/(2^d-1)),
2 <= d <= n-1, and the target is T_n = 2^(2n-1) - 2^n.  The ascending
greedy gives a take set D_n and a skip set Skip_n.  With
rem(n) = T_n - sum_{d in D_n} w(n,d) and Delta_n = rem(n) - 2^n, the
identity is

    Delta_n = K(2n) + sum_{d in Skip_n} w(n,d),
    K(M) = 2^(M-1) - sum_{d=2}^{M} floor(2^M/(2^d-1)).

The record proves (I) for every n >= 6.  This program is a finite exact
check of the same identity, together with the recurrence
K(2) = 1, K(M+1) = 2K(M) - (tau(M+1) - 1) and the auxiliary sum
sum_{d=n}^{2n} floor(4^n/(2^d-1)) = 2^(n+1) used in its proof.

Written on 23 September 2026 for the public record.  The two earlier
computations the record reports for rows 6 to 200 were not found.
Python integers only; no floating point.
"""

from __future__ import annotations

import argparse
import json


def tau(n: int) -> int:
    count = 0
    d = 1
    while d * d <= n:
        if n % d == 0:
            count += 1 if d * d == n else 2
        d += 1
    return count


def k_direct(m: int) -> int:
    return (1 << (m - 1)) - sum((1 << m) // ((1 << d) - 1) for d in range(2, m + 1))


def check(max_row: int) -> dict:
    # K by the recurrence, checked against the definition at every index used.
    k_rec = {2: 1}
    for m in range(2, 2 * max_row):
        k_rec[m + 1] = 2 * k_rec[m] - (tau(m + 1) - 1)
    recurrence_mismatches = [m for m in range(2, 2 * max_row + 1) if k_rec[m] != k_direct(m)]

    identity_mismatches = []
    auxiliary_mismatches = []
    for n in range(6, max_row + 1):
        four_n = 1 << (2 * n)
        weights = {d: four_n // ((1 << d) - 1) for d in range(2, n)}
        target = (1 << (2 * n - 1)) - (1 << n)
        acc = 0
        skipped = []
        for d in range(2, n):
            if acc + weights[d] <= target:
                acc += weights[d]
            else:
                skipped.append(d)
        delta = target - acc - (1 << n)
        if delta != k_rec[2 * n] + sum(weights[d] for d in skipped):
            identity_mismatches.append(n)
        if sum(four_n // ((1 << d) - 1) for d in range(n, 2 * n + 1)) != 1 << (n + 1):
            auxiliary_mismatches.append(n)
    return {
        "probe": "erdos257_quotient_identity_check",
        "rows": [6, max_row],
        "rows_checked": max_row - 5,
        "identity_mismatches": identity_mismatches,
        "recurrence_indices_checked": [2, 2 * max_row],
        "recurrence_mismatches": recurrence_mismatches,
        "auxiliary_sum_mismatches": auxiliary_mismatches,
        "anchor_rem_14": (1 << 27) - (1 << 14)
        - sum((1 << 28) // ((1 << d) - 1) for d in (2, 3, 6, 7)),
    }


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__.split("\n\n")[0])
    parser.add_argument("--max-row", type=int, default=200, help="last row checked (default 200)")
    args = parser.parse_args()
    if args.max_row < 6:
        parser.error("--max-row must be at least 6")
    result = check(args.max_row)
    print(json.dumps(result, indent=2, sort_keys=True))
    clean = not (result["identity_mismatches"] or result["recurrence_mismatches"]
                 or result["auxiliary_sum_mismatches"])
    return 0 if clean else 1


if __name__ == "__main__":
    raise SystemExit(main())
