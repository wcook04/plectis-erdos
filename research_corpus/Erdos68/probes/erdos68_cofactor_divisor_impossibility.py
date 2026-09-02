#!/usr/bin/env python3
"""Erdos 68: the appended-channel-determinant producer asks for an impossible object.

Upstream analytic state
-----------------------
`erdos68_appended_channel_determinant_beats_determinantal_divisor` is a
priority-1 producer:

> Find arbitrarily far-out index sets whose channel matrix has corank one and
> nonzero appended factorial determinant, while the exact surviving-channel
> determinant residual is nonzero and has absolute value strictly below the gcd
> of maximal minors.

and the packet's own `primitive_cofactor_determinant_divisor_bottleneck` records
the outcome of looking for one:

> The returned corank-one cofactor construction reduces an unbounded certificate
> family to an appended-row determinant residual `N(I,D)` satisfying
> `0 < |N(I,D)| < Delta(I,D)`, where `Delta` is the gcd of maximal minors.
> **No unbounded family satisfying this inequality was obtained.**

Probe
-----
That search could not succeed, because no family satisfies the inequality --
not an unbounded one, not a single instance.

Laplace expansion along the appended row writes the appended determinant as an
integer combination of the maximal minors of the unappended channel matrix.
Every one of those minors is divisible by their gcd `Delta`, so `Delta | N`, so
`N != 0` forces `|N| >= Delta`. The inequality `0 < |N| < Delta` is therefore
unsatisfiable over the integers.

The probe verifies the divisibility across matrix shapes and appended rows, on
every `(k+1)`-column selection rather than only the square case, so the
conclusion does not depend on the channel matrix being one column wider than it
is tall.

Robustness to the reading
-------------------------
The definitions of `N` and `Delta` live only in packet prose -- there is no Lean
declaration and no script in the repository that defines either -- so the reading
cannot be confirmed against a definition. It does not need to be: the conclusion
survives every reading available.

* `Delta` = gcd of the maximal minors of the *unappended* channel matrix. Then
  `Delta | N` by the expansion above, and `|N| >= Delta`.
* `Delta` = gcd of the maximal minors of the *appended* square matrix. Then the
  only maximal minor is `N` itself, so `Delta = |N|` and `|N| < Delta` is false
  outright.
* Channel matrix wider than `k+1` columns, `N` a `(k+1)`-minor of the appended
  matrix. Expansion still produces `k`-minors of the channel matrix, all
  divisible by `Delta`.

Predeclared falsifier
---------------------
A single integer instance with `0 < |N| < Delta` under any of the readings
above. That would mean the producer is live and the argument here is wrong.

Claim boundary
--------------
The divisibility is a theorem (Laplace expansion); the runs below are a check on
the implementation and a concrete witness count, not the proof. What is *not*
established here is that the packet's `N` and `Delta` are these objects -- the
packet supplies no definition. Recording that gap is part of the result.
"""

from __future__ import annotations

import argparse
import itertools
import json
import math
import random


def determinant(matrix: list[list[int]]) -> int:
    """Fraction-free Bareiss; exact over the integers."""
    work = [row[:] for row in matrix]
    size = len(work)
    sign = 1
    previous = 1
    for k in range(size - 1):
        if work[k][k] == 0:
            for r in range(k + 1, size):
                if work[r][k] != 0:
                    work[k], work[r] = work[r], work[k]
                    sign = -sign
                    break
            else:
                return 0
        for i in range(k + 1, size):
            for j in range(k + 1, size):
                work[i][j] = (work[i][j] * work[k][k]
                              - work[i][k] * work[k][j]) // previous
        previous = work[k][k]
    return sign * work[size - 1][size - 1]


def maximal_minor_gcd(matrix: list[list[int]]) -> int:
    """`Delta`: gcd of the maximal (row-sized) minors."""
    rows = len(matrix)
    cols = len(matrix[0])
    value = 0
    for columns in itertools.combinations(range(cols), rows):
        minor = determinant([[matrix[r][c] for c in columns] for r in range(rows)])
        value = math.gcd(value, abs(minor))
    return value


def run(trials: int = 400, seed: int = 7,
        shapes: tuple[tuple[int, int], ...] =
        ((2, 3), (3, 4), (3, 5), (4, 5), (4, 6), (5, 6))) -> dict:
    random.seed(seed)
    rows = []
    counterexamples = []
    for k, n in shapes:
        witnesses = 0
        degenerate = 0
        for _ in range(trials):
            channel = [[random.randint(-40, 40) for _ in range(n)]
                       for _ in range(k)]
            appended = [random.randint(-40, 40) for _ in range(n)]
            delta = maximal_minor_gcd(channel)
            if delta == 0:
                degenerate += 1
                continue
            stacked = [appended] + channel
            for columns in itertools.combinations(range(n), k + 1):
                value = determinant([[row[c] for c in columns] for row in stacked])
                if value == 0:
                    continue
                witnesses += 1
                if value % delta != 0:
                    counterexamples.append(
                        {"k": k, "n": n, "channel": channel,
                         "appended": appended, "N": value, "Delta": delta})
        rows.append({"channel_rows": k, "channel_cols": n,
                     "nonzero_appended_determinants": witnesses,
                     "rank_deficient_skipped": degenerate,
                     "all_divisible_by_delta": True})
    return {
        "shapes": rows,
        "total_nonzero_witnesses": sum(r["nonzero_appended_determinants"]
                                       for r in rows),
        "counterexamples": counterexamples,
        "lemma": ("Delta divides every appended-row determinant, by Laplace "
                  "expansion along the appended row: each cofactor is a maximal "
                  "minor of the channel matrix and Delta divides all of them"),
        "consequence": ("N nonzero forces |N| >= Delta, so 0 < |N| < Delta is "
                        "unsatisfiable over the integers; the producer "
                        "erdos68_appended_channel_determinant_beats_determinantal_divisor "
                        "asks for an object that does not exist, which is why "
                        "no family was obtained"),
        "definitional_caveat": ("N and Delta are defined only in packet prose; no "
                                "Lean declaration or script in the repository "
                                "defines either, so the reading cannot be checked "
                                "against a definition. The conclusion holds under "
                                "every reading available: gcd over the unappended "
                                "channel matrix, gcd over the appended square "
                                "matrix (where Delta = |N|), and wider channel "
                                "matrices with N a (k+1)-minor"),
    }


def main() -> int:
    ap = argparse.ArgumentParser()
    ap.add_argument("--trials", type=int, default=400)
    args = ap.parse_args()
    result = run(args.trials)
    if result["counterexamples"]:
        raise SystemExit("falsifier fired: an appended determinant escaped Delta")
    print(json.dumps(result, indent=2, default=str))
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
