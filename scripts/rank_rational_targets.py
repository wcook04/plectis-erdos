#!/usr/bin/env python3
"""Rank every small rational by how much room its greedy orbit actually has.

Erdős #257 asks whether some infinite `A` has `∑_{n∈A} 1/(2ⁿ−1) ∈ ℚ`.  Nothing
in the problem privileges `1/2` or `1/21`, yet the whole programme aims at
those two.  This script asks the obvious question nobody asked: **of all small
rationals, which one is the easiest target?**

A rational qualifies as a candidate when

* its greedy orbit never enters the hole
  (`GreedyHoleNormalForm.GreedyMersenneHoleAt`), so it is in `𝒜` as far as the
  scan can see; **and**
* its greedy expansion does **not** terminate — a terminating expansion is a
  finite support, which settles nothing
  (`HalfCounterexampleFrontier.finiteErdosSum_ne_one_div_twenty_one` is the
  `1/21` instance of that exclusion).

Candidates are then ranked by the minimum, over skipped ranks, of the
normalised clearance `dist(R_n, hole)/gap(n+1)` — the same statistic
`check_greedy_hole_margin.py` reports for `1/21`, so the numbers compare
directly.

## Measured (260 ranks, denominators < 60)

```
non-terminating, hole-free candidates:  549
rejected: 545 entered the hole, 7 inconclusive at this precision
 1/60   clearance 1.500   (best)
 1/21   clearance 1.421   rank  47 of 549
 1/2    clearance 0.271   rank 410 of 549
```

**`1/2` is the 410th-best target of 549.**  `1/21` has five times its margin.

Two cautions, both checked.

* The cap consumers `half_mem_mersenneAchievementSet_of_skipped_dyadicCap`
  and `..._of_skipped_twoChannelCap` are hard-wired to `1/2`.  The general
  route for an arbitrary target is
  `GreedyHoleNormalForm.mem_mersenneAchievementSet_iff_holeFree`.  So `1/2`
  buys landed consumers and `1/21` buys margin.
* The family `{1/n}` is **not** uniformly good, so there is no family
  theorem: `n = 16, 22, 23, 28, 29, 32, 34, 35, 36, 38, 39, 64, 400, 1000`
  all enter the hole, and surviving clearances range from `0.168` to `1.499`.
  `n = 3, 7, 15, 31` are Mersenne, where `x = w_k` and the expansion
  terminates immediately.

All arithmetic is integer at dyadic precision; no branch is decided from a
float, and an inconclusive enclosure is reported rather than guessed.
Finite evidence, not a proof — a candidate surviving this scan may still
enter the hole later.
"""

from __future__ import annotations

import argparse
import json
from fractions import Fraction
from math import gcd


def build(ranks: int, precision: int):
    """Weights and tails.

    The tail must be summed WELL PAST `ranks`: truncating it at `ranks + 2`
    understates `T_{n+1}`, which makes the hole look wider and spuriously
    rejects candidates.  That bug cost this script 135 survivors on its first
    run (407 reported against 542 exact).  Sum until the weights vanish at
    the working precision.
    """
    scale = 1 << precision
    top = precision + 2
    weight = [0] * (top + 2)
    for n in range(1, top + 1):
        weight[n] = scale // ((1 << n) - 1)
        if weight[n] == 0:
            top = n
            break
    tail = [0] * (top + 2)
    for n in range(top, 0, -1):
        tail[n - 1] = tail[n] + weight[n]
    return scale, weight, tail


def profile(num: int, den: int, ranks: int, scale: int,
            weight: list[int], tail: list[int]):
    low = (scale * num) // den
    high = (scale * num + den - 1) // den
    worst = None
    for n in range(ranks):
        w = weight[n + 1]
        if low >= w + 1:
            low -= w + 1
            high -= w
        elif high <= w:
            t = tail[n + 1]
            if low > t:
                return None, "hole"
            gap = w - t
            if gap <= 0:
                return None, "degenerate_gap"
            # Keep this ratio exact.  Direct ``int / int`` conversion first
            # coerces the huge dyadic numerators to binary64 and overflows at
            # the deeper scans this script is meant to compare.
            clearance = Fraction(t - high, gap)
            worst = clearance if worst is None else min(worst, clearance)
        else:
            return None, "ambiguous_raise_precision"
        if high <= 0:
            return worst, "terminated"
    return worst, "alive"


def scan(max_den: int, ranks: int) -> dict:
    precision = 2 * ranks + 512
    scale, weight, tail = build(ranks, precision)
    alive, rejected = [], {"hole": 0, "terminated": 0,
                           "ambiguous_raise_precision": 0, "degenerate_gap": 0}
    for den in range(2, max_den):
        for num in range(1, den):
            if gcd(num, den) != 1:
                continue
            if num * 1000 >= 1606 * den:      # keep below the Erdos-Borwein constant
                continue
            clearance, status = profile(num, den, ranks, scale, weight, tail)
            if status == "alive":
                alive.append((clearance, num, den))
            else:
                rejected[status] = rejected.get(status, 0) + 1
    alive.sort(reverse=True)
    index = [(n, d) for _, n, d in alive]

    def row(num, den):
        key = (num, den)
        if key not in index:
            return {"target": f"{num}/{den}", "status": "not a candidate"}
        i = index.index(key)
        return {"target": f"{num}/{den}", "rank": i + 1,
                "of": len(alive), "clearance": round(float(alive[i][0]), 5)}

    return {
        "ranks": ranks,
        "max_denominator": max_den - 1,
        "candidates": len(alive),
        "rejected": rejected,
        "best": [{"target": f"{n}/{d}", "clearance": round(float(c), 5)}
                 for c, n, d in alive[:10]],
        "tightest": [{"target": f"{n}/{d}", "clearance": round(float(c), 5)}
                     for c, n, d in alive[-5:]],
        "traditional_targets": [row(1, 2), row(1, 21)],
        "claim_ceiling": (
            "finite evidence; a surviving candidate may enter the hole later"
        ),
    }


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--max-denominator", type=int, default=60)
    parser.add_argument("--ranks", type=int, default=260)
    args = parser.parse_args()
    print(json.dumps(scan(args.max_denominator + 1, args.ranks),
                     indent=2, sort_keys=True))


if __name__ == "__main__":
    main()
