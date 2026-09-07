#!/usr/bin/env python3
"""Late-kill hunter: how late can a fatal rank occur for a rational target?

Samples random reduced odd targets a/b and runs the exact greedy orbit,
recording the full kill-rank distribution.  Kills require the residual to
land inside the fatal sliver (T_n, w_n), an interval of Mersenne-gap
width ~2^{-2n}; the question is whether late kills occur at all, and how
their count decays with n.
"""

from __future__ import annotations

import argparse
import json
import random
from math import gcd


def trial(a: int, b: int, depth: int, slack_bits: int = 256):
    precision = 2 * depth + slack_bits
    scale = 1 << precision
    lower = (scale * a) // b
    upper = (scale * a + b - 1) // b
    if lower == upper:
        return None  # exact dyadic-scale hit at start (a/b exact at scale)
    for n in range(1, depth + 1):
        wf = scale // ((1 << n) - 1)
        if lower >= wf + 1:
            lower -= wf + 1
            upper -= wf
        elif upper <= wf:
            pass
        else:
            return -n  # tie with weight -> finite support signal
        cap = (1 << (precision - n)) + (1 << (precision - 2 * n)) \
            if 2 * n + 2 <= precision else 0
        if lower > cap:
            return n  # fatal rank
        if upper <= 0:
            return None  # exact finite representation
    return None  # survivor


def main() -> None:
    ap = argparse.ArgumentParser()
    ap.add_argument("--samples", type=int, default=100_000)
    ap.add_argument("--max-b", type=int, default=1_000_000)
    ap.add_argument("--depth", type=int, default=400)
    ap.add_argument("--seed", type=int, default=20260822)
    args = ap.parse_args()
    rng = random.Random(args.seed)
    kill_hist: dict[int, int] = {}
    ties = 0
    survivors = 0
    max_b = args.max_b | 1
    for _ in range(args.samples):
        b = rng.randrange(3, max_b, 2)
        a = rng.randrange(1, b, 2)
        while gcd(a, b) != 1:
            a = rng.randrange(1, b, 2)
        res = trial(a, b, args.depth)
        if res is None:
            survivors += 1
        elif res < 0:
            ties += 1
        else:
            kill_hist[res] = kill_hist.get(res, 0) + 1
    killed = sum(kill_hist.values())
    out = {
        "params": vars(args),
        "survivors": survivors,
        "weight_ties_finite": ties,
        "killed": killed,
        "kill_rank_histogram": {str(k): v for k, v in sorted(kill_hist.items())},
        "max_kill_rank": max(kill_hist, default=None),
        "kills_after_rank_20": sum(v for k, v in kill_hist.items() if k > 20),
        "kills_after_rank_50": sum(v for k, v in kill_hist.items() if k > 50),
    }
    print(json.dumps(out, indent=1))


if __name__ == "__main__":
    main()
