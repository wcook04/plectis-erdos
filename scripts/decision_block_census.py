#!/usr/bin/env python3
"""Decision-word block census for the two candidate greedy orbits.

Runs an orbit (target 1/21 via the exact quotient chain, or target 1/2 via
the exact residual replay) and computes, over the full depth:

* complete k-block frequency census for k <= kmax (missing blocks are
  forbidden-word theorems in the making);
* longest run of each symbol and of selected longer patterns;
* lag-autocorrelation of the bit stream at lags 1..64;
* block-entropy profile.

Under the Haar/doubling null the stream should look like a fair coin:
every k-block present for k <= log2(depth) - c, run maxima ~ log2 depth,
zero autocorrelation.  Any deviation is structure.
"""

from __future__ import annotations

import argparse
import json
from collections import Counter


def quotient_chain_bits(ranks: int) -> str:
    dc = [0] * (ranks + 1)
    qc = [0] * (2 * ranks + 3)
    state = 0
    bits = ["0"]  # rank one is always skipped for 1/21
    for n in range(2, ranks + 1):
        prev = n - 1
        pulse = 2 * qc[2 * prev + 1] + qc[2 * prev + 2]
        tp = (4 * pow(2, 2 * prev, 21)) // 21
        core = 4 * state + tp - pulse
        coin = (1 << n) + 1
        take = coin <= core
        state = core - coin if take else core
        bits.append("1" if take else "0")
        if take:
            for m in range(n, ranks + 1, n):
                dc[m] += 1
            for m in range(n, 2 * ranks + 3, n):
                qc[m] += 1
    return "".join(bits)


def half_bits(ranks: int) -> str:
    precision = 2 * ranks + 256
    scale = 1 << precision
    lower = scale // 2
    upper = lower
    bits = []
    for n in range(2, ranks + 1):
        wf = scale // ((1 << n) - 1)
        if lower >= wf + 1:
            bits.append("1")
            lower -= wf + 1
            upper -= wf
        elif upper <= wf:
            bits.append("0")
        else:
            raise AssertionError("ambiguous")
    return "".join(bits)


def census(word: str, kmax: int) -> dict:
    n = len(word)
    missing = {}
    freq = {}
    for k in range(1, kmax + 1):
        c = Counter(word[i:i + k] for i in range(n - k + 1))
        seen = len(c)
        missing[k] = (1 << k) - seen
        freq[k] = c.most_common(4)
    runs = {}
    for sym in "01":
        best = cur = 0
        for ch in word:
            cur = cur + 1 if ch == sym else 0
            best = max(best, cur)
        runs[sym] = best
    # autocorrelation at small lags on +/-1 coding
    pm = [1 if ch == "1" else -1 for ch in word]
    total = sum(pm)
    ac = {}
    for lag in range(1, 65):
        s = 0
        for i in range(n - lag):
            s += pm[i] * pm[i + lag]
        ac[lag] = round(s / (n - lag), 6)
    return {
        "length": n,
        "ones_density": total / n,
        "missing_blocks_by_k": missing,
        "top_blocks_by_k": {k: v for k, v in freq.items() if k <= 6},
        "max_runs": runs,
        "autocorr_1_64": ac,
    }


def main() -> None:
    ap = argparse.ArgumentParser()
    ap.add_argument("--orbit", choices=["21", "half"], required=True)
    ap.add_argument("--ranks", type=int, default=1_000_000)
    ap.add_argument("--kmax", type=int, default=16)
    args = ap.parse_args()
    word = quotient_chain_bits(args.ranks) if args.orbit == "21" \
        else half_bits(args.ranks)
    out = census(word, args.kmax)
    out["orbit"] = args.orbit
    print(json.dumps(out, indent=1))


if __name__ == "__main__":
    main()
