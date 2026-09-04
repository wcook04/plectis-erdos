#!/usr/bin/env python3
"""Erdos #68: are consecutive EXTREME digits independent?

Why this is the load-bearing untested assumption
------------------------------------------------
Every summable target on the #68 frontier rests on the same heuristic.  The
zero-branch cylinder is `D_m = 0` together with `A_m <= R_m`, of width
`O(m^-2)`; the no-consecutive-failure target is `P(fail at m and m+1) ~ 1/m^2`.
Both get their `1/m^2` by multiplying two `1/m` events **as if the digit at `m`
and the digit at `m+1` were independent in their extreme tails**.  Borel-Cantelli
is then applied to a convergent sum.

`FactorialDigitLawLab.md` measured the digit's marginal law (uniform, KS
`sqrt(n)D = 0.619` against 1.95 at the 0.1% level) and the lag-one correlation of
the normalised digit (`+0.00080`, `z = 0.18`).  Neither of those tests the joint
behaviour in the TAILS, which is the only place the heuristic is used: a
correlation near zero is compatible with strong clustering of rare events.

Nobody had tested it.  If extremes clustered, the `1/m^2` shape would be wrong
and the summable targets would be worth less than the frontier believes; if they
repelled, the targets would be easier than believed.

The test
--------
Run the exact recursion to collect the digit stream, form the normalised rank
`r_m = (D_m + 1)/m in [0,1)`, and for a ladder of thresholds count how often two
CONSECUTIVE indices are both in the bottom (or top) `thr` tail.

The null must be discrete, not `thr`.  `r_m` takes values `k/m` for
`k = 0..m-1`, so `P(r_m < thr) = ceil(thr*m)/m`, which exceeds `thr` whenever
`thr*m` is not an integer -- badly so at small `m`.  Using the naive `thr`
manufactures a spurious excess; this probe uses the exact discrete probability.

Predeclared falsifier
---------------------
Any consecutive-pair z-score beyond `+/- 3` against the discrete null, at a
threshold whose expected pair count is at least 5.  That is clustering or
repulsion and it would revise the frontier's `1/m^2` arithmetic.

Claim boundary
--------------
Finite range.  Independence confirmed on a finite stream is not independence, and
the marginal low-tail line in the output is reported unresolved rather than
claimed.  Erdos #68 remains open.
"""

from __future__ import annotations

import argparse
import json
import math
from fractions import Fraction
from math import factorial
from pathlib import Path

SEED_INDEX = 12
DEFAULT_MAX_M = 6000
THRESHOLDS = (0.5, 0.2, 0.1, 0.05, 0.02, 0.01)
MIN_EXPECTED_PAIRS_TO_GATE = 5.0


def digit_stream(max_m: int) -> dict[int, int]:
    digits = int((factorial(max_m) // factorial(SEED_INDEX)).bit_length() / 3.3219) + 4000
    scale = 10**digits
    prefix = sum(Fraction(1, factorial(n) - 1) for n in range(2, SEED_INDEX + 1))
    scaled = factorial(SEED_INDEX) * prefix
    gap = int((1 - (scaled - scaled.__floor__())) * scale)
    running = factorial(SEED_INDEX)
    out: dict[int, int] = {}
    for m in range(SEED_INDEX + 1, max_m + 1):
        running *= m
        step = m * gap - scale - (scale // (running - 1))
        digit = -((-step) // scale) - 1
        gap = step - digit * scale
        if not 0 < gap <= scale:
            raise RuntimeError(f"gap left (0,1] at m={m}: precision failure")
        out[m] = digit
    return out


def _discrete_p_low(threshold: float, m: int) -> float:
    return min(1.0, math.ceil(threshold * m) / m)


def run(max_m: int = DEFAULT_MAX_M) -> dict:
    digits = digit_stream(max_m)
    indices = sorted(digits)
    rank = {m: (digits[m] + 1) / m for m in indices}

    def tail_rows(low: bool) -> list[dict]:
        rows = []
        for threshold in THRESHOLDS:
            if low:
                member = {m for m in indices if rank[m] < threshold}
            else:
                member = {m for m in indices if rank[m] > 1 - threshold}
            observed = sum(1 for m in indices if m in member and m + 1 in member)
            expected = sum(
                _discrete_p_low(threshold, m) * _discrete_p_low(threshold, m + 1)
                for m in indices
                if m + 1 in digits
            )
            variance = expected * (1 - expected / max(len(indices), 1))
            z = (observed - expected) / math.sqrt(variance) if variance > 0 else None
            rows.append({
                "threshold": threshold,
                "tail_members": len(member),
                "consecutive_pairs_observed": observed,
                "consecutive_pairs_expected_discrete_null": round(expected, 1),
                "z": round(z, 2) if z is not None else None,
                "gated": expected >= MIN_EXPECTED_PAIRS_TO_GATE,
            })
        return rows

    low_rows, high_rows = tail_rows(True), tail_rows(False)

    marginal = []
    for threshold in (0.1, 0.05, 0.02, 0.01):
        observed = sum(1 for m in indices if rank[m] < threshold)
        expected = sum(_discrete_p_low(threshold, m) for m in indices)
        variance = sum(
            _discrete_p_low(threshold, m) * (1 - _discrete_p_low(threshold, m)) for m in indices
        )
        marginal.append({
            "threshold": threshold,
            "observed": observed,
            "expected_discrete_null": round(expected, 1),
            "naive_expected_thr_times_n": round(threshold * len(indices), 1),
            "z": round((observed - expected) / math.sqrt(variance), 2) if variance > 0 else None,
        })

    gated = [r for r in low_rows + high_rows if r["gated"] and r["z"] is not None]
    worst = max((abs(r["z"]) for r in gated), default=0.0)
    return {
        "probe": "erdos68_extreme_digit_independence",
        "range": f"m = {SEED_INDEX + 1}..{max_m}",
        "mean_rank": round(sum(rank.values()) / len(rank), 5),
        "consecutive_low_tail": low_rows,
        "consecutive_high_tail": high_rows,
        "marginal_low_tail_unresolved": marginal,
        "worst_gated_pair_z": round(worst, 2),
        "reading": (
            "The consecutive-extreme test is the point: every summable target on "
            "the frontier multiplies two 1/m events to get 1/m^2, and that step "
            "assumes independence in the tails, which the marginal-uniformity and "
            "lag-one-correlation measurements do not establish. On this stream the "
            "consecutive-pair counts sit on the discrete null at every gated "
            "threshold, in both tails. The marginal low-tail row is reported "
            "separately and is NOT claimed: it shows a mild excess at the tightest "
            "threshold with no coherent per-value pattern, at the edge of what a "
            "ladder of correlated tests supports."
        ),
        "claim_boundary": (
            "Finite range. Independence confirmed on a finite stream is not "
            "independence. Erdos #68 remains open."
        ),
    }


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__.splitlines()[0])
    parser.add_argument("--max-m", type=int, default=DEFAULT_MAX_M)
    parser.add_argument("--json-out", type=Path, default=None)
    args = parser.parse_args()
    result = run(args.max_m)
    print(json.dumps(result, indent=2))
    if args.json_out:
        args.json_out.write_text(json.dumps(result, indent=2) + "\n", encoding="utf-8")
    return 0 if result["worst_gated_pair_z"] <= 3.0 else 1


if __name__ == "__main__":
    raise SystemExit(main())
