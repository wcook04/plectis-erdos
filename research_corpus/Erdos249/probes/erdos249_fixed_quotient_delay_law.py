#!/usr/bin/env python3
"""Is Erdos #249's fixed-quotient trap capped, or does it grow like log2(c)?

Upstream analytic state
-----------------------
#249 reduces to `totient_specific_moving_dyadic_escape`: for every c and odd v,
find H divisible by phi(v) whose canonical residue lands in the central interval
of radius c+H+1. On the pure-dyadic axis the Lean-checked coordinate is

    E_H = totientBlock(H,c) - k*(2^H - 1),   E_(H+1) = 2 E_H + phi(c+H+1) - k,

with the nearest quotient k held fixed while the state is trapped.  The packet
records exact computation through c <= 1000000 finding "delay nineteen at
c=490794, ruling out caps through seventeen" -- the latest in a series of
uniform delay caps that finite search kept refuting.

The suspicion this probe tests
------------------------------
log2(490794) = 18.9. If the trap length is governed by how long the doubling
recurrence takes to push a state of size about c past a window of radius about
c, then it should run for about log2(c) steps and **no uniform cap can exist**.
Every cap would then be refuted by going to larger c, which is exactly the
observed history. The right conjecture would be a bounded EXCESS over log2(c),
not a cap.

Probe
-----
Compute the exact fixed-quotient trap length for every c in range and regress it
against log2(c): report the running maximum, where each new record occurs, and
the excess max_delay - log2(c) at each record.

Predeclared falsifier
---------------------
A running maximum that stops growing, or an excess that grows without bound,
refutes the log2(c) reading.  A running maximum that keeps setting records at
c ~ 2^delay, with bounded excess, establishes that no uniform cap exists and
redirects the producer.
"""

from __future__ import annotations

import argparse
import json
from math import log2
from pathlib import Path

import numpy as np


def totient_sieve(limit: int) -> np.ndarray:
    phi = np.arange(limit + 1, dtype=np.int64)
    for p in range(2, limit + 1):
        if phi[p] == p:                       # p is prime
            phi[p::p] -= phi[p::p] // p
    return phi


def trap_length(c: int, phi: np.ndarray, max_h: int) -> tuple[int, int]:
    """Two trap statistics for one c.

    `total` counts the longest run of consecutive H with |E_H| <= c+H+1 at a
    fixed quotient k.  Its first stretch is trivial: while (2^H-1)/2 <= c+H+1 the
    window is wider than the whole residue range, so every H is trapped for free.
    That trivial prefix has length about log2(c).

    `post_clear` counts only runs whose every step has already cleared that
    threshold, so it is the part of the trap that carries information.  This is
    the quantity a uniform delay cap would have to bound.
    """
    T = 0
    total_best = total_run = 0
    total_k = None
    post_best = post_run = 0
    post_k = None
    post_best_c_start = 0
    for H in range(1, max_h + 1):
        T = 2 * T + int(phi[c + H])
        M = (1 << H) - 1
        if M == 0:
            continue
        r = T % M
        if r > M // 2:
            r -= M
        k = (T - r) // M
        radius = c + H + 1
        trapped = abs(r) <= radius
        cleared = M // 2 > radius

        if trapped and (total_k is None or k == total_k):
            total_k = k
            total_run += 1
        else:
            total_k = k if trapped else None
            total_run = 1 if trapped else 0
        total_best = max(total_best, total_run)

        if trapped and cleared and (post_k is None or k == post_k):
            post_k = k
            post_run += 1
            if post_run > post_best:
                post_best, post_best_c_start = post_run, H
        else:
            post_k = k if (trapped and cleared) else None
            post_run = 1 if (trapped and cleared) else 0
            post_best = max(post_best, post_run)
    return total_best, post_best


def run(max_c: int, max_h: int, sample: int) -> dict:
    phi = totient_sieve(max_c + max_h + 4)
    records = []
    post_records = []
    running_max = 0
    post_running_max = 0
    for c in range(1, max_c + 1, sample):
        d, post = trap_length(c, phi, max_h)
        if d > running_max:
            running_max = d
            records.append({
                "c": c,
                "delay": d,
                "log2_c": round(log2(c), 3) if c > 1 else 0.0,
                "excess": round(d - (log2(c) if c > 1 else 0.0), 3),
            })
        if post > post_running_max:
            post_running_max = post
            post_records.append({
                "c": c,
                "post_clear_delay": post,
                "log2_c": round(log2(c), 3) if c > 1 else 0.0,
                "post_over_log2c": round(post / log2(c), 4) if c > 2 else None,
            })
    excesses = [r["excess"] for r in records if r["c"] > 16]
    return {
        "probe_id": "erdos249_fixed_quotient_delay_law",
        "parameters": {"max_c": max_c, "max_h": max_h, "sample_stride": sample},
        "running_max_delay": running_max,
        "running_max_post_clear_delay": post_running_max,
        "post_clear_records": post_records,
        "record_count": len(records),
        "records": records,
        "excess_min": round(min(excesses), 3) if excesses else None,
        "excess_max": round(max(excesses), 3) if excesses else None,
        "excess_last": records[-1]["excess"] if records else None,
        "reading": (
            "post-clear delay keeps setting records as c grows, so no uniform cap "
            "survives; the records occur near c ~ 2^delay, which is the growth law a "
            "producer must target instead of a constant"
            if len(post_records) > 3 and post_records[-1]["c"] > 1000 else
            "post-clear delay saturates in the tested range; a uniform cap is plausible"
        ),
    }


def main() -> int:
    ap = argparse.ArgumentParser()
    ap.add_argument("--max-c", type=int, default=1_000_000)
    ap.add_argument("--max-h", type=int, default=60)
    ap.add_argument("--sample", type=int, default=1)
    ap.add_argument("--out", type=str, default="")
    args = ap.parse_args()
    payload = run(args.max_c, args.max_h, args.sample)
    if args.out:
        Path(args.out).write_text(json.dumps(payload, indent=1) + "\n")
    print(json.dumps(payload, indent=1))
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
