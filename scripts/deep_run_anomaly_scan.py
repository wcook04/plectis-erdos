#!/usr/bin/env python3
"""Erdos 257: many rational targets, deep, scored by the run law.

Why this and not a survivor-density census.  A target's greedy decisions to
depth ``N`` depend only on ``x`` to precision ``gamma_N ~ (2/3) 4^-N``, i.e.
on its first ``2N`` binary digits.  Rationals with denominator ``q``
equidistribute at scale ``1/q``, so for ``N > log_4 q`` they are forced to
reproduce the Cantor-measure statistics exactly, and a survivor-density
census can say nothing there.  All of its deaths necessarily sit at depth
``O(log q)``.  To probe the regime that actually matters one must take
``N >> log_4 q`` -- many targets, run deep.

The observable is the run law of SupportWordStructureLab.md section 3: a
target dies exactly when its greedy word ends in an INFINITE run of selected
ranks, and a finite run of length ``L`` beginning at ``m+1`` certifies the
survival margin ``delta_m = T_m - r_{m-1}`` in ``(T_{m+L+1}, T_{m+L}]``.  So

    R_N = max run of consecutive selected ranks below N

is a single integer recording the closest approach to death over the whole
history.  Under the Bernoulli(1/2) null it is a Gumbel variable with mode
``log2 N`` and scale ``1/ln 2 = 1.4427``, so over ``S`` independent targets
the maximum should be near ``log2 N + 1.4427 * ln S``.  Death at rank ``m``
requires ``R ~ m``.  Any target whose ``R_N`` sits far above the Gumbel band
is the first visible arithmetic signal in this problem; none does so far.

Death is detected exactly (not by run length): the scan carries a certified
enclosure of ``T_n`` and stops at the first rank with ``r_n > T_n``.

Companion analysis: ErdosProblems/Erdos257/SupportWordStructureLab.md
"""

from __future__ import annotations

import argparse
import hashlib
import json
import math
from typing import Any


def canonical_sha256(payload: Any) -> str:
    return hashlib.sha256(
        json.dumps(payload, separators=(",", ":"), sort_keys=True).encode()
    ).hexdigest()


def build_tables(P: int, ranks: int) -> tuple[list[int], list[int]]:
    nbytes = (P + 8) // 8 + 1
    pat = bytearray(nbytes)
    Z = [0] * (P + 2)
    for n in range(1, P + 1):
        pos = P - n
        positions = []
        while pos >= 0:
            positions.append(pos)
            pos -= n
        for u in positions:
            pat[nbytes - 1 - (u >> 3)] |= 1 << (u & 7)
        Z[n] = int.from_bytes(bytes(pat), "big")
        for u in positions:
            pat[nbytes - 1 - (u >> 3)] = 0
    TT = [0] * (ranks + 2)
    acc = 0
    for k in range(P, ranks, -1):
        acc += Z[k]
    for n in range(ranks, -1, -1):
        TT[n] = acc
        if n >= 1:
            acc += Z[n]
    return Z, TT


def scan_target(
    p: int, q: int, ranks: int, P: int, Z: list[int], TT: list[int]
) -> dict[str, Any]:
    lo = ((1 << P) * p) // q
    hi = lo + 1
    best = 0
    best_at = 0
    cur = 0
    start = 0
    selected = 0
    for n in range(1, ranks + 1):
        zn = Z[n]
        if lo >= zn + 1:
            lo -= zn + 1
            hi -= zn
            selected += 1
            if cur == 0:
                start = n
            cur += 1
            if cur > best:
                best, best_at = cur, start
        elif hi > zn:
            return {"status": "undecided", "rank": n}
        else:
            cur = 0
        tn = TT[n]
        if lo > tn + P:
            return {"status": "dead", "rank": n, "max_take_run": best}
        if hi > tn:
            return {"status": "undecided", "rank": n}
    return {
        "status": "alive",
        "max_take_run": best,
        "max_take_run_start": best_at,
        "selected": selected,
        "density": selected / ranks,
    }


def main() -> None:
    ap = argparse.ArgumentParser()
    ap.add_argument("--ranks", type=int, default=10000)
    ap.add_argument("--pad", type=int, default=128)
    ap.add_argument("--denominators", type=str, default="101,211,509,1021")
    ap.add_argument("--per-q", type=int, default=90)
    ap.add_argument("--write", type=str, default=None)
    args = ap.parse_args()

    P = 2 * args.ranks + args.pad
    Z, TT = build_tables(P, args.ranks)
    E_lo = TT[0]

    hist: dict[int, int] = {}
    alive = 0
    dead = 0
    undec = 0
    top: list[list[Any]] = []
    death_ranks: list[int] = []
    densities: list[float] = []
    for q in [int(t) for t in args.denominators.split(",") if t.strip()]:
        pmax = (E_lo * q) // (1 << P)
        step = max(1, pmax // args.per_q)
        for pnum in range(1, pmax + 1, step):
            out = scan_target(pnum, q, args.ranks, P, Z, TT)
            if out["status"] == "alive":
                alive += 1
                r = out["max_take_run"]
                hist[r] = hist.get(r, 0) + 1
                densities.append(out["density"])
                top.append([r, f"{pnum}/{q}", out["max_take_run_start"]])
            elif out["status"] == "dead":
                dead += 1
                death_ranks.append(out["rank"])
            else:
                undec += 1
    top.sort(reverse=True)
    n_alive = max(alive, 1)
    gumbel_mode = math.log2(args.ranks)
    gumbel_expected_max = gumbel_mode + 1.4427 * math.log(n_alive)
    payload = {
        "schema": "erdos257_deep_run_anomaly_v1",
        "parameters": vars(args),
        "source": {
            "script": "formal_math/erdos257_period_noncollapse/scripts/"
            "deep_run_anomaly_scan.py",
            "analysis": "formal_math/erdos257_period_noncollapse/ErdosProblems/"
            "Erdos257/SupportWordStructureLab.md",
        },
        "result": {
            "alive": alive,
            "dead": dead,
            "death_rank_max": max(death_ranks) if death_ranks else None,
            "death_rank_histogram": {
                str(k): death_ranks.count(k) for k in sorted(set(death_ranks))
            },
            "undecided": undec,
            "depth": args.ranks,
            "log4_q_range": [
                round(math.log(int(t), 4), 2)
                for t in args.denominators.split(",")
                if t.strip()
            ],
            "max_take_run_histogram": {str(k): v for k, v in sorted(hist.items())},
            "gumbel_mode_log2_N": gumbel_mode,
            "gumbel_expected_max_over_sample": gumbel_expected_max,
            "observed_max_take_run": top[0][0] if top else None,
            "top_runs": top[:15],
            "mean_support_density": (
                sum(densities) / len(densities) if densities else None
            ),
            "min_support_density": min(densities) if densities else None,
            "max_support_density": max(densities) if densities else None,
        },
    }
    payload["payload_sha256"] = canonical_sha256(payload)
    text = json.dumps(payload, indent=2, sort_keys=True, default=str)
    if args.write:
        with open(args.write, "w", encoding="utf-8") as h:
            h.write(text + "\n")
        print(f"wrote {args.write} sha256={payload['payload_sha256']}")
    else:
        print(text)


if __name__ == "__main__":
    main()
