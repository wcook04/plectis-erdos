#!/usr/bin/env python3
"""Normalised hole-clearance scan for the 1/21 greedy Mersenne orbit.

Companion receipt for `Erdos257PeriodNoncollapse/GreedyHoleNormalForm.lean`.

Death at rank n+1 happens exactly when the residual lies in the hole
    HOLE_n = ( T_{n+1} , w_{n+1} ),      w_k = 1/(2^k-1),  T_k = sum_{m>k} w_m,
whose width is gap(n+1) = w_{n+1} - T_{n+1} > 0 (super-increasingness).  This script
reports the normalised clearance

    nu_n = dist( R_n , HOLE_n ) / gap(n+1)

which must be positive at every rank for 1/21 to be achievable.  All arithmetic is
integer at dyadic precision P; no greedy branch is ever decided from a float, and an
inconclusive enclosure raises rather than guessing.  Finite evidence, not a proof.
"""
from __future__ import annotations

problem_id = "erdos_257"

import argparse
import json


def scan(ranks: int, precision_bits: int | None = None) -> dict:
    P = precision_bits or (2 * ranks + 2048)
    S = 1 << P

    # W[n] = floor(2^P / (2^n - 1)); Tail[k] = sum_{m>k} W[m]
    W = [0] * (P + 3)
    top = 1
    for n in range(1, P + 1):
        W[n] = S // ((1 << n) - 1)
        top = n
        if W[n] == 0:
            break
    Tail = [0] * (top + 3)
    for n in range(top, 0, -1):
        Tail[n - 1] = Tail[n] + W[n]

    lo, hi = S // 21, (S + 20) // 21
    worst = None
    profile = []
    skips = 0
    for n in range(1, ranks + 1):
        w = W[n]
        if lo >= w + 1:
            take = True
            lo -= w + 1
            hi -= w
        elif hi <= w:
            take = False
            skips += 1
        else:
            raise AssertionError(f"ambiguous greedy branch at rank {n}; raise precision")
        gap = W[n + 1] - Tail[n + 1]
        if gap <= 0:
            raise AssertionError(f"non-positive gap at rank {n + 1}")
        dist = (lo - W[n + 1]) if lo > Tail[n + 1] else (Tail[n + 1] - hi)
        log2_nu = (dist.bit_length() - gap.bit_length()) if dist > 0 else None
        if log2_nu is None:
            raise AssertionError(f"orbit entered the hole at rank {n + 1}")
        if worst is None or log2_nu < worst[0]:
            worst = (log2_nu, n, take)
        if n <= 12:
            profile.append({"rank": n, "take": take, "log2_clearance": log2_nu})
    return {
        "ranks": ranks,
        "precision_bits": P,
        "skips": skips,
        "skip_density": round(skips / ranks, 6),
        "opening_profile": profile,
        "min_log2_clearance": worst[0],
        "min_log2_clearance_rank": worst[1],
        "min_log2_clearance_was_take": worst[2],
        "hole_free_verified_through": ranks,
    }


def main() -> None:
    ap = argparse.ArgumentParser()
    ap.add_argument("--ranks", type=int, default=4000)
    ap.add_argument("--precision-bits", type=int)
    args = ap.parse_args()
    print(json.dumps(scan(args.ranks, args.precision_bits), indent=2, sort_keys=True))


if __name__ == "__main__":
    main()
