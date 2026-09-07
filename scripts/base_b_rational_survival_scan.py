#!/usr/bin/env python3
"""Erdos 257: does base-2 criticality decide the answer, or only the difficulty?

Erdos 257 is the ``b = 2`` case of: for infinite ``A``, is
``sum_{a in A} 1/(b^a - 1)`` irrational?  The achievement set

    C_b = { sum_{a in A} 1/(b^a - 1) : A subset of N }

is a Cantor set for every ``b >= 2``, but its measure has a phase transition
exactly at ``b = 2``.  With ``z_n = 1/(b^n-1)`` and ``T_n = sum_{k>n} z_k``,

    z_n = sum_{j>=1} b^{-jn},      T_n = sum_{j>=1} b^{-jn}/(b^j - 1),
    gamma_n = z_n - T_n = sum_{j>=1} b^{-jn} (b^j - 2)/(b^j - 1).

The ``j = 1`` term of gamma_n vanishes iff ``b = 2``.  For ``b = 2`` the gaps
are therefore ``~ (2/3) 4^-n``, quadratically smaller than the bridges
``T_n ~ 2^-n``, and ``|C_2| = lim 2^n T_n = 1``.  For ``b >= 3`` the gaps are
``~ b^-n (b-2)/(b-1)``, the same order as the bridges, and
``|C_b| = lim 2^n T_n = 0`` with Hausdorff dimension ``log 2 / log b``.
(The measure and dimension side is already mapped by
``base_b_tractability_map.py``; what is asked here is different.)

The question this scan asks is about TARGETS, not about the set: do rational
targets in base ``b >= 3`` actually die, and how fast?  The null prediction
is that survival to depth ``N`` has probability ``(2/b)^N / ((b-1) E_b)``, so
every rational with denominator ``q`` should die by depth about
``log2(q) / log2(b/2)``, and no rational should survive deep.  Base 2 has
``62%`` of rationals surviving to depth ``2.5 x 10^4``.

If the scan confirms that, it locates the difficulty exactly: at ``b >= 3`` a
measure or gap-density argument has room to work and the analogous Erdos
question is plausibly provable that way, while at ``b = 2`` no such argument
can exist because the survivors carry full measure.  That is a statement
about which resource a proof of Erdos 257 may not use.

Companion analysis: ErdosProblems/Erdos257/SupportWordStructureLab.md
"""

from __future__ import annotations

import argparse
import hashlib
import json
import math
from typing import Any


problem_id = "erdos_257"


def canonical_sha256(payload: Any) -> str:
    return hashlib.sha256(
        json.dumps(payload, separators=(",", ":"), sort_keys=True).encode()
    ).hexdigest()


def build_tables(b: int, P: int, ranks: int) -> tuple[list[int], list[int], int]:
    """Z[n] = floor(b^P / (b^n - 1)) = sum_{j>=1} b^(P - j n);  TT[n] = sum_{k>n} Z[k]."""
    powers = [1] * (P + 1)
    for i in range(1, P + 1):
        powers[i] = powers[i - 1] * b
    Z = [0] * (P + 2)
    for n in range(1, P + 1):
        acc = 0
        e = P - n
        while e >= 0:
            acc += powers[e]
            e -= n
        Z[n] = acc
    TT = [0] * (ranks + 2)
    acc = 0
    for k in range(P, ranks, -1):
        acc += Z[k]
    for n in range(ranks, -1, -1):
        TT[n] = acc
        if n >= 1:
            acc += Z[n]
    return Z, TT, powers[P]


def scan_target(
    p: int, q: int, ranks: int, scale: int, P: int, Z: list[int], TT: list[int]
) -> dict[str, Any]:
    lo = (scale * p) // q
    hi = lo + 1
    selected = 0
    for n in range(1, ranks + 1):
        zn = Z[n]
        if lo >= zn + 1:
            lo -= zn + 1
            hi -= zn
            selected += 1
        elif hi > zn:
            return {"status": "undecided", "rank": n}
        tn = TT[n]
        if lo > tn + P:
            return {"status": "dead", "rank": n, "selected": selected}
        if hi > tn:
            return {"status": "undecided", "rank": n}
    return {"status": "alive", "selected": selected}


def scan_base(
    b: int, ranks: int, pad: int, denominators: list[int], per_q: int
) -> dict[str, Any]:
    P = ranks + pad
    Z, TT, scale = build_tables(b, P, ranks)
    E_lo = TT[0]
    E = E_lo / scale
    alive = 0
    dead = 0
    undec = 0
    death_ranks: list[int] = []
    for q in denominators:
        pmax = (E_lo * q) // scale
        step = max(1, pmax // per_q)
        for pnum in range(1, pmax + 1, step):
            out = scan_target(pnum, q, ranks, scale, P, Z, TT)
            if out["status"] == "alive":
                alive += 1
            elif out["status"] == "dead":
                dead += 1
                death_ranks.append(out["rank"])
            else:
                undec += 1
    qmax = max(denominators)
    predicted = (
        math.log2(qmax) / math.log2(b / 2) if b > 2 else float("inf")
    )
    return {
        "base": b,
        "depth": ranks,
        "erdos_borwein_E_b": E,
        "gap_to_bridge_ratio_limit": (b - 2) / (b - 1),
        "measure_of_C_b": "1 (exactly)" if b == 2 else "0",
        "hausdorff_dimension": math.log(2) / math.log(b),
        "alive": alive,
        "dead": dead,
        "undecided": undec,
        "survivor_fraction": alive / max(alive + dead, 1),
        "deepest_death_rank": max(death_ranks) if death_ranks else None,
        "predicted_all_dead_by_depth": predicted,
        "death_rank_histogram": {
            str(k): death_ranks.count(k) for k in sorted(set(death_ranks))[:40]
        },
    }


def main() -> None:
    ap = argparse.ArgumentParser()
    ap.add_argument("--bases", type=str, default="2,3,4,5,7")
    ap.add_argument("--ranks", type=int, default=400)
    ap.add_argument("--pad", type=int, default=64)
    ap.add_argument("--denominators", type=str, default="101,509,1021,4099")
    ap.add_argument("--per-q", type=int, default=80)
    ap.add_argument("--write", type=str, default=None)
    args = ap.parse_args()

    dens = [int(t) for t in args.denominators.split(",") if t.strip()]
    rows = [
        scan_base(int(t), args.ranks, args.pad, dens, args.per_q)
        for t in args.bases.split(",")
        if t.strip()
    ]
    payload = {
        "schema": "erdos257_base_b_rational_survival_v1",
        "parameters": vars(args),
        "source": {
            "script": "formal_math/erdos257_period_noncollapse/scripts/"
            "base_b_rational_survival_scan.py",
            "analysis": "formal_math/erdos257_period_noncollapse/ErdosProblems/"
            "Erdos257/SupportWordStructureLab.md",
            "related": "formal_math/erdos257_period_noncollapse/scripts/"
            "base_b_tractability_map.py",
        },
        "rows": rows,
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
