#!/usr/bin/env python3
"""Erdos 257: does the greedy avoid divisor-rich ranks?

Different central object.  The pseudorandomness battery treats the support as
a binary WORD and finds nothing.  This probe treats ``f_A(n) = #{d | n : d in A}``
as an ARITHMETIC FUNCTION, where there is a concrete dynamical reason to
expect structure.

The carry obeys ``Q_n = 2 Q_{n-1} + t_n - f_A(n) >= 0``, so

    f_A(n) <= 2 Q_{n-1} + t_n,

i.e. a large divisor load at rank ``n`` must be paid for by carry banked
beforehand.  Carry is usually small.  So the forced greedy is under standing
pressure to keep the divisors of highly composite ranks OUT of the support --
a pressure that is invisible to any additive or spectral test of the word,
because it is indexed by the divisor lattice, not by translation.

Null model.  For a support of density 1/2 chosen without regard to divisor
structure, ``E[f_A(n)] = d(n)/2`` exactly, so

    E[ f_A(n) / d(n) ] = 1/2   for every value of d(n),
    P[ n in A | d(n) = k ]  = 1/2   for every k.

A decreasing trend in either statistic as ``d(n)`` or ``omega(n)`` grows is
real structure, and it is structure of exactly the kind a proof would need:
it would say the support is forced to thin out precisely where the divisor
lattice concentrates.

The probe separates the trivial self-term: ``s_n = f_A(n) - 1_A(n)`` is the
PROPER divisor load, which is what the carry inequality actually constrains.

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


def greedy(p: int, q: int, ranks: int, Z: list[int], TT: list[int], P: int) -> bytearray:
    lo = ((1 << P) * p) // q
    hi = lo + 1
    w = bytearray(ranks + 1)
    for n in range(1, ranks + 1):
        zn = Z[n]
        if lo >= zn + 1:
            lo -= zn + 1
            hi -= zn
            w[n] = 1
        elif hi > zn:
            raise RuntimeError(f"undecided at rank {n}")
        if lo > TT[n] + P:
            raise ValueError(f"{p}/{q} dead at rank {n}")
        if hi > TT[n]:
            raise RuntimeError(f"death test undecided at rank {n}")
    return w


def analyse(p: int, q: int, ranks: int, pad: int, reps: int = 40) -> dict[str, Any]:
    P = 2 * ranks + pad
    Z, TT = build_tables(P, ranks)
    w = greedy(p, q, ranks, Z, TT, P)

    d = [0] * (ranks + 1)
    omega = [0] * (ranks + 1)
    load = [0] * (ranks + 1)          # f_A(n)
    for k in range(1, ranks + 1):
        for m in range(k, ranks + 1, k):
            d[m] += 1
        if w[k]:
            for m in range(k, ranks + 1, k):
                load[m] += 1
    for k in range(2, ranks + 1):
        if omega[k] == 0:
            for m in range(k, ranks + 1, k):
                omega[m] += 1

    lo_n = ranks // 4                  # skip the transient

    def bin_stats(key: list[int], name: str, cap: int) -> dict[str, Any]:
        agg: dict[int, list[float]] = {}
        for n in range(lo_n, ranks + 1):
            k = min(key[n], cap)
            row = agg.setdefault(k, [0.0, 0.0, 0.0])
            row[0] += 1
            row[1] += load[n] / d[n]
            row[2] += w[n]
        out = {}
        for k in sorted(agg):
            cnt, frac, mem = agg[k]
            if cnt < 30:
                continue
            se = 0.5 / math.sqrt(cnt)
            out[str(k)] = {
                "count": int(cnt),
                "mean_fA_over_d": frac / cnt,
                "z_fA_over_d": (frac / cnt - 0.5) / (se / math.sqrt(max(k, 1))),
                "P_in_A": mem / cnt,
                "z_P_in_A": (mem / cnt - 0.5) / se,
            }
        return out

    # Permutation null.  E[f_A(n)/d(n)] is NOT 1/2 under any realistic null:
    # f_A weights small divisors heavily (a small d divides many n) and the
    # support has a transient near the origin, so the statistic is dominated
    # by the density profile of A at small ranks rather than by its bulk
    # density.  The correct null therefore resamples A while PRESERVING that
    # profile: independent Bernoulli membership with the empirical density of
    # A inside each dyadic block [2^i, 2^(i+1)).  Any residual deviation is
    # divisor-lattice structure and nothing else.
    import random

    rng = random.Random(12345)
    block_density: list[float] = []
    i = 0
    while (1 << i) <= ranks:
        a0, a1 = 1 << i, min(ranks, (1 << (i + 1)) - 1)
        cnt = sum(w[a0 : a1 + 1])
        block_density.append(cnt / (a1 - a0 + 1))
        i += 1

    def resample_stat(reps: int) -> dict[str, list[float]]:
        acc: dict[int, list[float]] = {}
        for _ in range(reps):
            ws = bytearray(ranks + 1)
            for a in range(1, ranks + 1):
                if rng.random() < block_density[a.bit_length() - 1]:
                    ws[a] = 1
            ld = [0] * (ranks + 1)
            for k in range(1, ranks + 1):
                if ws[k]:
                    for m in range(k, ranks + 1, k):
                        ld[m] += 1
            per: dict[int, list[float]] = {}
            for n in range(lo_n, ranks + 1):
                k = min(d[n], 48)
                row = per.setdefault(k, [0.0, 0.0])
                row[0] += 1
                row[1] += ld[n] / d[n]
            for k, (c, f) in per.items():
                acc.setdefault(k, []).append(f / c)
        return acc

    null = resample_stat(reps)
    tot = ranks - lo_n + 1
    return {
        "target": f"{p}/{q}",
        "ranks": ranks,
        "window_from": lo_n,
        "density": sum(w[lo_n : ranks + 1]) / tot,
        "mean_fA_over_d_overall": sum(
            load[n] / d[n] for n in range(lo_n, ranks + 1)
        )
        / tot,
        "by_d": bin_stats(d, "d", 48),
        "permutation_null_by_d": {
            str(k): {
                "null_mean": sum(v) / len(v),
                "null_sd": (
                    (sum((x - sum(v) / len(v)) ** 2 for x in v) / max(len(v) - 1, 1))
                    ** 0.5
                ),
                "reps": len(v),
            }
            for k, v in sorted(null.items())
        },
        "by_omega": bin_stats(omega, "omega", 6),
        "max_d": max(d[lo_n:]),
        "max_fA": max(load[lo_n:]),
    }


def main() -> None:
    ap = argparse.ArgumentParser()
    ap.add_argument("--ranks", type=int, default=40000)
    ap.add_argument("--pad", type=int, default=128)
    ap.add_argument("--targets", type=str, default="1/21,4/9,3/11,1/465,1/5,90/511")
    ap.add_argument("--reps", type=int, default=40)
    ap.add_argument("--write", type=str, default=None)
    args = ap.parse_args()

    rows = []
    for tok in args.targets.split(","):
        tok = tok.strip()
        if not tok:
            continue
        a, b = tok.split("/")
        try:
            rows.append(analyse(int(a), int(b), args.ranks, args.pad, args.reps))
        except ValueError as exc:
            rows.append({"target": tok, "status": "dead", "detail": str(exc)})

    payload = {
        "schema": "erdos257_divisor_richness_bias_v1",
        "parameters": vars(args),
        "null_model": (
            "support of density 1/2 chosen independently of divisor structure: "
            "E[f_A(n)/d(n)] = 1/2 and P[n in A | d(n)=k] = 1/2 for every k"
        ),
        "source": {
            "script": "formal_math/erdos257_period_noncollapse/scripts/"
            "divisor_richness_bias_probe.py",
            "analysis": "formal_math/erdos257_period_noncollapse/ErdosProblems/"
            "Erdos257/SupportWordStructureLab.md",
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
