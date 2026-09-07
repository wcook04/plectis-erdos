#!/usr/bin/env python3
"""Erdos 257: does the rational survivor density match the Cantor measure?

The Mersenne achievement set

    C = { sum_{a in A} 1/(2^a - 1) : A subset of N }  subset [0, E],
    E = sum_{k>=1} 1/(2^k - 1) = 1.60669515...   (Erdos-Borwein constant)

is a Cantor set, because  z_n := 1/(2^n - 1)  strictly dominates its own
tail  T_n := sum_{k>n} z_k.  Its depth-``N`` approximation ``C_N`` is a
union of ``2^N`` intervals of length ``T_N`` each, so

    |C_N| = 2^N T_N = 1 + 2^-N/3 + 2^-2N/7 + ...   ->   1,

i.e. ``C`` has Lebesgue measure EXACTLY 1 inside an interval of length
``E``.  For a uniformly random real in ``[0, E]`` the probability of
surviving the forced greedy to depth ``N`` is therefore

    S_pred(N) = 2^N T_N / E,     S_pred(inf) = 1/E = 0.62244997...

and the convergence is geometric: ``S_pred`` is already ``1/E`` to ten
decimals by depth 35.

This census measures the same quantity for RATIONAL targets ``p/q``.  It is
a mechanism discriminator, not a horizon audit:

*   If the rational survivor fraction saturates at ``1/E`` and stops
    decaying with depth, then rational targets are statistically
    indistinguishable from random reals under this dynamics.  There is then
    no arithmetic obstruction available to a proof of Erdos 257, and the
    surviving targets are counterexample candidates.
*   If the fraction keeps decaying with depth (any rate), an arithmetic
    obstruction is present and its rate is the object to explain.

Both outcomes are one-way information about which mechanism can exist.

Exactness.  Everything is integer.  ``Z[n] = floor(2^P / (2^n - 1))`` and
``TT[n] = sum_{k>n} Z[k]`` are shared across every target in a batch, so
``T_n`` is enclosed by ``[TT[n], TT[n] + P] / 2^P``.  A target is certified
dead at rank ``n`` when its remainder enclosure satisfies ``lo > TT[n] + P``
(no completion can reach it) and certified alive when ``hi <= TT[n]``.

Companion analysis: ErdosProblems/Erdos257/SupportWordStructureLab.md
"""

from __future__ import annotations

import argparse
import hashlib
import json
from typing import Any


def canonical_sha256(payload: Any) -> str:
    blob = json.dumps(payload, separators=(",", ":"), sort_keys=True)
    return hashlib.sha256(blob.encode("utf-8")).hexdigest()


def build_tables(P: int, ranks: int) -> tuple[list[int], list[int]]:
    """Z[n] = floor(2^P/(2^n-1)) for n <= P; TT[n] = sum_{k>n} Z[k]."""
    nbytes = (P + 8) // 8 + 1
    pat = bytearray(nbytes)
    Z = [0] * (P + 2)
    for n in range(1, P + 1):
        positions = []
        pos = P - n
        while pos >= 0:
            positions.append(pos)
            pos -= n
        for pos in positions:
            pat[nbytes - 1 - (pos >> 3)] |= 1 << (pos & 7)
        Z[n] = int.from_bytes(bytes(pat), "big")
        for pos in positions:
            pat[nbytes - 1 - (pos >> 3)] = 0
    TT = [0] * (ranks + 2)
    acc = 0
    for k in range(P, ranks, -1):
        acc += Z[k]
    for n in range(ranks, -1, -1):
        TT[n] = acc
        acc += Z[n] if n >= 1 else 0
    return Z, TT


def run_target(
    p: int, q: int, ranks: int, P: int, Z: list[int], TT: list[int]
) -> tuple[int | None, int | None, int]:
    """Return (death_rank, undecided_rank, selected_count)."""
    scale = 1 << P
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
            return None, n, selected
        # certified death test: r_n > T_n means no completion reaches x
        tn = TT[n]
        if lo > tn + P:
            return n, None, selected
        if hi > tn:
            return None, n, selected
    return None, None, selected


def census(
    denominators: list[int], ranks: int, checkpoints: list[int], pad: int
) -> dict[str, Any]:
    P = 2 * ranks + pad
    Z, TT = build_tables(P, ranks)
    # E enclosure at scale 2^P
    E_lo = TT[0]
    rows = []
    for q in denominators:
        pmax = (E_lo * q) // (1 << P)
        deaths: list[int] = []
        undecided = 0
        alive = 0
        total = 0
        coprime_total = 0
        coprime_alive = 0
        death_by_rank: dict[int, int] = {}
        for p in range(1, pmax + 1):
            total += 1
            d, u, _sel = run_target(p, q, ranks, P, Z, TT)
            g = _gcd(p, q)
            if u is not None:
                undecided += 1
                continue
            if d is None:
                alive += 1
                if g == 1:
                    coprime_alive += 1
            else:
                deaths.append(d)
                death_by_rank[d] = death_by_rank.get(d, 0) + 1
            if g == 1:
                coprime_total += 1
        surv_by_depth = {}
        for c in checkpoints:
            if c > ranks:
                continue
            survivors = alive + sum(1 for d in deaths if d > c)
            surv_by_depth[str(c)] = survivors / total if total else None
        rows.append(
            {
                "q": q,
                "targets": total,
                "alive_to_full_depth": alive,
                "dead": len(deaths),
                "undecided": undecided,
                "survivor_fraction": alive / total if total else None,
                "coprime_targets": coprime_total,
                "coprime_alive": coprime_alive,
                "coprime_survivor_fraction": (
                    coprime_alive / coprime_total if coprime_total else None
                ),
                "survivor_fraction_by_depth": surv_by_depth,
                "death_rank_histogram": {
                    str(k): v for k, v in sorted(death_by_rank.items())[:60]
                },
                "max_death_rank": max(deaths) if deaths else None,
            }
        )
    # predicted survival fractions from the Cantor measure
    pred = {}
    for c in checkpoints + [ranks]:
        if c > ranks:
            continue
        pred[str(c)] = (TT[c] * (1 << c)) / E_lo
    return {
        "precision_bits": P,
        "erdos_borwein_E": E_lo / (1 << P),
        "predicted_survivor_fraction_by_depth": pred,
        "predicted_limit_one_over_E": (1 << P) / E_lo,
        "rows": rows,
    }


def _gcd(a: int, b: int) -> int:
    while b:
        a, b = b, a % b
    return a


def main() -> None:
    ap = argparse.ArgumentParser()
    ap.add_argument("--ranks", type=int, default=300)
    ap.add_argument("--pad", type=int, default=96)
    ap.add_argument(
        "--denominators",
        type=str,
        default="21,63,101,255,511,997,1024,2047,4099",
    )
    ap.add_argument("--checkpoints", type=str, default="20,40,80,150,300")
    ap.add_argument("--write", type=str, default=None)
    args = ap.parse_args()

    dens = [int(t) for t in args.denominators.split(",") if t.strip()]
    cps = [int(t) for t in args.checkpoints.split(",") if t.strip()]
    result = census(dens, args.ranks, cps, args.pad)
    payload = {
        "schema": "erdos257_mersenne_survivor_density_v1",
        "parameters": {
            "ranks": args.ranks,
            "pad": args.pad,
            "denominators": args.denominators,
            "checkpoints": args.checkpoints,
        },
        "source": {
            "script": "formal_math/erdos257_period_noncollapse/scripts/"
            "mersenne_survivor_density_census.py",
            "analysis": "formal_math/erdos257_period_noncollapse/ErdosProblems/"
            "Erdos257/SupportWordStructureLab.md",
        },
        "result": result,
    }
    payload["payload_sha256"] = canonical_sha256(payload)
    text = json.dumps(payload, indent=2, sort_keys=True)
    if args.write:
        with open(args.write, "w", encoding="utf-8") as handle:
            handle.write(text + "\n")
        print(f"wrote {args.write} sha256={payload['payload_sha256']}")
    else:
        print(text)


if __name__ == "__main__":
    main()
