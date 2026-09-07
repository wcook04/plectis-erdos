#!/usr/bin/env python3
"""Erdos 257: is characteristic two special, and are any rational targets anomalous?

Two probes that test the same question from opposite sides: how much of the
obstruction lives in the divisor (Dirichlet) layer and how much in the
archimedean carry.

Probe A --- the characteristic-p analogue.
    In ``F_p((1/t))`` there are no carries, so

        sum_{a in A} 1/(t^a - 1) = sum_n f_A(n) t^-n,  f_A(n) = #{d | n : d in A},

    and rationality over ``F_p(t)`` is exactly eventual periodicity of
    ``f_A(n) mod p``.  Over ``F_2`` the Dirichlet inverse of ``1`` is ``mu``,
    which reduces to the squarefree indicator, so ``g * mu`` automatically
    lands in ``{0,1}`` for EVERY g and the analogue is false with an infinite
    family (witness ``g = delta_1``, ``A`` = squarefree, value ``1/t``).
    For odd ``p`` the values of ``g * mu`` spread over ``F_p`` and landing in
    ``{0,1}`` at every rank is a real constraint.  This probe searches
    eventually periodic residue targets and reports the deepest survivor.
    A survivor to the horizon with infinite support would extend the
    characteristic-two counterexample family to odd p; a short universal
    death shows characteristic two is a parity degeneracy and isolates
    ``mu = |mu| mod 2`` as the whole reason.

Probe B --- the run anomaly hunt.
    By the run law of SupportWordStructureLab.md section 3, the target dies
    at rank ``m`` exactly when the greedy word has an INFINITE run of
    selected ranks from ``m+1``, and a finite run of length ``L`` there
    certifies survival margin ``delta_m`` in ``(T_{m+L+1}, T_{m+L}]``.  So the
    maximal take-run below ``N`` is a single integer recording the closest
    approach to death, and under the null model (Bernoulli 1/2 word) it is
    ``log2 N + O(1)``.  This probe scans many rational targets for
    ``max_take_run - log2 N`` well above the Gumbel fluctuation, which would
    be the first visible arithmetic signal in this problem.

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
    blob = json.dumps(payload, separators=(",", ":"), sort_keys=True)
    return hashlib.sha256(blob.encode("utf-8")).hexdigest()


# ------------------------------------------------------- probe A: char p


def mobius_table(n: int) -> list[int]:
    mu = [1] * (n + 1)
    primes = []
    is_comp = bytearray(n + 1)
    for i in range(2, n + 1):
        if not is_comp[i]:
            primes.append(i)
            mu[i] = -1
        for p in primes:
            if i * p > n:
                break
            is_comp[i * p] = 1
            if i % p == 0:
                mu[i * p] = 0
                break
            mu[i * p] = -mu[i]
    return mu


def char_p_search(p: int, max_period: int, horizon: int) -> dict[str, Any]:
    """Force f_A(n) = g(n mod P) (mod p) and see how far 1_A stays Boolean."""
    best = {"depth": 0, "period": None, "pattern": None, "support": 0}
    survivors = []
    for P in range(1, max_period + 1):
        for code in range(p**P):
            g = []
            c = code
            for _ in range(P):
                g.append(c % p)
                c //= p
            load = [0] * (horizon + 2)
            support = 0
            depth = 0
            ok = True
            for n in range(1, horizon + 1):
                want = (g[n % P] - load[n]) % p
                if want > 1:
                    ok = False
                    break
                if want:
                    support += 1
                    for m in range(n, horizon + 1, n):
                        load[m] += 1
                depth = n
            if depth > best["depth"]:
                best = {
                    "depth": depth,
                    "period": P,
                    "pattern": g,
                    "support": support,
                }
            if ok and support > 3:
                survivors.append({"period": P, "pattern": g, "support": support})
    return {
        "p": p,
        "max_period": max_period,
        "horizon": horizon,
        "deepest": best,
        "full_horizon_survivors": survivors[:20],
        "full_horizon_survivor_count": len(survivors),
    }


def char_two_witness(horizon: int) -> dict[str, Any]:
    """A = squarefree gives f_A(n) = 2^omega(n), even for every n >= 2."""
    omega = [0] * (horizon + 1)
    for q in range(2, horizon + 1):
        if omega[q] == 0:
            for m in range(q, horizon + 1, q):
                omega[m] += 1
    odd = [n for n in range(2, horizon + 1) if omega[n] == 0]
    sqfree = bytearray([1]) * (horizon + 1)
    i = 2
    while i * i <= horizon:
        for m in range(i * i, horizon + 1, i * i):
            sqfree[m] = 0
        i += 1
    return {
        "horizon": horizon,
        "ranks_with_odd_divisor_count": odd[:8],
        "odd_count_beyond_one": len(odd),
        "support_size": int(sum(sqfree[1:])),
        "value_in_F2_of_t": "1/t",
        "identity": "sum_{a squarefree} 1/(t^a-1) = t^-1 in F_2((1/t))",
    }


# --------------------------------------------------- probe B: run anomaly


def build_z(P: int) -> list[int]:
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
    return Z


def greedy_runs(p: int, q: int, ranks: int, P: int, Z: list[int]) -> dict[str, Any]:
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
                best = cur
                best_at = start
        elif hi > zn:
            return {"undecided": n}
        else:
            cur = 0
    return {
        "max_take_run": best,
        "max_take_run_start": best_at,
        "selected": selected,
        "density": selected / ranks,
    }


def run_anomaly_scan(
    denominators: list[int], ranks: int, pad: int, limit_per_q: int
) -> dict[str, Any]:
    P = 2 * ranks + pad
    Z = build_z(P)
    E_lo = sum(Z[1 : P + 1])
    rows = []
    worst = {"excess": -99.0}
    hist: dict[int, int] = {}
    scanned = 0
    for q in denominators:
        pmax = min((E_lo * q) // (1 << P), limit_per_q)
        runs = []
        for pnum in range(1, pmax + 1):
            out = greedy_runs(pnum, q, ranks, P, Z)
            if "undecided" in out:
                continue
            scanned += 1
            r = out["max_take_run"]
            hist[r] = hist.get(r, 0) + 1
            runs.append(r)
            excess = r - math.log2(ranks)
            if excess > worst["excess"]:
                worst = {
                    "excess": excess,
                    "target": f"{pnum}/{q}",
                    "max_take_run": r,
                    "start": out["max_take_run_start"],
                    "density": out["density"],
                }
        if runs:
            rows.append(
                {
                    "q": q,
                    "scanned": len(runs),
                    "mean_max_take_run": sum(runs) / len(runs),
                    "max_max_take_run": max(runs),
                }
            )
    return {
        "ranks": ranks,
        "log2_ranks": math.log2(ranks),
        "scanned_targets": scanned,
        "max_take_run_histogram": {str(k): v for k, v in sorted(hist.items())},
        "most_anomalous": worst,
        "rows": rows,
    }


def main() -> None:
    ap = argparse.ArgumentParser()
    ap.add_argument("--char-primes", type=str, default="3,5,7")
    ap.add_argument("--char-max-period", type=int, default=6)
    ap.add_argument("--char-horizon", type=int, default=600)
    ap.add_argument("--char-two-horizon", type=int, default=200000)
    ap.add_argument("--run-ranks", type=int, default=3000)
    ap.add_argument("--run-pad", type=int, default=96)
    ap.add_argument("--run-denominators", type=str, default="97,211,509,1021,2053")
    ap.add_argument("--run-limit-per-q", type=int, default=400)
    ap.add_argument("--write", type=str, default=None)
    args = ap.parse_args()

    char_rows = [
        char_p_search(int(t), args.char_max_period, args.char_horizon)
        for t in args.char_primes.split(",")
        if t.strip()
    ]
    payload = {
        "schema": "erdos257_characteristic_analogue_and_run_anomaly_v1",
        "parameters": vars(args),
        "source": {
            "script": "formal_math/erdos257_period_noncollapse/scripts/"
            "characteristic_analogue_and_run_anomaly_lab.py",
            "analysis": "formal_math/erdos257_period_noncollapse/ErdosProblems/"
            "Erdos257/SupportWordStructureLab.md",
        },
        "characteristic_two_witness": char_two_witness(args.char_two_horizon),
        "characteristic_odd_search": char_rows,
        "run_anomaly": run_anomaly_scan(
            [int(t) for t in args.run_denominators.split(",") if t.strip()],
            args.run_ranks,
            args.run_pad,
            args.run_limit_per_q,
        ),
    }
    payload["payload_sha256"] = canonical_sha256(payload)
    text = json.dumps(payload, indent=2, sort_keys=True, default=str)
    if args.write:
        with open(args.write, "w", encoding="utf-8") as handle:
            handle.write(text + "\n")
        print(f"wrote {args.write} sha256={payload['payload_sha256']}")
    else:
        print(text)


if __name__ == "__main__":
    main()
