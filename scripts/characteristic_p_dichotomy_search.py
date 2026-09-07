#!/usr/bin/env python3
"""Erdos 257: is characteristic two special?  Exhaustive periodic search.

In ``F_p((1/t))`` there are no carries, so

    sum_{a in A} 1/(t^a - 1) = sum_n f_A(n) t^-n,   f_A(n) = #{d | n : d in A},

and rationality over ``F_p(t)`` is exactly eventual periodicity of
``(f_A(n) mod p)``.  The characteristic-p analogue of Erdos 257 is therefore:

    does there exist an INFINITE A with (f_A(n) mod p) eventually periodic?

For ``p = 2`` the answer is yes and abundantly so: over ``F_2`` the Dirichlet
inverse of ``1`` reduces to the squarefree indicator, so ``g * mu`` lands in
``{0,1}`` for every ``g`` and every eventually periodic residue target is
realised.  The witness ``g = delta_1`` gives ``A`` = squarefree numbers and
``sum_{a squarefree} 1/(t^a-1) = 1/t``.

This script decides the question exhaustively for small periods.  Fix a
period ``P`` and a preperiod ``L``.  The first ``L + P`` membership bits are
free; thereafter periodicity of ``f_A mod p`` forces

    b_n  ==  f_A(n - P) - s_n   (mod p),      s_n = sum_{d | n, d < n} b_d,

and the branch survives only while the forced residue lies in ``{0,1}``.
Every eventually periodic residue target with those parameters is reached by
exactly one free prefix, so the enumeration is complete for (p, P, L).

A survivor whose support keeps growing to the horizon is a characteristic-p
counterexample.  A universal early death for odd p, contrasted with the
abundance at p = 2, isolates ``mu == |mu| (mod 2)`` as the whole reason the
carry-free analogue fails, and therefore shows that the obstruction in the
real problem is archimedean rather than Dirichlet-combinatorial.

Companion analysis: ErdosProblems/Erdos257/SupportWordStructureLab.md
"""

from __future__ import annotations

import argparse
import hashlib
import json
from typing import Any


def canonical_sha256(payload: Any) -> str:
    return hashlib.sha256(
        json.dumps(payload, separators=(",", ":"), sort_keys=True).encode()
    ).hexdigest()


def run_branch(
    p: int, P: int, L: int, prefix: int, horizon: int
) -> tuple[int, int, list[int]]:
    """Return (depth_reached, support_size, first_support_elements)."""
    free = L + P
    b = bytearray(horizon + 1)
    load = [0] * (horizon + 2)      # f_A(n) accumulated over d < n
    fA = [0] * (horizon + 1)
    support: list[int] = []
    for n in range(1, horizon + 1):
        if n <= free:
            bit = (prefix >> (n - 1)) & 1
        else:
            want = (fA[n - P] - load[n]) % p
            if want > 1:
                return n - 1, len(support), support[:24]
            bit = want
        b[n] = bit
        fA[n] = load[n] + bit
        if bit:
            support.append(n)
            for m in range(2 * n, horizon + 1, n):
                load[m] += 1
    return horizon, len(support), support[:24]


def search(p: int, periods: range, preperiods: range, horizon: int) -> dict[str, Any]:
    survivors: list[dict[str, Any]] = []
    deepest = {"depth": 0}
    branches = 0
    for P in periods:
        for L in preperiods:
            free = L + P
            if free > 18:
                continue
            for prefix in range(1 << free):
                branches += 1
                depth, size, head = run_branch(p, P, L, prefix, horizon)
                if depth > deepest["depth"]:
                    deepest = {
                        "depth": depth,
                        "period": P,
                        "preperiod": L,
                        "prefix_bits": bin(prefix)[2:].zfill(free)[::-1],
                        "support_size": size,
                        "support_head": head,
                    }
                if depth >= horizon and size >= max(8, horizon // 64):
                    survivors.append(
                        {
                            "period": P,
                            "preperiod": L,
                            "prefix_bits": bin(prefix)[2:].zfill(free)[::-1],
                            "support_size": size,
                            "support_head": head,
                        }
                    )
    return {
        "p": p,
        "periods": [periods.start, periods.stop - 1],
        "preperiods": [preperiods.start, preperiods.stop - 1],
        "horizon": horizon,
        "branches_enumerated": branches,
        "survivor_count": len(survivors),
        "survivors_sample": survivors[:12],
        "deepest_non_survivor_or_best": deepest,
    }


def main() -> None:
    ap = argparse.ArgumentParser()
    ap.add_argument("--primes", type=str, default="2,3,5,7,11")
    ap.add_argument("--max-period", type=int, default=6)
    ap.add_argument("--max-preperiod", type=int, default=8)
    ap.add_argument("--horizon", type=int, default=3000)
    ap.add_argument("--write", type=str, default=None)
    args = ap.parse_args()

    rows = [
        search(
            int(t),
            range(1, args.max_period + 1),
            range(1, args.max_preperiod + 1),
            args.horizon,
        )
        for t in args.primes.split(",")
        if t.strip()
    ]
    payload = {
        "schema": "erdos257_characteristic_p_dichotomy_v1",
        "parameters": vars(args),
        "question": (
            "does an infinite A exist with (f_A(n) mod p) eventually periodic? "
            "equivalently, is sum_{a in A} 1/(t^a-1) rational in F_p(t)?"
        ),
        "source": {
            "script": "formal_math/erdos257_period_noncollapse/scripts/"
            "characteristic_p_dichotomy_search.py",
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
