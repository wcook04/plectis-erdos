#!/usr/bin/env python3
"""Erdos 257 as a renormalization flow to a gapless point.

Exact identity.  For every n >= 0 and k >= 1,

    b^n * z_{n+k}  =  b^n / (b^(n+k) - 1)  =  1 / (b^k - b^-n),

so the depth-n TAIL of the base-b system, rescaled by b^n, is exactly the
neighbour family  z^(c)_k = 1/(b^k - c)  of SupportWordStructureLab section 4e
at parameter

    c = b^-n.

The problem therefore carries an exact renormalization: running the greedy
deeper is the same as flowing the family parameter c geometrically toward 0.

Why that settles the shape of the whole problem.  For z_k = 1/(b^k - c),

    z_k = b^-k + c b^-2k + O(b^-3k),
    T_k = b^-k/(b-1) + c b^-2k/(b^2-1) + O(b^-3k),
    gamma_k = z_k - T_k
            = b^-k (b-2)/(b-1)  +  c b^-2k (b^2-2)/(b^2-1)  + O(b^-3k).

The first term is INDEPENDENT of c and vanishes exactly when b = 2.  Hence:

  * b >= 3: a c-independent gap of size ~ b^-k survives the flow.  The
    renormalization cannot remove it, |C_b| = 0, and rational targets die --
    which is what the base scan measures (0 survivors out of 2868).
  * b = 2: the ENTIRE gap is carried by the flow parameter,
    gamma_k = (2c/3) 4^-k + O(8^-k), so at depth n it is (2/3) 2^-n 4^-k.
    The difficulty decays geometrically with depth, |C| = 1, and the
    conditional death rate is summable -- which is exactly the summability
    invariant of section 4g.

So the four facts recorded separately -- |C| = 1, base 2 unique, Erdos 257 the
minimal positive-gap member of its family, and a summable death rate -- are one
fact: at b = 2 the gap is purely the flow parameter, and the flow parameter is
summable.  A proof must therefore control a c -> 0 limit uniformly, and cannot
appeal to any quantity that survives the limit, because at c = 0 the
achievement set is the whole interval and the statement is false.

This script verifies the identity in exact rational arithmetic and measures
the induced gap flow against the prediction.

Companion analysis: ErdosProblems/Erdos257/SupportWordStructureLab.md
"""

from __future__ import annotations

import argparse
import hashlib
import json
from fractions import Fraction
from typing import Any


def canonical_sha256(payload: Any) -> str:
    return hashlib.sha256(
        json.dumps(payload, separators=(",", ":"), sort_keys=True).encode()
    ).hexdigest()


def verify_identity(bases: list[int], depth: int, rank: int) -> dict[str, Any]:
    failures = []
    checks = 0
    for b in bases:
        for n in range(0, depth + 1):
            for k in range(1, rank + 1):
                checks += 1
                lhs = Fraction(b**n, b ** (n + k) - 1)
                rhs = 1 / (Fraction(b**k) - Fraction(1, b**n))
                if lhs != rhs:
                    failures.append([b, n, k])
    return {
        "statement": "b^n * z_{n+k} == 1/(b^k - b^-n)",
        "bases": bases,
        "n_range": [0, depth],
        "k_range": [1, rank],
        "checks": checks,
        "failures": failures[:8],
        "exact": not failures,
    }


def gap_flow(b: int, cs: list[Fraction], depth: int, ks: list[int]) -> list[dict[str, Any]]:
    rows = []
    for c in cs:
        z = [Fraction(0)] + [1 / (Fraction(b**k) - c) for k in range(1, depth + 1)]
        T = [Fraction(0)] * (depth + 2)
        acc = Fraction(0)
        for k in range(depth, 0, -1):
            T[k] = acc
            acc += z[k]
        rows.append(
            {
                "base": b,
                "c": f"{c.numerator}/{c.denominator}",
                "c_float": float(c),
                "scaled_gap_b^(2k)_times_gamma_k": {
                    str(k): float((z[k] - T[k]) * b ** (2 * k)) for k in ks
                },
                "c_independent_leading_term_b^k_gamma_k": float(
                    Fraction(b - 2, b - 1)
                ),
                "predicted_c_term_coefficient": float(
                    c * Fraction(b**2 - 2, b**2 - 1)
                ),
                "total_sum_z": float(acc),
            }
        )
    return rows


def main() -> None:
    ap = argparse.ArgumentParser()
    ap.add_argument("--bases", type=str, default="2,3,5,10")
    ap.add_argument("--identity-depth", type=int, default=30)
    ap.add_argument("--identity-rank", type=int, default=30)
    ap.add_argument("--gap-depth", type=int, default=300)
    ap.add_argument("--write", type=str, default=None)
    args = ap.parse_args()

    bases = [int(t) for t in args.bases.split(",") if t.strip()]
    cs = [Fraction(1, 2**n) for n in (0, 1, 2, 4, 8, 12)]
    payload = {
        "schema": "erdos257_tail_renormalization_flow_v1",
        "parameters": vars(args),
        "identity": verify_identity(bases, args.identity_depth, args.identity_rank),
        "gap_flow_base_two": gap_flow(2, cs, args.gap_depth, [3, 4, 5, 6]),
        "gap_flow_base_three": gap_flow(
            3, [Fraction(1, 3**n) for n in (0, 1, 2, 4)], args.gap_depth, [3, 4, 5, 6]
        ),
        "source": {
            "script": "formal_math/erdos257_period_noncollapse/scripts/"
            "tail_renormalization_flow.py",
            "analysis": "formal_math/erdos257_period_noncollapse/ErdosProblems/"
            "Erdos257/SupportWordStructureLab.md",
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
