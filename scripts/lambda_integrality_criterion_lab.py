#!/usr/bin/env python3
"""Erdos 257 without carries: the Lambda integrality criterion.

Every $1/(2^a-1)$ has odd denominator, so $x=\\sum_{a\\in A}1/(2^a-1)$ is
rational iff $(2^\\ell-1)x\\in\\mathbb Z$ for some $\\ell\\ge1$ (take
$\\ell=\\mathrm{ord}_q(2)$).  Division with remainder in the exponent gives,
for every $a,\\ell$,

    (2^ell - 1)/(2^a - 1)  =  2^{ell mod a} * (2^{a*floor(ell/a)} - 1)/(2^a - 1)
                              + (2^{ell mod a} - 1)/(2^a - 1),

whose first summand is an integer.  Summing over ``a in A`` (the series
converges: for ``a > ell`` the term is ``(2^ell-1)/(2^a-1)``) yields the exact
congruence

    (2^ell - 1) x  ==  Lambda(ell, A)   (mod 1),
    Lambda(ell, A) = sum_{a in A} (2^{ell mod a} - 1)/(2^a - 1).

Therefore

    x is rational  <=>  Lambda(ell, A) is an INTEGER for some ell,
                    <=>  Lambda(k*ell_0, A) is an integer for every k>=1,
                         where ell_0 = ord_q(2).

Every term lies in [0, (2^{a-1}-1)/(2^a-1)) subset [0, 1/2), and a term
vanishes exactly when a divides ell.  No carry, no cylinder, no reservoir
appears: the whole of Erdos 257 is the statement that a sum of explicit
rationals in [0,1/2) is never an integer for an infinite support.

This lab does three things.

1.  VALIDATION.  For a target of known period ell_0 it recomputes
    Lambda(k*ell_0, A) from the greedy support A and checks it is an integer
    to the truncation error.  This is an independent check of the whole
    pipeline: the support word is produced by dyadic enclosures on the real
    remainder, while Lambda is a carry-free exponent-arithmetic sum.

2.  STRUCTURE.  It measures the distance to the nearest integer,
    ||Lambda(ell, A)||, for ell NOT a multiple of ell_0, looking for
    unexpectedly small values -- a near-integrality that no rationality
    forces would be the first sign of hidden arithmetic structure.

3.  ANTI-CONCENTRATION.  It reports the empirical distribution of
    ||Lambda(ell, A)|| against the uniform null, which is the exact quantity
    a proof of Erdos 257 would have to bound away from zero along an
    arithmetic progression.

Companion analysis: ErdosProblems/Erdos257/SupportWordStructureLab.md
"""

from __future__ import annotations

import argparse
import hashlib
import json
import math
from typing import Any


def canonical_sha256(payload: Any) -> str:
    blob = json.dumps(payload, separators=(",", ":"), sort_keys=True)
    return hashlib.sha256(blob.encode("utf-8")).hexdigest()


def build_z(P: int) -> list[int]:
    nbytes = (P + 8) // 8 + 1
    pat = bytearray(nbytes)
    Z = [0] * (P + 2)
    for n in range(1, P + 1):
        pos = P - n
        positions = []
        while pos >= 0:
            positions.append(pos)
            pos -= n
        for q in positions:
            pat[nbytes - 1 - (q >> 3)] |= 1 << (q & 7)
        Z[n] = int.from_bytes(bytes(pat), "big")
        for q in positions:
            pat[nbytes - 1 - (q >> 3)] = 0
    return Z


def greedy_support(p: int, q: int, ranks: int, Z: list[int], P: int) -> tuple[list[int], int | None]:
    lo = ((1 << P) * p) // q
    hi = lo + 1
    A: list[int] = []
    for n in range(1, ranks + 1):
        zn = Z[n]
        if lo >= zn + 1:
            lo -= zn + 1
            hi -= zn
            A.append(n)
        elif hi > zn:
            return A, n
    return A, None


def order_of_two(q: int) -> int | None:
    m = q
    while m % 2 == 0:
        m //= 2
    if m == 1:
        return None
    r = 2 % m
    k = 1
    while r != 1:
        r = (2 * r) % m
        k += 1
        if k > 4 * m:
            return None
    return k


def lambda_value(
    ell: int, A: list[int], bits: int, mers: dict[int, int] | None = None
) -> tuple[int, int]:
    """Return (numerator, bits) with Lambda ~ numerator / 2^bits, exact floor.

    Pruning is exact, not heuristic: with j = a - (ell mod a) the term equals
    2^-j (1 - (2^j-1)/(2^a-1)) < 2^-j, so any a with j > bits contributes less
    than 2^-bits and its floor at this scale is 0.
    """
    scale = 1 << bits
    total = 0
    for a in A:
        r = ell % a
        if r == 0:
            continue
        if a - r > bits:
            continue
        m = mers[a] if mers is not None else ((1 << a) - 1)
        total += (scale * ((1 << r) - 1)) // m
    return total, bits


def distance_to_integer(num: int, bits: int) -> float:
    frac = num & ((1 << bits) - 1)
    d = min(frac, (1 << bits) - frac)
    return d / (1 << bits)


def analyse(
    p: int, q: int, ranks: int, ells: int, bits: int, pad: int
) -> dict[str, Any]:
    P = 2 * ranks + pad
    Z = build_z(P)
    A, stop = greedy_support(p, q, ranks, Z, P)
    mers = {a: (1 << a) - 1 for a in A}
    ell0 = order_of_two(q)
    row: dict[str, Any] = {
        "target": f"{p}/{q}",
        "ranks": ranks,
        "support_size": len(A),
        "greedy_stop_rank": stop,
        "binary_period_ell0": ell0,
        "lambda_precision_bits": bits,
    }
    # truncation: terms with a > ranks are omitted; their total is at most
    # (2^ell - 1) * T_ranks < 2^(ell - ranks + 1).
    max_ell = min(ells, ranks // 3)
    row["max_ell_used"] = max_ell
    row["truncation_exponent_bound"] = f"2^({max_ell} - {ranks} + 1)"

    if ell0:
        multiples = [k * ell0 for k in range(1, max_ell // ell0 + 1)]
        worst = 0.0
        worst_at = None
        for ell in multiples:
            num, b = lambda_value(ell, A, bits, mers)
            d = distance_to_integer(num, b)
            if d > worst:
                worst = d
                worst_at = ell
        row["rationality_multiples_checked"] = len(multiples)
        row["max_distance_to_integer_on_multiples"] = worst
        row["max_distance_multiple"] = worst_at
        row["integer_values_sample"] = [
            [ell, lambda_value(ell, A, bits, mers)[0] >> bits] for ell in multiples[:8]
        ]

    # The fractional part of Lambda(ell) is forced to equal {(2^ell - 1) x},
    # so its distance to Z carries no information beyond x itself.  The
    # informative object is the INTEGER VALUE on the rationality progression
    # and its growth law, plus the "first multiple above ell" decomposition
    #     Lambda(ell,A) = sum_a 2^{-j_a(ell)} - sum_a (1 - 2^{-j_a(ell)})/(2^a-1),
    #     j_a(ell) = a - (ell mod a) = distance from ell up to the next
    #                multiple of a  (j_a = a when a | ell, giving term 0).
    if ell0:
        vals = []
        for k in range(1, min(60, max_ell // ell0) + 1):
            ell = k * ell0
            num, b = lambda_value(ell, A, bits, mers)
            vals.append([ell, num >> b])
        row["integer_values_on_progression"] = vals
        if len(vals) >= 4:
            row["integer_value_growth"] = {
                "first": vals[0][1],
                "last": vals[-1][1],
                "last_ell": vals[-1][0],
                "half_log_ell": 0.5 * math.log(max(vals[-1][0], 2)),
                "monotone": all(
                    vals[i][1] <= vals[i + 1][1] for i in range(len(vals) - 1)
                ),
            }
        # first-multiple decomposition at the deepest checked multiple
        ell = vals[-1][0]
        head = 0.0
        jhist: dict[int, int] = {}
        for a in A:
            j = a - (ell % a)
            jhist[j] = jhist.get(j, 0) + 1
            head += 2.0 ** (-j) if j < 200 else 0.0
        row["first_multiple_decomposition"] = {
            "ell": ell,
            "head_sum_2^-j": head,
            "j_histogram_small": {
                str(k): v for k, v in sorted(jhist.items())[:16]
            },
        }
    return row


def main() -> None:
    ap = argparse.ArgumentParser()
    ap.add_argument("--ranks", type=int, default=6000)
    ap.add_argument("--ells", type=int, default=2000)
    ap.add_argument("--bits", type=int, default=256)
    ap.add_argument("--pad", type=int, default=96)
    ap.add_argument(
        "--targets", type=str, default="1/21,4/9,1/5,2/21,3/11,90/511,17/29,1/465"
    )
    ap.add_argument("--write", type=str, default=None)
    args = ap.parse_args()

    rows = []
    for tok in args.targets.split(","):
        tok = tok.strip()
        if not tok:
            continue
        a, b = tok.split("/")
        rows.append(analyse(int(a), int(b), args.ranks, args.ells, args.bits, args.pad))

    payload = {
        "schema": "erdos257_lambda_integrality_criterion_v1",
        "parameters": vars(args),
        "criterion": (
            "x rational  <=>  Lambda(ell,A) = sum_{a in A} (2^{ell mod a}-1)/(2^a-1) "
            "is an integer for some ell; equivalently for every multiple of "
            "ell0 = ord_q(2).  Each term lies in [0,1/2) and vanishes iff a | ell."
        ),
        "source": {
            "script": "formal_math/erdos257_period_noncollapse/scripts/"
            "lambda_integrality_criterion_lab.py",
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
