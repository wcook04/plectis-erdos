#!/usr/bin/env python3
"""Erdos 257 sits at the minimal positive gap of its own family.

For a decreasing summable ``z_n`` with tails ``T_n = sum_{k>n} z_k``, the set
of subsums ``{ sum_{a in A} z_a }`` is

  * the full interval ``[0, sum z]``            if ``z_n <= T_n`` for every n,
  * a Cantor set with a gap of width ``z_n - T_n`` at each rank otherwise.

Take the one-parameter neighbour family ``z_n^(c) = 1/(2^n - c)``.  Expanding,

    z_n^(c) = 2^-n + c 4^-n + O(8^-n),
    T_n^(c) = 2^-n + (c/3) 4^-n + O(8^-n),
    gamma_n = z_n - T_n = (2c/3) 4^-n + O(8^-n).

So the sign of the gap is the sign of ``c``, and its scale is always
``4^-n`` against bridges of size ``2^-n``:

    c = -1   z_n = 1/(2^n + 1)   gamma_n = -(2/3) 4^-n   NO gaps  -> interval
    c =  0   z_n = 2^-n          gamma_n = 0             NO gaps  -> [0,1]
    c = +1   z_n = 1/(2^n - 1)   gamma_n = +(2/3) 4^-n   gaps     -> Erdos 257

For ``c <= 0`` the analogue of Erdos 257 is FALSE, and constructively so:
every value in the interval is achieved, while every FINITE subsum of
``1/(2^a + 1)`` has odd denominator (each ``2^a + 1`` is odd).  Hence

    x = 1/2  is achieved and cannot be a finite subsum,
    so its support is infinite and  sum_{a in A} 1/(2^a + 1) = 1/2  exactly.

The same denominator remark applies to Erdos 257 itself and removes a side
condition: every finite subsum of ``1/(2^a - 1)`` has odd denominator, so a
target with EVEN denominator that survives the forced greedy is automatically
a counterexample -- no separate argument that the support is infinite is
needed.  The census already carries such targets (q = 512, 1024, 2048, 4096).

This lab verifies the gap signs in exact rational arithmetic, runs the forced
greedy for c <= 0 to exhibit the explicit infinite support of 1/2, and
records the even-denominator sharpening.

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


def gap_signs(c: int, levels: int, depth: int) -> dict[str, Any]:
    """Exact z_n vs T_n.  Truncating the tail at `depth` makes the comparison
    meaningful only while |gamma_n| ~ 4^-n dominates the omitted 2^-depth, i.e.
    for 2n < depth; the reliable range is reported explicitly."""
    # first rank with 2^n - c > 0
    start = 1
    while 2**start - c <= 0:
        start += 1
    z = [Fraction(0)] * (depth + 1)
    for n in range(start, depth + 1):
        z[n] = Fraction(1, 2**n - c)
    T = [Fraction(0)] * (depth + 2)
    acc = Fraction(0)
    for n in range(depth, start - 1, -1):
        T[n] = acc
        acc += z[n]
    # Certified enclosure of the true tail.  T[n] omits sum_{k>depth} z_k;
    # for 2^(depth-1) >= |c| that omitted mass is at most 2^(1-depth).  A gap
    # is certified only when z_n exceeds the UPPER enclosure of T_n, and its
    # absence only when z_n is at most the lower enclosure.  Without this the
    # exactly-critical case c = 0 (where z_n = T_n identically) reports a
    # spurious gap at every rank.
    tail_bound = Fraction(1, 2 ** (depth - 1))
    reliable = depth // 2 - 4
    gaps = [n for n in range(start, reliable + 1) if z[n] > T[n] + tail_bound]
    no_gaps = [n for n in range(start, reliable + 1) if z[n] <= T[n]]
    undecided = reliable - start + 1 - len(gaps) - len(no_gaps)
    scaled = [
        float((z[n] - T[n]) * 4**n)
        for n in range(max(start + 1, 2), min(levels + start, reliable) + 1)
    ]
    return {
        "c": c,
        "first_rank": start,
        "sequence": f"1/(2^n - {c})" if c else "2^-n",
        "total": float(acc),
        "reliable_range": reliable,
        "ranks_with_a_certified_gap": gaps[:8],
        "certified_gap_count": len(gaps),
        "certified_no_gap_count": len(no_gaps),
        "undecided_ranks": undecided,
        "tail_enclosure_bound": "2^(1-depth)",
        "scaled_gap_4^n_times_(z_n - T_n)": [round(v, 6) for v in scaled[:10]],
        "predicted_limit_2c_over_3": 2 * c / 3,
        "structure": (
            "cantor_set_with_gaps"
            if gaps
            else ("full_interval" if undecided == 0 else "undecided")
        ),
        "analogue_of_erdos257": (
            "OPEN" if gaps else ("FALSE" if undecided == 0 else "UNDECIDED")
        ),
    }


def greedy_support(c: int, p: int, q: int, depth: int, prec: int) -> dict[str, Any]:
    """Forced greedy for z_n = 1/(2^n - c) on x = p/q, exact enclosures."""
    scale = 1 << prec
    lo = (scale * p) // q
    hi = lo + 1
    support: list[int] = []
    start = 1
    while 2**start - c <= 0:
        start += 1
    for n in range(start, depth + 1):
        d = 2**n - c
        zlo = scale // d
        if lo >= zlo + 1:
            lo -= zlo + 1
            hi -= zlo
            support.append(n)
        elif hi > zlo:
            return {"status": "undecided", "rank": n, "support": support[:24]}
    return {
        "status": "ran_to_depth",
        "depth": depth,
        "support_size": len(support),
        "support_head": support[:24],
        "largest_selected": support[-1] if support else None,
        "selected_beyond_half_depth": sum(1 for a in support if a > depth // 2),
    }


def main() -> None:
    ap = argparse.ArgumentParser()
    ap.add_argument("--cs", type=str, default="-2,-1,0,1,2")
    ap.add_argument("--levels", type=int, default=10)
    ap.add_argument("--depth", type=int, default=600)
    ap.add_argument("--greedy-depth", type=int, default=2000)
    ap.add_argument("--greedy-prec", type=int, default=4200)
    ap.add_argument("--write", type=str, default=None)
    args = ap.parse_args()

    rows = []
    for tok in args.cs.split(","):
        c = int(tok)
        row = gap_signs(c, args.levels, args.depth)
        if row["structure"] == "full_interval":
            row["explicit_counterexample_x_equals_one_half"] = greedy_support(
                c, 1, 2, args.greedy_depth, args.greedy_prec
            )
            row["why_infinite_support"] = (
                "every finite subsum of 1/(2^a - c) with c odd has odd "
                "denominator, so x = 1/2 cannot be one"
                if c % 2
                else "c even: 2^a - c is even, so the parity argument does "
                "not apply and only the interval property is used"
            )
        rows.append(row)

    payload = {
        "schema": "erdos257_neighbour_family_gap_sign_v1",
        "parameters": vars(args),
        "source": {
            "script": "formal_math/erdos257_period_noncollapse/scripts/"
            "neighbour_family_gap_sign_lab.py",
            "analysis": "formal_math/erdos257_period_noncollapse/ErdosProblems/"
            "Erdos257/SupportWordStructureLab.md",
        },
        "even_denominator_sharpening": (
            "Every finite subsum of 1/(2^a - 1) has odd denominator. Hence any "
            "target with even denominator that survives the forced greedy is a "
            "counterexample outright: no separate infinitude argument is needed."
        ),
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
