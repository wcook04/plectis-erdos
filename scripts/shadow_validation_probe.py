#!/usr/bin/env python3
"""Shadow-validation probe for the periodic-doubling reduction.

Hypothesis being tested (new reduction, not yet in the corpus):

At anchor rank N the greedy residual r_N is a rational with odd reduced
denominator q_N.  The idealised scaled dynamics is the doubling map on
y = 2^N r_N mod 1, whose orbit is periodic with period p = ord_{q_N}(2).
The TRUE orbit's take/skip decision at future rank N+k (take iff
2*y_k >= c_{N+k+1} ~= 1) must agree with the ideal doubling orbit except
where the ideal orbit is within ``ambiguity`` of the 1/2 boundary, where
``ambiguity(k) ~ C * 2^(k-N) * q``-scaled.  This tool:

1. computes the exact true decisions up to rank N2 by direct simulation;
2. computes the ideal periodic orbit decisions from (y_N, q_N);
3. reports the first disagreement rank and whether every disagreement is
   preceded by an ideal-orbit boundary approach inside the predicted
   ambiguity window.

A validation says the wall is equivalent to: the periodic orbit of
2^k mod q_N approaching q/2 within the ambiguity schedule never converts
into a sliver entry.
"""

from __future__ import annotations

import argparse
import json
from fractions import Fraction


def true_decisions(a: int, b: int, n2: int, slack: int = 64):
    precision = 2 * n2 + slack
    scale = 1 << precision
    lower = (scale * a) // b
    upper = (scale * a + b - 1) // b
    decisions = []
    for n in range(1, n2 + 1):
        wf = scale // ((1 << n) - 1)
        if lower >= wf + 1:
            decisions.append(1)
            lower -= wf + 1
            upper -= wf
        elif upper <= wf:
            decisions.append(0)
        else:
            raise AssertionError(f"ambiguous at {n}")
        if upper <= 0:
            break
    return decisions


def main() -> None:
    ap = argparse.ArgumentParser()
    ap.add_argument("--a", type=int, default=1)
    ap.add_argument("--b", type=int, default=21)
    ap.add_argument("--anchor", type=int, default=300)
    ap.add_argument("--horizon-extra", type=int, default=300)
    args = ap.parse_args()
    n2 = args.anchor + args.horizon_extra
    dec = true_decisions(args.a, args.b, n2)
    if len(dec) < n2:
        print(json.dumps({"status": "finite_support", "len": len(dec)}))
        return
    # residual at anchor: exact rational
    r = Fraction(args.a, args.b)
    for n in range(1, args.anchor + 1):
        w = Fraction(1, (1 << n) - 1)
        if r >= w:
            r -= w
    q = r.denominator
    assert q % 2 == 1
    num = r.numerator % q  # orbit state mod q: z_k = (2^k * num mod q) / q
    y = (1 << args.anchor) * r  # scaled residual (real, rational)
    # ideal orbit via modular arithmetic on the odd denominator q
    z_num = ((1 << args.anchor) * r.numerator) % q
    mismatches = []
    ambiguity_events = 0
    half_q = q // 2
    for k in range(0, args.horizon_extra):
        z_num = (2 * z_num) % q
        ideal = 1 if 2 * z_num >= q else 0
        truek = dec[args.anchor + k]
        dist_num = min(z_num, q - z_num)  # distance to boundary in q units
        if ideal != truek:
            mismatches.append({
                "k": k, "rank": args.anchor + k + 1,
                "ideal": ideal, "true": truek,
                "dist_over_q": dist_num / q,
            })
        if dist_num * (1 << max(0, args.anchor - k)) < q // 4:
            ambiguity_events += 1
    out = {
        "params": vars(args),
        "q_anchor_bits": q.bit_length(),
        "mismatch_count": len(mismatches),
        "first_mismatches": mismatches[:12],
        "ideal_boundary_approaches": ambiguity_events,
    }
    print(json.dumps(out, indent=1))


if __name__ == "__main__":
    main()
