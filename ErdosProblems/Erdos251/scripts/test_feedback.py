#!/usr/bin/env python3
"""Exact finite checks of residue feedback. These do not prove an infinite theorem."""
from __future__ import annotations

import json
from fractions import Fraction as F
from pathlib import Path
from random import Random


def select(A: int, Q: int, C: int, w: F, lo: F, hi: F, x: F) -> int:
    """Choose a correction repairing C modulo Q and keep the next remainder bounded."""
    if Q <= 0 or A < 2 * Q or w <= 0:
        raise ValueError("Positive Q,w and A >= 2Q are required")
    if hi - lo < Q * w or not Q * w + lo <= x <= (A-Q) * w + hi:
        raise ValueError("The common continuation interval hypotheses failed")
    r = (-C) % Q
    D = (A-r)//Q
    z = x-r*w-lo
    k = min(D, z//(Q*w))
    d = r+Q*k
    assert 0 <= d <= A and (C+d) % Q == 0
    assert lo <= x-d*w <= hi
    return d


def main() -> dict[str, object]:
    counts = {"progression_extrema": 0, "common_interval_union": 0,
              "one_step_exact_targets": 0, "feedback_steps": 0,
              "feedback_prefix_telescopes": 0, "finite_schedule_overlap": 0}
    for Q in range(1, 13):
        for A in range(2*Q, 6*Q+3):
            for r in range(Q):
                D = (A-r)//Q
                assert r+Q*D <= A < r+Q*D+Q
                counts["progression_extrema"] += 1
                for w in (F(1), F(1,8), F(3,17)):
                    for extra in (F(0), F(1,19)):
                        lo, hi = F(2,13), F(2,13)+Q*w+extra
                        intervals = [(d*w+lo, d*w+hi) for d in range(r,A+1,Q)]
                        assert intervals[0][0] <= Q*w+lo
                        assert intervals[-1][1] >= (A-Q)*w+hi
                        assert all(b >= c for (_, b), (c, _) in zip(intervals, intervals[1:]))
                        counts["common_interval_union"] += 1
                        left, right = Q*w+lo, (A-Q)*w+hi
                        targets = {left, right, (left+right)/2}
                        for d in range(r,A+1,Q):
                            for x in (d*w+lo, d*w+hi):
                                if left <= x <= right:
                                    targets.add(x)
                        C = (-r) % Q
                        for x in targets:
                            select(A,Q,C,w,lo,hi,x)
                            counts["one_step_exact_targets"] += 1
    rng = Random(251006)
    # Finite continuations have an explicitly NONZERO terminal interval.
    # Truncating a filling proof to zero tail would be an invalid test.
    for trial in range(160):
        N = 18
        Qs = [2**(j//3) for j in range(N)]
        ws = [F(1,2**(3*j+1)) for j in range(N)]
        As = [64*q for q in Qs]
        lows = [F(0)]*(N+1)
        highs = [F(0)]*(N+1)
        lows[N] = Qs[-1]*ws[-1]
        highs[N] = lows[N]+2*Qs[-1]*ws[-1]
        for j in reversed(range(N)):
            assert highs[j+1]-lows[j+1] >= Qs[j]*ws[j]
            counts["finite_schedule_overlap"] += 1
            lows[j] = Qs[j]*ws[j]+lows[j+1]
            highs[j] = (As[j]-Qs[j])*ws[j]+highs[j+1]
        q = F(rng.randrange(10001),10000)
        if trial == 0: q = F(0)
        if trial == 1: q = F(1)
        y = lows[0]+q*(highs[0]-lows[0])
        x,C,total = y,0,F(0)
        previous_modulus = 1
        for j in range(N):
            assert C % previous_modulus == 0
            d = select(As[j],Qs[j],C,ws[j],lows[j+1],highs[j+1],x)
            assert d % previous_modulus == 0
            C += d; total += d*ws[j]; x -= d*ws[j]
            assert C % Qs[j] == 0
            assert total == y-x
            assert lows[j+1] <= x <= highs[j+1]
            previous_modulus = Qs[j]
            counts["feedback_steps"] += 1
            counts["feedback_prefix_telescopes"] += 1
    receipt = {"status":"passed", "arithmetic":"integers and fractions.Fraction",
               "random_seed":251006, "counts":counts,
               "boundary":"Finite selector/overlap/congruence/telescope tests only; no prime data, Lean run, asymptotic verification or infinite theorem check."}
    out = Path(__file__).with_name("receipt.json")
    out.write_text(json.dumps(receipt,indent=2)+"\n")
    return receipt

if __name__ == "__main__":
    print(json.dumps(main(),indent=2))
