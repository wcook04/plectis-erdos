#!/usr/bin/env python3
r"""
Erdos 257, 4/9 diagonal -- is the required residue-certificate suffix excess BOUNDED?

FourNinthsDiagonalMarginInvariant.md closes with an explicit unexecuted directive:
"Any next computation should discriminate arithmetic descriptions of those overshoots,
not merely extend the trajectory horizon."  This is that computation.

THE OPEN QUESTION IT DECIDES
----------------------------
The surviving 4/9 socket is the selected-landing rank producer

    b_d = 1  ==>  d <= rho_d.                                              (3)

The history identity rho_d = sum_{0<=j<d} 4^(d-1-j) q_j means rho_d mod 4^k depends only
on the last k increments, so the residue certificate

    rho_d mod 4^k >= d                                                     (RC)

would certify (3).  The existing audit falsifies the least natural k (least k with
4^k > d) at selected rank 20, and records that the ADDITIONAL base-four digits needed
reach 14 by rank 146803.  The note's own claim boundary states the gap precisely: these
"neither prove that the required suffix excess is unbounded nor rule out a genuinely
nonlocal use of (5)".

Deciding boundedness decides the route:

 * excess BOUNDED  -> a fixed-suffix residue certificate is viable and (3) becomes
   attackable by a bounded-suffix argument.  That is a genuine positive.
 * excess UNBOUNDED -> no fixed-suffix certificate can work, the route dies for a
   STRUCTURAL reason rather than a horizon limit, and any continuation must use (5)
   nonlocally, as the note anticipates.

PREDICTION, DECLARED BEFORE THE RUN
-----------------------------------
Model rho_d mod 4^k as equidistributed.  Then P[rho_d mod 4^k < d] ~ d/4^k, and writing
k = base_k + e with base_k the least k such that 4^k > d, the failure probability per
selected rank is ~4^-e -- a CONSTANT independent of d.  Over a dyadic band of ~2^i ranks
the largest excess needed is therefore ~log_4(2^i) = i/2.

  P1  max excess over the dyadic band [2^i, 2^(i+1)) grows LINEARLY in the band index i
      with slope ~0.5, i.e. the required suffix excess is UNBOUNDED.
  P2  the fitted slope over the measured bands lies in [0.3, 0.8].
  P3  the base certificate (e = 0) fails, first at selected rank 20 with rho_20 mod 64
      = 12 -- reproducing the existing audit as a calibrator in the same run.

FALSIFIER
---------
A max-excess column that PLATEAUS across bands refutes P1/P2 and reopens the fixed-suffix
route.  Failure to reproduce P3 is an instrument error and voids the run.

    ./repo-python formal_math/erdos257_period_noncollapse/scripts/four_ninths_residue_excess_growth.py [horizon]
"""
from __future__ import annotations
import json, math, sys
from array import array
from math import gcd

problem_id = "erdos_257"
HORIZON = int(sys.argv[1]) if len(sys.argv) > 1 else 120000

def pair_pulse(rank: int) -> int:
    return 0 if rank % 3 == 0 else (1 if rank % 3 == 1 else 3)

def schedule_selected_rank(loads: array, rank: int, horizon: int) -> None:
    period = rank // gcd(rank, 2)
    start = (rank // period + 1) * period
    for future in range(start, horizon + 1, period):
        loads[future] += 1
    if rank % 2 == 1:
        start = (3 * rank + 1) // 2
        for future in range(start, horizon + 1, rank):
            loads[future] += 2

def main() -> None:
    H = HORIZON
    loads = array("I", [0]) * (H + 2)
    rho = 0
    prefix = []
    rho_12 = None
    base_fail = None
    bands: dict[int, int] = {}
    band_examples: dict[int, tuple] = {}
    selected = 0
    violations = 0
    for rank in range(1, H + 1):
        transition = 4 * rho + pair_pulse(rank) - int(loads[rank])
        coin = (1 << rank) + 1
        take = coin <= transition
        rho = transition - coin if take else transition
        if rank <= 12:
            prefix.append("1" if take else "0")
            if rank == 12:
                rho_12 = rho
        if not take:
            continue
        selected += 1
        if rho < rank:
            violations += 1
        # least k with 4^k > rank
        base_k = 1
        while (1 << (2 * base_k)) <= rank:
            base_k += 1
        # least k with rho mod 4^k >= rank
        k = base_k
        while (rho % (1 << (2 * k))) < rank:
            k += 1
        excess = k - base_k
        if excess > 0 and base_fail is None:
            base_fail = {"rank": rank, "base_k": base_k,
                         "rho_mod_base": rho % (1 << (2 * base_k)), "excess": excess}
        b = rank.bit_length()
        if excess > bands.get(b, -1):
            bands[b] = excess
            band_examples[b] = (rank, base_k, k)
        schedule_selected_rank(loads, rank, H)

    calib = "".join(prefix) == "010110110001" and rho_12 == 2460
    print(f"horizon {H}   selected {selected}   landing-rank violations {violations}")
    print(f"CALIBRATOR bit prefix 010110110001 and rho_12=2460 reproduced: {calib}")
    print(f"CALIBRATOR first base-certificate failure: {base_fail}")
    print()
    print(f"{'band i':>7} {'ranks':>12} {'max excess':>11} {'at rank':>9} {'base_k':>7} {'k':>4}")
    xs, ys = [], []
    for b in sorted(bands):
        if b < 6:
            continue
        r, bk, k = band_examples[b]
        print(f"{b:>7} [2^{b-1},2^{b}) {bands[b]:>11} {r:>9} {bk:>7} {k:>4}")
        xs.append(b); ys.append(bands[b])
    slope = None
    if len(xs) >= 3:
        n = len(xs); mx = sum(xs)/n; my = sum(ys)/n
        den = sum((x-mx)**2 for x in xs)
        slope = sum((x-mx)*(y-my) for x, y in zip(xs, ys))/den if den else None
        print(f"\nfitted slope of max excess vs band index: {slope:.4f}   (P1/P2 predict ~0.5)")
    out = {"schema": "aiw-formal-math-receipt/1", "problem_id": problem_id,
           "probe": "four_ninths_residue_excess_growth", "horizon": H,
           "selected_ranks": selected, "landing_rank_violations": violations,
           "calibrator_prefix_and_rho12": bool(calib),
           "calibrator_first_base_failure": base_fail,
           "max_excess_by_band": {str(k_): v for k_, v in sorted(bands.items())},
           "band_examples": {str(k_): list(v) for k_, v in sorted(band_examples.items())},
           "fitted_slope": slope,
           "verdict": (
               "Decides whether the residue-certificate suffix excess for the 4/9 selected-"
               "landing rank producer is bounded. A slope near 0.5 means the excess grows "
               "like log_4 of the horizon, so NO fixed-suffix residue certificate can work "
               "and the route dies structurally rather than by horizon; a plateau would "
               "reopen the fixed-suffix route. Finite evidence only; no claim on Erdos 257.")}
    dest = "state/formal_math/erdos257_period_noncollapse/four_ninths_residue_excess_growth_receipt.json"
    with open("public-source-redacted://ai_workflow" + dest, "w") as fh:
        json.dump(out, fh, indent=2, sort_keys=True); fh.write("\n")
    print(f"receipt: {dest}")

if __name__ == "__main__":
    main()
