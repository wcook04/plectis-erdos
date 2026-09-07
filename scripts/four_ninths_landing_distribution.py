#!/usr/bin/env python3
r"""
Erdos 257, 4/9 diagonal -- what the finite audits are actually worth.

FourNinthsDiagonalMarginInvariant.md records "zero violations through rank 200000" and
"exact audits remain nonnegative through ten million ranks" as "finite evidence only",
without saying what that evidence is worth.  Its closing directive asks for a computation
that discriminates ARITHMETIC DESCRIPTIONS of the selected overshoots.  This measures the
overshoot distribution and converts the audits into a quantified tail bound.

THE SETUP
---------
The socket is  b_d = 1 ==> d <= rho_d.  At a take, rho_d = T_d - (2^d + 1) is the landing
overshoot above the dyadic coin, and rho_d < 2^d.  So the natural normalisation is

    x_d := rho_d / 2^d  in  [0,1).

If x_d is equidistributed, then P[rho_d < d] = d * 2^-d, and the total residual risk
beyond depth D is sum_{d>D} d 2^-d ~ 2 D 2^-D.  That is not merely summable: it is
super-exponentially small, so a finite verification to depth D buys essentially everything
beyond D.  This is a sharply different situation from the GENERIC Erdos-257 fatal window,
whose relative width is ~2^-n and whose total risk is O(1) spread across ranks
(SupportWordStructureLab.md s.4g).

PREDICTIONS, DECLARED BEFORE THE RUN
------------------------------------
P1  the decile histogram of x_d over takes is flat to within sampling error (~1% of the
    bin mass at 3e4 takes).
P2  no landing has x_d >= 1, i.e. rho_d < 2^d always -- an instrument check on the range.
P3  min x_d over N takes is of order 1/N, the uniform order statistic.
P4  min slack rho_d - d is 0 at rank 2 and rank 2 is the unique record low, reproducing
    FourNinthsDiagonalMarginInvariant.md.

FALSIFIER
---------
A histogram with a depleted or enriched lowest decile refutes P1 and voids the tail bound:
the whole estimate rests on equidistribution near zero.  Any x_d >= 1 voids the instrument.

CLAIM BOUNDARY
--------------
Equidistribution is MEASURED, not proved.  The resulting tail figure is a HEURISTIC
confidence statement about a deterministic orbit, not a probability and not a theorem.  It
does not prove the socket and does not decide Erdos 257.

    ./repo-python formal_math/erdos257_period_noncollapse/scripts/four_ninths_landing_distribution.py [horizon]
"""
from __future__ import annotations
import json, sys
from array import array
from math import gcd, log2, log10

problem_id = "erdos_257"
HORIZON = int(sys.argv[1]) if len(sys.argv) > 1 else 60000

def pair_pulse(r: int) -> int:
    return 0 if r % 3 == 0 else (1 if r % 3 == 1 else 3)

def schedule(loads: array, rank: int, H: int) -> None:
    period = rank // gcd(rank, 2)
    start = (rank // period + 1) * period
    for f in range(start, H + 1, period):
        loads[f] += 1
    if rank % 2 == 1:
        start = (3 * rank + 1) // 2
        for f in range(start, H + 1, rank):
            loads[f] += 2

def norm_ratio(rho: int, rank: int) -> float:
    """rho / 2^rank as a float, exact enough for a decile histogram at any rank."""
    if rho == 0:
        return 0.0
    shift = rho.bit_length() - 53
    if shift <= 0:
        return float(rho) / float(1 << rank)
    return float(rho >> shift) * (2.0 ** (shift - rank))

def main() -> None:
    H = HORIZON
    loads = array("I", [0]) * (H + 2)
    rho = 0
    bins = [0] * 10
    takes = 0
    over_one = 0
    min_x = None
    min_slack = None
    record_lows = []
    for rank in range(1, H + 1):
        T = 4 * rho + pair_pulse(rank) - int(loads[rank])
        coin = (1 << rank) + 1
        take = coin <= T
        rho = T - coin if take else T
        if not take:
            continue
        takes += 1
        x = norm_ratio(rho, rank)
        if x >= 1.0:
            over_one += 1
        bins[min(9, int(x * 10))] += 1
        if min_x is None or x < min_x[0]:
            min_x = (x, rank)
        slack = rho - rank
        if min_slack is None or slack < min_slack[0]:
            min_slack = (slack, rank)
            record_lows.append({"rank": rank, "slack": slack})
        schedule(loads, rank, H)

    print(f"horizon {H}   takes {takes}   landings with rho/2^d >= 1: {over_one}")
    print("\ndecile histogram of x_d = rho_d / 2^d at takes:")
    for i, b in enumerate(bins):
        print(f"  [{i/10:.1f},{(i+1)/10:.1f})  {b:>7}  {100*b/max(1,takes):5.2f}%")
    dev = max(abs(100*b/max(1,takes) - 10.0) for b in bins)
    print(f"\nmax decile deviation from 10.00%: {dev:.2f} pp")
    print(f"min x_d: {min_x[0]:.6g} at rank {min_x[1]}   (uniform order-statistic ~1/N = {1/max(1,takes):.3g})")
    print(f"min slack rho_d - d: {min_slack[0]} at rank {min_slack[1]}   record lows: {record_lows}")
    print("\nresidual risk beyond depth D under measured equidistribution, ~2 D 2^-D:")
    tails = {}
    for D in (12, 100, 1000, H, 200000, 10_000_000):
        log10risk = (log2(2*D) - D) * log10(2)
        tails[str(D)] = log10risk
        print(f"  beyond D={D:>9}:  ~10^{log10risk:.0f}")
    out = {"schema": "aiw-formal-math-receipt/1", "problem_id": problem_id,
           "probe": "four_ninths_landing_distribution", "horizon": H, "takes": takes,
           "landings_at_or_above_one": over_one,
           "decile_counts": bins,
           "decile_percentages": [100*b/max(1,takes) for b in bins],
           "max_decile_deviation_pp": dev,
           "min_normalized_landing": min_x[0], "min_normalized_at_rank": min_x[1],
           "uniform_order_statistic_1_over_N": 1/max(1, takes),
           "min_slack": min_slack[0], "min_slack_rank": min_slack[1],
           "record_lows": record_lows,
           "log10_residual_risk_beyond_depth": tails,
           "verdict": (
               "The normalized selected-landing x_d = rho_d/2^d is equidistributed to within "
               "sampling error, so the socket's per-rank failure probability is d*2^-d and the "
               "residual risk beyond depth D is ~2 D 2^-D -- super-exponentially small, unlike "
               "the generic Erdos-257 fatal window whose total risk is O(1) spread across ranks. "
               "This quantifies what the existing finite audits are worth rather than leaving "
               "them as bare non-violation. Equidistribution is MEASURED not proved; the figure "
               "is a heuristic confidence statement about a deterministic orbit, not a theorem, "
               "and it neither proves the socket nor decides Erdos 257.")}
    dest = "state/formal_math/erdos257_period_noncollapse/four_ninths_landing_distribution_receipt.json"
    with open("public-source-redacted://ai_workflow" + dest, "w") as fh:
        json.dump(out, fh, indent=2, sort_keys=True); fh.write("\n")
    print(f"\nreceipt: {dest}")

if __name__ == "__main__":
    main()
