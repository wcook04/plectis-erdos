#!/usr/bin/env python3
"""Erdos 1049: a conditional rank/rate calibration for Hermite--Pade budgets.

Setting.  q = a/b in lowest terms, a > b >= 1, S = sum_{n>=1} 1/(q^n - 1).  A rank-r
type-I system uses r functions f_0 = 1, f_1, ..., f_{r-1} and polynomials P_i of
degree <= D, giving the linear form  F = sum_i P_i(q) f_i.

Conditional model.  Suppose a concrete rank-r family independently proves the following
three exponents, all per unit of degree D:

  decay      the idealized Hermite-Pade count.  In x = 1/q, r(D+1) unknowns can
             impose the corresponding number of homogeneous vanishing conditions;
             if the selected family realizes this count with the required degree
             normalization, its remainder scale is q^{-(r-1)D}. gain (r-1) log(a/b)
  homogenise clearing P_i(a/b) to integers costs b^D.                cost log b
  clear      the cyclotomic denominator of the coefficients costs a^{kappa D}.
             MEASURED at rank two on the fixed diagonal: the clearing is
             (3/pi^2) j^2 log a against D_j = (3/2) j^2, so kappa = 2/pi^2.
                                                                    cost kappa log a

Under those hypotheses, the displayed exponential budget is positive iff cost < gain:

    kappa log a + log b  <  (r-1)(log a - log b)
    <=>   r log b  <  (r - 1 - kappa) log a
    <=>   t := log b / log a  <  (r - 1 - kappa) / r .

CALIBRATION.  At r = 2 with the measured kappa = 2/pi^2 this is exactly

    t < (1 - 2/pi^2)/2 = 1/2 - 1/pi^2 = 0.398679... ,

the packet's recorded threshold law, reproduced to every digit.  That is the warrant
for reusing this numerical rate as a comparison column; it is not evidence that a
rank-r family for r > 2 has the same clearing rate or realizes the idealized decay.

CONDITIONAL CALIBRATION.   r > (1 + kappa) / (1 - t).

    base   t=log b/log a   first r under reused kappa_2   first r if kappa = 0
    q int      0.00000            2                          2
    7/2        0.35621            2   <- published           2
    5/2        0.43068            3                          2   <- content route
    3/2        0.63093            4                          3
    4/3        0.79248            6                          5
    5/4        0.86135            9                          8

In this table, 3/2 is the first listed base that the rank-two budget cannot admit even
with zero coefficient-clearing cost (that ceiling is t < 1/2, i.e. a > b^2; see
HomogenisationCeilingProof.md).  A rank-three family reusing the measured rank-two
clearing rate would also miss.  Two illustrative ways a concrete family might enter
the budget are:

  (A) rank 3 with a better clearing.  Rank three closes 3/2 iff its per-degree
      clearing rate kappa_3 satisfies (2 - kappa_3)/3 > 0.63093, i.e.
      kappa_3 < 0.10721 -- at most 53% of the rank-two rate.  The packet's recorded
      "rectangular two-function Hermite-Pade optimisation does not improve the
      classical threshold" is consistent: that shape does not realise the generic
      count.  Nonrectangular multi-indices are explicitly not covered by it.
  (B) a rank-4 family that independently proves both the idealized decay and the same
      clearing rate as the rank-two calibration.  Under those extra hypotheses the
      numerical margin is 0.69933 - 0.63093 = 0.06840 in t.  Cubic decay in another
      parameter does not by itself identify a construction as rank four, and the
      packet's Zudilin/Hankel route is not evidence for this hypothetical family.

WHAT THIS IS AND IS NOT.  This is a conditional budget and room analysis, not a
construction.  For a specified family satisfying the displayed decay and clearing
hypotheses, the inequality is the corresponding exponent test.  Rank alone does not
fix either rate, so the table neither proves that an unspecified rank can work nor
rules out every family of a lower rank.  It does not supply polynomials, integrality,
or nonvanishing.  kappa is measured only at rank two; carrying it to r > 2 is a
comparison model.  The kappa = 0 column is only a clearing-free numerical ceiling
within the same idealized decay model.

Exit 0 iff all six bounded consistency checks pass.
"""
from __future__ import annotations

import argparse
import json
import os
import sys
from fractions import Fraction
from math import ceil, gcd, log, pi

KAPPA = 2 / pi ** 2          # measured rank-two clearing rate, = (3/pi^2)/(3/2)


# ---------------------------------------------------------------- rank-3 reality check
def _series(nmax: int) -> tuple[list[int], list[int]]:
    """zeta_q(1) = sum d(N) x^N ;  zeta_q(2) = sum (sigma(N)-d(N)) x^N,  x = 1/q"""
    dv, sv = [0] * (nmax + 1), [0] * (nmax + 1)
    for n in range(1, nmax + 1):
        for m in range(n, nmax + 1, n):
            dv[m] += 1
            sv[m] += n
    return [0] + dv[1:], [0] + [sv[N] - dv[N] for N in range(1, nmax + 1)]


def generic_type_I(D: int) -> list[int] | None:
    """primitive integer type-I Hermite-Pade coefficients: p0 + p1 f1 + p2 f2 = O(x^(3D+2))"""
    M = 3 * D + 2
    f1, f2 = _series(M + D + 2)
    rows = []
    for k in range(M):
        row = [Fraction(0)] * (3 * D + 3)
        if k <= D:
            row[k] = Fraction(1)
        for i in range(D + 1):
            if k - i >= 0:
                row[(D + 1) + i] = Fraction(f1[k - i])
                row[2 * (D + 1) + i] = Fraction(f2[k - i])
        rows.append(row)
    n, A, piv, r = 3 * D + 3, [x[:] for x in rows], [], 0
    for c in range(n):
        p = next((i for i in range(r, len(A)) if A[i][c] != 0), None)
        if p is None:
            continue
        A[r], A[p] = A[p], A[r]
        pv = A[r][c]
        A[r] = [v / pv for v in A[r]]
        for i in range(len(A)):
            if i != r and A[i][c] != 0:
                f = A[i][c]
                A[i] = [a - f * b for a, b in zip(A[i], A[r])]
        piv.append(c)
        r += 1
        if r == len(A):
            break
    free = [c for c in range(n) if c not in piv]
    if not free:
        return None
    fc = free[0]
    sol = [Fraction(0)] * n
    sol[fc] = Fraction(1)
    for i, c in enumerate(piv):
        sol[c] = -A[i][fc]
    den = 1
    for v in sol:
        den = den * v.denominator // gcd(den, v.denominator)
    ints = [int(v * den) for v in sol]
    g = 0
    for v in ints:
        g = gcd(g, abs(v))
    return [v // g for v in ints] if g else ints


def threshold(r: int, kappa: float = KAPPA) -> float:
    """Largest t admitted by the displayed conditional decay/clearing model."""
    return (r - 1 - kappa) / r


def rank_needed(t: float, kappa: float = KAPPA) -> int:
    """First r admitted by the model for the supplied kappa; not an existence claim."""
    if t >= 1:
        return 10 ** 9
    r = (1 + kappa) / (1 - t)
    r = int(ceil(r))
    while not t < threshold(r, kappa):
        r += 1
    return max(r, 2)


BASES = [(2, 1), (3, 1), (7, 2), (5, 2), (3, 2), (10, 3), (4, 3), (5, 4), (11, 3), (17, 4)]


def main() -> int:
    ap = argparse.ArgumentParser()
    ap.add_argument("--json", action="store_true")
    args = ap.parse_args()

    report: dict = {"probe": "erdos1049_rank_budget_law", "kappa": KAPPA, "falsifiers": {}}
    fails: list[str] = []

    def record(key: str, ok: bool, **payload):
        report["falsifiers"][key] = {"pass": bool(ok), **payload}
        if not ok:
            fails.append(key)
        if not args.json:
            print(f"  [{'PASS' if ok else 'FAIL'}] {key}: "
                  + "  ".join(f"{k}={v}" for k, v in payload.items()))

    if not args.json:
        print("Erdos 1049 -- conditional rank/rate calibration"
              "   t < (r - 1 - kappa)/r,   reused kappa_2 = 2/pi^2\n")

    # ---- F1  rank two reproduces the recorded threshold exactly
    recorded = 0.5 - 1 / pi ** 2
    record("F1_rank_two_is_the_recorded_threshold", abs(threshold(2) - recorded) < 1e-15,
           derived=round(threshold(2), 12), recorded_half_minus_one_over_pi2=round(recorded, 12))

    # ---- F2  rank two with zero clearing is the homogenisation ceiling a > b^2
    ok = abs(threshold(2, 0.0) - 0.5) < 1e-15 and all(
        (log(b) / log(a) < threshold(2, 0.0)) == (a > b * b) for a, b in BASES if b > 0 and a > 1)
    record("F2_zero_clearing_rank_two_is_a_gt_b2", ok, ceiling=threshold(2, 0.0),
           checked_bases=len(BASES))

    # ---- F3  the published cases must come out at rank two
    published = [(2, 1), (3, 1), (7, 2)]
    got = {f"{a}/{b}": rank_needed(log(b) / log(a)) for a, b in published}
    record("F3_published_cases_are_rank_two", all(v == 2 for v in got.values()), ranks=got)

    # ---- F4  the reused rank-two calibration first admits 3/2 at r=4
    t32 = log(2) / log(3)
    r_obs, r_free = rank_needed(t32), rank_needed(t32, 0.0)
    record("F4_reused_rank_two_clearing_first_admits_rank_four", r_obs == 4 and r_free == 3,
           t=round(t32, 5), first_rank_under_reused_rank_two_clearing=r_obs,
           first_rank_under_zero_clearing_model=r_free,
           rank3_fails_by=round(t32 - threshold(3), 5),
           rank4_margin=round(threshold(4) - t32, 5))

    # ---- F5  the rank-3 clearing rate that would close 3/2
    #          (2 - k)/3 > t  <=>  k < 2 - 3t
    k3 = 2 - 3 * t32
    ok = k3 > 0 and k3 < KAPPA and abs(threshold(3, k3) - t32) < 1e-12
    record("F5_rank_three_clearing_target", ok,
           kappa3_must_be_below=round(k3, 5), rank_two_rate=round(KAPPA, 5),
           fraction_of_rank_two_rate=round(k3 / KAPPA, 4))

    # ---- F6  a generic rank-3 solve cannot enter the lane: measure its clearing rate
    #          kappa_3(D) = log(height)/(D log 3) must stay below 2 - 3 log2/log3
    gen = []
    for D in range(3, 13):
        c = generic_type_I(D)
        if c is None:
            continue
        H = max(abs(v) for v in c)
        gen.append({"D": D, "log_height": round(log(H), 4),
                    "kappa3": round(log(H) / (D * log(3)), 5)})
    worst = min(g["kappa3"] for g in gen)
    record("F6_generic_rank3_solve_misses_by_an_order_of_magnitude",
           bool(gen) and worst > k3,
           budget=round(k3, 5), best_generic_kappa3=worst,
           over_budget_factor=round(worst / k3, 1),
           at_D=[(g["D"], g["kappa3"]) for g in gen[:4]],
           note=("D=2 is a degenerate index whose primitive coefficients are all +-1; it is "
                 "a single index, not a family, and is excluded from the range scanned here"))
    report["generic_rank3_scan"] = gen

    table = []
    for a, b in BASES:
        t = log(b) / log(a)
        table.append({"base": f"{a}/{b}", "t": round(t, 5),
                      "first_rank_under_reused_rank_two_clearing": rank_needed(t),
                      "first_rank_under_zero_clearing_model": rank_needed(t, 0.0)})
    report["base_table"] = table
    report["thresholds"] = {r: round(threshold(r), 5) for r in range(2, 8)}
    report["all_pass"] = not fails
    report["failed"] = fails

    receipt = os.path.join("state", "formal_math", "erdos257_period_noncollapse",
                           "erdos1049_rank_budget_law_receipt.json")
    os.makedirs(os.path.dirname(receipt), exist_ok=True)
    with open(receipt, "w") as fh:
        json.dump(report, fh, indent=2, sort_keys=True)

    if args.json:
        print(json.dumps(report, indent=2, sort_keys=True))
    else:
        print("\n  thresholds t < (r-1-kappa)/r:")
        for r in range(2, 8):
            print(f"    rank {r}: {threshold(r):.5f}   (zero clearing: {threshold(r,0.0):.5f})")
        print("\n  first rank admitted by each displayed conditional model:")
        for row in table:
            print(f"    {row['base']:>5}  t={row['t']:.5f}"
                  f"   reused-kappa_2 r={row['first_rank_under_reused_rank_two_clearing']}"
                  f"   (zero-clearing model: r={row['first_rank_under_zero_clearing_model']})")
        print(f"\n  receipt: {receipt}")
        print(f"  {'ALL FALSIFIERS PASS' if not fails else 'FAILED: ' + ', '.join(fails)}")
    return 0 if not fails else 1


if __name__ == "__main__":
    sys.exit(main())
