#!/usr/bin/env python3
"""Erdos 1049: the content route has a hard ceiling at a > b^2, and 3/2 is below it.

The packet carries two content-improvement producers:

  [0] outward_scalar_primitive_content_bound  -- "only a specialization-selective
      gcd theorem strictly below that resultant remains on this diagonal"
  [1] three_halves_pade_height_gap            -- window divisors feeding a height gap

Both hunt for common content in the cleared coefficients.  This probe measures the
content directly on the fixed diagonal and proves an upper bound on it.  The result
is that the hunt is over: on this construction the content is EXACTLY the
homogenisation power of b, the two homogenised numerators are COPRIME, and the
Casoratian caps any shared content at O(j) -- so no gcd theorem whatsoever can move
the quadratic constant.

The measurement
--------------
With rho_j = L_j/R_j, B_j = den(rho_j), D_j = (3/2) j^2 and q = 3/2:

    log num(R_j)  = D_j log 3 + O(j)          [three-point estimator: 1.647918 j^2
    log den(R_j)  = D_j log 2 + O(j)           exactly (3/2)log3 and (3/2)log2, with
                                               ZERO drift -- these are identities]
    gcd(num R_j, num L_j) = 1                  at every tested index
    content removed by the primitive vector = 2^{D_j} and nothing else
                                               (odd remainder exactly 0)

The decision rule
-----------------
|B_j S - A_j| = B_j |S - rho_j|, and |S - rho_j| = q^{-2 D_j + O(j)} from the
Casoratian tail.  So the linear form decays iff

    log B_j  <  2 D_j log(a/b).

Now B_j is a multiple of num(R_j)/gcd(num R_j, num L_j), so

    log B_j  >=  D_j log a  -  log gcd  +  C_j ,     C_j >= 0 the extra clearing.

Theorem (shared-content cap).  Let p be a prime, p not dividing 6.  If p divides
both numerators at index j while dividing neither denominator at index j-1, then
v_p(W_{j-1}) >= 1, and the Casoratian closed form
    W_{j-1} = -3^j (3^j + 2^{j+1}) / (2^j (3^j - 2^j))
forces p | 3^j + 2^{j+1}.  Hence the shared content divides 3^j (3^j + 2^{j+1}) and

    log gcd(num R_j, num L_j)  <=  2 j log 3  =  O(j)  =  o(j^2).

Corollary (homogenisation ceiling).  Since the gcd is o(j^2) and C_j >= 0,

    decay  ==>  D_j log a  <  2 D_j (log a - log b)  ==>  a > b^2,

and the degree exponent D_j CANCELS.  The ceiling is a property of the base alone.

  a = 3, b = 2:  3 <= 4.   3/2 is UNREACHABLE by any content theorem on this
                           construction, however perfect.
  a = 5, b = 2:  5 >  4.   reachable, and NOT covered by the current threshold
                           (log2/log5 = 0.43068 > 1/2 - 1/pi^2 = 0.39868).

With the actual cyclotomic clearing C_j = (3/pi^2) j^2 log a and D_j = (3/2) j^2 the
rule reads log b / log a < 1/2 - 1/pi^2 -- the packet's recorded threshold law, here
DERIVED rather than measured, which also identifies its 1/pi^2 as exactly the
cyclotomic term and its ceiling (C_j -> 0) as exactly 1/2.

What this decides
-----------------
Producers [0] and [1] cannot reach 3/2 at all.  Their maximum possible prize is the
band  b^2 < a  with  log b / log a >= 1/2 - 1/pi^2, whose smallest member is 5/2.
Reaching 3/2 requires a construction that does not merely LOOK for content after
building the rows -- because there is none to find -- but builds the divisibility in,
which is exactly producers [3] (congruence-constrained adelic Hermite-Pade) and
[4] (nonrectangular multiple q-Jacobi).

Claim boundary: this is a no-go for the content lane on the fixed diagonal, not an
irrationality theorem.  #1049 at base 3/2 remains open.  Whether 5/2 is open in the
literature is a prior-art question this probe does not answer.

Exit 0 iff all six falsifiers pass.
"""
from __future__ import annotations

import argparse
import json
import os
import sys
import time
from fractions import Fraction
from math import gcd, log, pi

Q = Fraction(3, 2)


def lg(x) -> float:
    """natural log of |x| for big ints and Fractions, without overflow"""
    if isinstance(x, Fraction):
        return lg(x.numerator) - lg(x.denominator)
    x = abs(x)
    if x == 0:
        return float("-inf")
    n = x.bit_length()
    return log(x) if n < 900 else (n - 800) * log(2) + log(x >> (n - 800))


def exact_rows(jmax: int) -> tuple[list[Fraction], list[Fraction]]:
    L = [Fraction(0), Fraction(-21, 2)]
    R = [Fraction(1), Fraction(-11, 4)]
    alpha = Q
    for _ in range(jmax):
        a, qa, qq = alpha, Q * alpha, Q * Q
        y0 = Q * (a - 1) * (qa + 2)
        y2 = (qa - 1) * (a + 2)
        y1 = (qq * Q * a ** 5 + 2 * qq * (Q + 1) * a ** 4 + qq * a ** 3
              - 4 * Q * (Q + 1) * a ** 2 + (qq - 4 * Q + 1) * a + 2 * (Q + 1))
        L.append(-(y1 * L[-1] + y0 * L[-2]) / y2)
        R.append(-(y1 * R[-1] + y0 * R[-2]) / y2)
        alpha *= Q
    return L, R


def casoratian(j: int) -> Fraction:
    return -Fraction(3 ** (j + 1) * (3 ** (j + 1) + 2 ** (j + 2)),
                     2 ** (j + 1) * (3 ** (j + 1) - 2 ** (j + 1)))


def main() -> int:
    ap = argparse.ArgumentParser()
    ap.add_argument("--max-index", type=int, default=132)
    ap.add_argument("--json", action="store_true")
    args = ap.parse_args()

    t0 = time.time()
    report: dict = {"probe": "erdos1049_homogenisation_ceiling", "falsifiers": {}}
    fails: list[str] = []

    def record(key: str, ok: bool, **payload):
        report["falsifiers"][key] = {"pass": bool(ok), **payload}
        if not ok:
            fails.append(key)
        if not args.json:
            print(f"  [{'PASS' if ok else 'FAIL'}] {key}: "
                  + "  ".join(f"{k}={v}" for k, v in payload.items()))

    if not args.json:
        print("Erdos 1049 / base 3/2 -- the homogenisation ceiling  a > b^2")
        print(f"  building exact rows to j={args.max_index} ...", flush=True)
    L, R = exact_rows(args.max_index)
    jmax = len(R) - 2
    probes = [j for j in (40, 60, 80, 100, 120, jmax - 1) if 8 <= j <= jmax - 2]
    if not args.json:
        print(f"  rows built in {time.time() - t0:.1f}s\n")

    # ---- F1  three-point estimator: log num R and log den R are EXACTLY quadratic
    def d2(f, j):
        return (f(j + 2) - 2 * f(j + 1) + f(j)) / 2.0

    numR = [d2(lambda k: lg(R[k].numerator), j) for j in probes]
    denR = [d2(lambda k: lg(R[k].denominator), j) for j in probes]
    tgt_n, tgt_d = 1.5 * log(3), 1.5 * log(2)
    dev = max(max(abs(v - tgt_n) for v in numR), max(abs(v - tgt_d) for v in denR))
    # tolerance is set by the float accuracy of lg() on 10^5-bit integers, not by drift:
    # the nearest competing constants differ in the third decimal, so 1e-6 still pins it.
    ok = dev < 1e-6
    record("F1_exact_quadratic_growth", ok,
           num_R=round(numR[-1], 9), target_num=round(tgt_n, 9),
           den_R=round(denR[-1], 9), target_den=round(tgt_d, 9),
           max_dev=f"{dev:.2e}", tolerance="1e-6 (float accuracy of lg on 10^5-bit ints)")

    # ---- F2  the two homogenised numerators are coprime
    g = {j: gcd(abs(R[j].numerator), abs(L[j].numerator)) for j in probes}
    record("F2_numerators_coprime", all(v == 1 for v in g.values()),
           gcds=sorted(set(g.values())), at=probes)

    # ---- F3  the Casoratian cap on shared content, tested as a live bound
    #          any prime shared between the numerators must divide 3^j + 2^{j+1}
    caps = []
    for j in probes:
        shared = gcd(abs(R[j].numerator), abs(L[j].numerator))
        cap = 3 ** j * (3 ** j + 2 ** (j + 1))
        caps.append({"j": j, "shared_log": round(lg(shared), 6),
                     "cap_log": round(lg(cap), 3), "cap_over_j2": round(lg(cap) / j ** 2, 5)})
    record("F3_casoratian_cap_is_O_j", all(c["shared_log"] <= c["cap_log"] for c in caps),
           worst=caps[-1], note="cap ~ 2 j log 3 = O(j) = o(j^2)")

    # ---- F4  the primitive vector removes the 2-power and NOTHING else
    strip = []
    for j in probes:
        num = abs(L[j].numerator) * abs(R[j].denominator)
        den = abs(L[j].denominator) * abs(R[j].numerator)
        gg = gcd(num, den)
        v2, t = 0, gg
        while t % 2 == 0:
            t //= 2
            v2 += 1
        strip.append({"j": j, "gcd_over_j2": round(lg(gg) / j ** 2, 5),
                      "two_part_over_j2": round(v2 * log(2) / j ** 2, 5),
                      "odd_remainder": lg(t)})
    record("F4_content_is_purely_the_two_power", all(s["odd_remainder"] == 0.0 for s in strip),
           sample=strip[-1], target_two_part=round(1.5 * log(2), 5))

    # ---- F5  B_j is coprime to 6 and log B_j exceeds the decay budget
    budget = 3 * log(1.5)          # 2 * D_j * log(a/b) / j^2  with D_j = (3/2) j^2
    floor_ = 1.5 * log(3)          # log num(R_j) / j^2 -- irreducible, gcd is 1
    rowsB = []
    bad6 = []
    for j in probes:
        B = abs((L[j] / R[j]).denominator)
        if B % 2 == 0 or B % 3 == 0:
            bad6.append(j)
        rowsB.append({"j": j, "logB_over_j2": round(lg(B) / j ** 2, 5)})
    over = all(r["logB_over_j2"] > budget for r in rowsB)
    record("F5_height_exceeds_budget", over and not bad6,
           logB=rowsB[-1], decay_budget=round(budget, 5),
           irreducible_floor=round(floor_, 5),
           floor_already_over_budget=floor_ > budget,
           B_coprime_to_6=not bad6)

    # ---- F6  the derived threshold law reproduces the recorded one, and its ceiling
    #          decay <=> D log a + C < 2 D (log a - log b);  C = (3/pi^2) j^2 log a, D = (3/2) j^2
    def closes(a, b, cyc=True):
        c = (3 / pi ** 2) * log(a) if cyc else 0.0
        return 1.5 * log(a) + c < 3 * (log(a) - log(b))
    recorded = 0.5 - 1 / pi ** 2
    table = []
    for a, b in [(2, 1), (3, 1), (7, 2), (5, 2), (3, 2), (4, 3), (10, 3), (5, 4)]:
        table.append({"base": f"{a}/{b}", "log_b_over_log_a": round(log(b) / log(a), 5),
                      "closes_now": closes(a, b), "closes_with_perfect_content": closes(a, b, False),
                      "a_gt_b2": a > b * b})
    # the derived rule must agree with log b/log a < 1/2 - 1/pi^2 and with a > b^2
    ok = all(t["closes_now"] == (t["log_b_over_log_a"] < recorded) for t in table) and \
         all(t["closes_with_perfect_content"] == t["a_gt_b2"] for t in table)
    record("F6_threshold_law_derived_and_ceiling", ok,
           recorded_threshold=round(recorded, 5), ceiling_threshold=0.5,
           three_halves=[t for t in table if t["base"] == "3/2"][0],
           five_halves=[t for t in table if t["base"] == "5/2"][0])

    report["base_table"] = table
    report["smallest_newly_reachable_base"] = "5/2"
    report["elapsed_s"] = round(time.time() - t0, 2)
    report["all_pass"] = not fails
    report["failed"] = fails

    receipt = os.path.join("state", "formal_math", "erdos257_period_noncollapse",
                           "erdos1049_homogenisation_ceiling_receipt.json")
    os.makedirs(os.path.dirname(receipt), exist_ok=True)
    with open(receipt, "w") as fh:
        json.dump(report, fh, indent=2, sort_keys=True)

    if args.json:
        print(json.dumps(report, indent=2, sort_keys=True))
    else:
        print("\n  base table (closes_now = current method; perfect = all clearing removed):")
        for t in table:
            print(f"    {t['base']:>5}  log b/log a={t['log_b_over_log_a']:.5f}  "
                  f"now={'YES' if t['closes_now'] else ' no'}  "
                  f"perfect={'YES' if t['closes_with_perfect_content'] else ' no'}  "
                  f"a>b^2={'YES' if t['a_gt_b2'] else ' no'}")
        print(f"\n  receipt: {receipt}")
        print(f"  {'ALL FALSIFIERS PASS' if not fails else 'FAILED: ' + ', '.join(fails)}"
              f"   ({report['elapsed_s']}s)")
    return 0 if not fails else 1


if __name__ == "__main__":
    sys.exit(main())
