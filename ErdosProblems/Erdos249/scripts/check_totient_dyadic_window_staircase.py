#!/usr/bin/env python3
"""Dyadic-window insufficiency for Erdos 249, and the exact repair.

Setting.  S = sum_{n>=1} phi(n)/2^n,  P_n = sum_{j<=n} 2^{n-j} phi(j),
R_n = 2^n S - P_n,  0 < R_n <= n+2,  R_n = 2 R_{n-1} - phi(n).
Suppose S = a/(2^c v) with v odd.  For n >= c,  u_n := v R_n = a 2^{n-c} - v P_n
is an integer with  0 < u_n <= v(n+2),  and  u_n = 2^t u_{n-t} - v sum_{j=1}^t 2^{t-j} phi(n-t+j).

PART A (route falsification, proved, checked numerically here).
  A1.  The TERMWISE window hypothesis  2^{max(0,j-c)} | phi(N+j)  (1<=j<=t)  yields only
       2^{t-c} | u_{N+t},  NOT  2^t | u_{N+t}: the j-th term of the sum has 2-adic
       valuation  (t-j) + max(0, j-c) = t - min(j,c) >= t-c,  attained at j >= c.
  A2.  Under the STRENGTHENED hypothesis  2^j | phi(N+j)  (1<=j<=t)  one does get
       2^t | u_{N+t}.
  A3.  Either way the argument is VACUOUS.  The hypothesis at j=t forces
       2^{t-c} <= phi(N+t) <= N+t-1  (resp. 2^t <= N+t-1), while the contradiction
       with 0 < u_{N+t} <= v(N+t+2) needs 2^{t-c} > v(N+t+2) (resp. 2^t > v(N+t+2)).
       Since v >= 1 gives v(N+t+2) > N+t-1, the two are incompatible for EVERY
       v >= 1 and EVERY c >= 0.  So the termwise dyadic-window transfer excludes no
       denominator at all -- not merely those with odd part v >= 2^c.
  A4.  Measured: the 2-adic staircase  t(X) = max{t : exists N<=X with
       v_2(phi(N+j)) >= j for 1<=j<=t}  against log2 X and sqrt(2 log2 X).

PART B (the exact repair, and the live consumer).
  For t <= n-c one has  2^t | u_n  <=>  2^t | v P_n  <=>  2^t | P_n  (v odd).
  Hence rationality S = a/(2^c v) forces, for every n with n - c > log2(v(n+2)),
        v_2(P_n) <= log2( v (n+2) ).
  CONSUMER (sufficient for irrationality of S):
        for every v >= 1 there are infinitely many n with  2^{v_2(P_n)} > v (n+2).
  This is a pure 2-adic consumer on the PREFIX integer P_n; it is not the
  ||v 2^c S|| statistic and not the canonical Mersenne residue supply.
  Measured: excess(X) = max_{n<=X} ( v_2(P_n) - log2(n+2) ).

PART C (backward-window residue occupancy).
  With B_k(n) = sum_{i<k} 2^i phi(n-i) one has P_n = B_k(n) (mod 2^k), so under
  rationality  u_n = ((-v B_k(n)) mod 2^k)  whenever 2^k > v(n+2).  Measured:
  the fraction of n whose residue lands in the admissible window (0, v(n+2)],
  against the heuristic v(n+2)/2^k.

Run: ./repo-python formal_math/erdos257_period_noncollapse/ErdosProblems/Erdos249/\
scripts/check_totient_dyadic_window_staircase.py --quick
"""
from __future__ import annotations

import argparse
import json
import math
import sys
from array import array


# ------------------------------------------------------------------ sieves --
def v2_totient_sieve(X: int) -> array:
    """acc[n] = v_2(phi(n)) for n <= X."""
    sieve = bytearray([1]) * (X + 1)
    sieve[0:2] = b"\x00\x00"
    acc = array("B", bytes(X + 1))
    for i in range(2, int(X ** 0.5) + 1):
        if sieve[i]:
            sieve[i * i:: i] = bytearray(len(range(i * i, X + 1, i)))
    for p in range(3, X + 1, 2):
        if sieve[p]:
            v = (p - 1 & -(p - 1)).bit_length() - 1     # v_2(p-1)
            if v:
                for n in range(p, X + 1, p):
                    acc[n] += v
    a = 2
    while (1 << a) <= X:
        step = 1 << a
        for n in range(step, X + 1, step):
            acc[n] += 1
        a += 1
    return acc


def totient_sieve(X: int) -> array:
    ph = array("I", range(X + 1))
    for i in range(2, X + 1):
        if ph[i] == i:
            for j in range(i, X + 1, i):
                ph[j] -= ph[j] // i
    return ph


# ------------------------------------------------------------- Part A: A1-A3 -
def part_a_algebra(cases) -> dict:
    """Numerically confirm the valuation accounting of A1/A2 on synthetic windows."""
    rows = []
    for (c, t) in cases:
        # worst case allowed by the conductor's hypothesis: v_2(phi(N+j)) = max(0, j-c)
        conductor = min([t] + [(t - j) + max(0, j - c) for j in range(1, t + 1)])
        strengthened = min([t] + [(t - j) + j for j in range(1, t + 1)])
        rows.append({
            "c": c, "t": t,
            "guaranteed_v2_u_under_conductor_hypothesis": conductor,
            "conductor_claimed": t,
            "conductor_claim_holds": conductor >= t,
            "guaranteed_v2_u_under_strengthened_hypothesis": strengthened,
            "strengthened_claim_holds": strengthened >= t,
        })
    return {
        "rows": rows,
        "A1_conductor_conclusion_is_off_by_2^c": all(
            r["guaranteed_v2_u_under_conductor_hypothesis"] == max(r["t"] - r["c"], 0)
            or r["c"] == 0 for r in rows),
        "A2_strengthened_hypothesis_gives_2^t": all(r["strengthened_claim_holds"] for r in rows),
        "A3_statement": ("hypothesis at j=t forces 2^(t-c) <= phi(N+t) <= N+t-1 while the "
                         "contradiction needs 2^(t-c) > v(N+t+2) >= N+t+2; incompatible for "
                         "every v>=1 and c>=0, so the termwise window excludes no denominator"),
    }


def part_a_staircase(X: int) -> dict:
    acc = v2_totient_sieve(X)
    best_t, best_N = 0, None
    per_scale = {}
    scale = 1 << 10
    cur_t, cur_N = 0, None
    for N in range(1, X):
        t = 0
        while N + t + 1 <= X and acc[N + t + 1] >= t + 1:
            t += 1
        if t > cur_t:
            cur_t, cur_N = t, N
        if N == scale or N == X - 1:
            per_scale[str(N)] = {
                "t": cur_t, "witness_N": cur_N,
                "log2_X": math.log2(N),
                "sqrt_2log2X": math.sqrt(2 * math.log2(N)),
            }
            scale <<= 1
    best_t, best_N = cur_t, cur_N
    return {"X": X, "max_t": best_t, "witness_N": best_N,
            "cap_from_2^t<=N+t": int(math.floor(math.log2(X))),
            "by_scale": per_scale}


# -------------------------------------------------------------- Part B ------
def part_b_prefix_valuation(X: int, ph: array) -> dict:
    MASK = (1 << 96) - 1
    P = 0
    best = (-999.0, None, None)
    recs = []
    per_scale = {}
    scale = 1 << 10
    for n in range(1, X + 1):
        P = ((P << 1) + ph[n]) & MASK
        v = 96 if P == 0 else ((P & -P).bit_length() - 1)
        ex = v - math.log2(n + 2)
        if ex > best[0]:
            best = (ex, n, v)
            recs.append({"n": n, "v2_P_n": v, "excess_log2": ex})
        if n == scale or n == X:
            per_scale[str(n)] = {"best_excess": best[0], "at_n": best[1], "v2": best[2]}
            scale <<= 1
    return {"X": X, "max_excess_log2": best[0], "witness_n": best[1],
            "v2_P_n_at_witness": best[2],
            "consumer": ("if for every v>=1 there are infinitely many n with "
                         "2^{v_2(P_n)} > v(n+2) then S is irrational"),
            "records": recs[-12:], "by_scale": per_scale}


def tail_R(n: int, ph: array, terms: int = 90):
    """R_n = sum_{j>=1} phi(n+j)/2^j, as a rational lower bound plus its error bound."""
    from fractions import Fraction as Fr
    R = Fr(0)
    for j in range(1, terms + 1):
        if n + j >= len(ph):
            return None, None
        R += Fr(int(ph[n + j]), 1 << j)
    return R, Fr(n + terms + 2, 1 << terms)


def exclusion_rectangles(records, ph) -> list:
    """A single n with t = v_2(P_n) excludes {c <= n-t} x {odd v < 2^t/R_n}.

    Proof: S = a/(2^c v) with v odd and c <= n-t gives the integer
    u_n = v R_n = a 2^{n-c} - v P_n with 0 < u_n <= v R_n; 2^t divides both
    a 2^{n-c} (as n-c >= t) and v P_n (as 2^t | P_n), so u_n is a positive
    multiple of 2^t, hence v R_n >= 2^t.
    """
    out = []
    for r in records:
        n, t = r["n"], r["v2_P_n"]
        R, err = tail_R(n, ph)
        if R is None:
            continue
        out.append({
            "n": n, "v2_P_n": t, "c_bound": n - t,
            "R_n_lower": float(R), "R_n_upper": float(R + err),
            "odd_v_excluded_below_crude": (1 << t) / (n + 2),
            "odd_v_excluded_below_sharp": (1 << t) / float(R + err),
        })
    return out


# -------------------------------------------------------------- Part C ------
def part_c_backward_window(X: int, ph: array, vs, deltas) -> dict:
    rows = []
    for v in vs:
        for delta in deltas:
            hit = 0
            tot = 0
            heur = 0.0
            n = 64
            while n <= X:
                w = v * (n + 2)
                k = w.bit_length() + delta          # 2^k > v(n+2)
                if k > n:
                    n += 1
                    continue
                B = 0
                for i in range(k):
                    B = (B << 1) + ph[n - k + 1 + i]
                r = (-v * B) % (1 << k)
                tot += 1
                heur += w / float(1 << k)
                if 0 < r <= w:
                    hit += 1
                n += 1
            rows.append({"v": v, "delta": delta, "n_tested": tot, "hits": hit,
                         "observed_fraction": hit / tot if tot else None,
                         "heuristic_fraction": heur / tot if tot else None,
                         "ratio_obs_over_heur": (hit / heur) if heur else None})
    return {"X": X, "rows": rows}


def main() -> int:
    ap = argparse.ArgumentParser()
    ap.add_argument("--quick", action="store_true")
    ap.add_argument("--json", action="store_true")
    ap.add_argument("--out")
    args = ap.parse_args()

    X_stair = 1 << 20 if args.quick else 10_000_000
    X_pref = 1 << 18 if args.quick else 1 << 22
    X_win = 1 << 14 if args.quick else 1 << 16

    rep = {"mode": "quick" if args.quick else "full"}
    rep["part_a_algebra"] = part_a_algebra([(0, 5), (1, 6), (2, 8), (3, 10), (5, 14)])
    rep["part_a_staircase"] = part_a_staircase(X_stair)
    ph = totient_sieve(max(X_pref, X_win) + 4)
    rep["part_b_prefix_valuation"] = part_b_prefix_valuation(X_pref, ph)
    rep["part_b_exclusion_rectangles"] = exclusion_rectangles(
        rep["part_b_prefix_valuation"]["records"], ph)
    rep["part_c_backward_window"] = part_c_backward_window(
        X_win, ph, (1, 3, 5, 7), (1, 2, 3, 4, 5, 6))

    if args.out:
        with open(args.out, "w") as fh:
            json.dump(rep, fh, indent=1)
    if args.json:
        print(json.dumps(rep, indent=1))
    else:
        a = rep["part_a_algebra"]
        print("A1 conductor conclusion off by 2^c:", a["A1_conductor_conclusion_is_off_by_2^c"])
        print("A2 strengthened hypothesis gives 2^t:", a["A2_strengthened_hypothesis_gives_2^t"])
        s = rep["part_a_staircase"]
        print(f"A4 staircase: max t = {s['max_t']} at N = {s['witness_N']} "
              f"(X = {s['X']}, log2 X = {math.log2(s['X']):.1f}, "
              f"sqrt(2 log2 X) = {math.sqrt(2 * math.log2(s['X'])):.2f})")
        for k, vv in s["by_scale"].items():
            print(f"   X={k:>9} t={vv['t']:2d}  log2X={vv['log2_X']:5.2f} "
                  f"sqrt(2log2X)={vv['sqrt_2log2X']:5.2f}")
        b = rep["part_b_prefix_valuation"]
        print(f"B max (v_2(P_n) - log2(n+2)) = {b['max_excess_log2']:.3f} at n = {b['witness_n']} "
              f"(v_2 = {b['v2_P_n_at_witness']}), X = {b['X']}")
        for k, vv in b["by_scale"].items():
            print(f"   X={k:>9} best excess={vv['best_excess']:6.3f} at n={vv['at_n']}")
        print("B exclusion rectangles  (S != a/(2^c v), v odd):")
        for e in rep["part_b_exclusion_rectangles"]:
            print(f"   n={e['n']:>9} v_2(P_n)={e['v2_P_n']:2d}  all c <= {e['c_bound']:>9}  "
                  f"and all odd v < {e['odd_v_excluded_below_sharp']:.2f} "
                  f"(crude bound {e['odd_v_excluded_below_crude']:.2f})")
        print("C backward-window occupancy (observed / heuristic):")
        for r in rep["part_c_backward_window"]["rows"]:
            print(f"   v={r['v']} delta={r['delta']} n={r['n_tested']:6d} "
                  f"obs={r['observed_fraction']:.5f} heur={r['heuristic_fraction']:.5f} "
                  f"ratio={r['ratio_obs_over_heur']:.4f}")
    return 0


if __name__ == "__main__":
    sys.exit(main())
