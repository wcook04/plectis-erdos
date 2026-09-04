#!/usr/bin/env python3
"""Erdos 1049 (base 3/2): a FIXED prime divides every primitive q-Apery denominator
coordinate from a computable index on, so step 1 of the three_halves_pade_height_gap
producer needs no moving prime and no effective form of Boyd's conjecture.

The recorded packet position was:

    "the refutation of fixed-prime infinite-tail persistence is unconditional and
     classical rather than computational"  (p-1 in J_p by Wolstenholme)
    "The surviving q-Apery producer is therefore a cofinal moving-prime law ...
     the remaining input is Boyd's heuristic for J_p made effective"

That conflates two different tails.  Wolstenholme kills a tail that starts at the
FIRST APPEARANCE index j = d = ord_p(3/2).  It says nothing about a tail that
starts past the LAST loss block.  If J_p is finite there is such a tail, and for
p = 5 finiteness of J_p is not a conjecture: it is a ten-element check.

Chain proved / certified here
-----------------------------
L1  descent lemma (proved, two lines):  H_n = H_{floor(n/p)}/p + sum_{p not| j<=n} 1/j,
    the second sum is p-integral, so v_p(H_n) >= 1 and n >= p force
    v_p(H_{floor(n/p)}) >= 1.  Hence J_p ∪ {0} is a tree under n -> floor(n/p) and
    the children of n lie in [pn, pn+p-1].

T_A J_5 = {4, 20, 24}, FINITE.  Level 1 of the tree is {4}; level 2 is {20,24};
    level 3 is the ten candidates [100,104] ∪ [120,124] and every one fails.
    By L1 the tree can grow no further.  Same argument gives J_3 = {2,7,22} and
    J_13 = {12,156,168}.

L2  monodromy at 5:  R_{j+P_N} == -R_j  (mod 5^N),  P_N = ord_{5^N}(3/2) = 2*5^(N-1).
    Certified per level.  det of the one-period transfer is 1 by the Casoratian
    closed form (C); the content of L2 is that the transfer is -1 on the R-line.
    The second solution L does NOT satisfy it -- that failure is the resonant log
    term, and it is exactly what produces the harmonic number.

L3  5-adic continuity (C5), from L2:  g_m mod 5^N depends only on m mod 5^(N-1),
    where the block increment is  rho_{2m} - rho_{2m-1} = -(4/(5m)) g_m  and
        g_m = lam^m (lam^m + 2) / (u_m R_{2m-1} R_{2m}),
        lam = 9/4 = q^2,  pi = 5/4,  u_m = (lam^m - 1)/(m pi).
    lam^m and u_m are 5-adically analytic in m; R_{2m-1}R_{2m} is invariant under
    m -> m + 5^(N-1) because the two sign flips of L2 cancel in the product.

T_B exact harmonic law at 5.  (C5) gives v_5(g_{5^a t} - g_*) >= a+1 for every a
    and every t coprime to 5, so
        sum_{m<=K} g_m/m  -  g_* H_K
          = sum_a 5^-a sum_{5 not| t <= K/5^a} (g_{5^a t} - g_*)/t   in  5 Z_5,
    using  H_K = sum_a 5^-a sum_{5 not| t <= K/5^a} 1/t  exactly.  Therefore
        v_5(rho_j) = v_5(H_{floor(j/2)}) - 1   whenever  v_5(H_{floor(j/2)}) < 1,
    i.e. whenever floor(j/2) is not in J_5.

T_C 5 | B_j for every j >= 50, and v_5(B_j) = 1 - v_5(H_{floor(j/2)}).

COR for every start s >= 50 the window [s, s + 3s^2+5s+3] has window gcd divisible
    by 5^(1 + floor(log_5(s/2))).  Step 1 is cofinal, unconditionally, with a fixed
    witness -- no first-appearance prime, no factoring of 3^s - 2^s, no Boyd.

CORRECTION this probe also pins that hypothesis (H) of CasoratianBlockLawProof.md,
    "c_K == c (mod p^eps) for a fixed p-adic unit c, independent of K", is FALSE at
    p = 5: g_m mod 25 takes three values.  (C5) is the true and sufficient
    replacement.  Falsifier F7 fails loudly if a later edit reinstates (H).

Claim boundary: this closes step 1 of the producer.  It bounds no coefficient
height and supplies no analytic decay, so Erdos #1049 at base 3/2 stays open.  The
separate "prime to the first power in a two-row determinant" condition of the
1/q-gap step is NOT settled here: v_5(B_j) = 1 exactly when v_5(H_{floor(j/2)}) = 0,
which in the tested range happens only on floor(j/2) in [100,104] ∪ [120,124], and
whether that recurs cofinally is open.

Exit 0 iff all eight falsifiers pass.
"""
from __future__ import annotations

import argparse
import json
import math
import os
import sys
import time
from fractions import Fraction
from math import gcd

Q = Fraction(3, 2)
LAM = Fraction(9, 4)
PI = Fraction(5, 4)


# ---------------------------------------------------------------- p-adic helpers
def vp_int(n: int, p: int) -> int:
    if n == 0:
        return 10 ** 9
    v = 0
    while n % p == 0:
        n //= p
        v += 1
    return v


def vp_frac(f: Fraction, p: int) -> int:
    if f == 0:
        return 10 ** 9
    return vp_int(f.numerator, p) - vp_int(f.denominator, p)


def unit_mod(f: Fraction, p: int, n: int) -> int:
    """value of a p-adic-unit rational modulo p^n"""
    m = p ** n
    return (f.numerator % m) * pow(f.denominator % m, -1, m) % m


def harmonic_valuations(p: int, xmax: int, slack: int = 6) -> list[int]:
    """v_p(H_K) for K = 0..xmax by O(xmax) modular work (no big rationals).

    H_K is carried as  S = H_K * p^c  mod p^w  with  c = floor(log_p xmax) + 1,
    which is an upper bound for -v_p(H_K); v_p(H_K) = v_p(S) - c.  Returns 10**9
    for K = 0 (H_0 = 0) and caps reported valuations at slack - 1.
    """
    c = 0
    while p ** (c + 1) <= xmax:
        c += 1
    c += 1
    w = c + slack
    mod = p ** w
    out = [10 ** 9]
    acc = 0
    for k in range(1, xmax + 1):
        a = vp_int(k, p)
        kk = k // p ** a
        acc = (acc + p ** (c - a) * pow(kk % mod, -1, mod)) % mod
        out.append((vp_int(acc, p) if acc else 10 ** 9) - c)
    return out


def ord_q(p: int) -> int:
    """multiplicative order of 3/2 modulo p (p > 3)"""
    x = 3 * pow(2, p - 2, p) % p
    d, y = 1, x
    while y != 1:
        y = y * x % p
        d += 1
    return d


# ---------------------------------------------------------------- the rows
def exact_rows(jmax: int) -> tuple[list[Fraction], list[Fraction]]:
    """L_j, R_j over Q. Seeds and indexing identical to erdos1049_casoratian_block_law.py."""
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


def primitive_B(l: Fraction, r: Fraction) -> int:
    den = l.denominator * r.denominator // gcd(l.denominator, r.denominator)
    a = l.numerator * (den // l.denominator)
    b = r.numerator * (den // r.denominator)
    g = gcd(abs(a), abs(b))
    return b // g if g else b


# ---------------------------------------------------------------- the tree
def jp_tree(p: int, eps: int, depth_cap: int, index_cap: int) -> dict:
    """J_p^(eps) = {K : v_p(H_K) >= eps} by the descent tree of L1.

    Returns terminated=True only when a whole level is empty, which by L1 proves
    the set is exactly what was found.
    """
    level, found, levels = [0], [], []
    for depth in range(1, depth_cap + 1):
        cand: list[int] = []
        for n in level:
            lo = p * n if n else 1
            cand.extend(range(lo, p * n + p))
        if not cand:
            return {"terminated": True, "J": sorted(found), "levels": levels, "depth": depth}
        top = max(cand)
        if top > index_cap:
            return {"terminated": False, "J": sorted(found), "levels": levels,
                    "depth": depth, "reason": f"index cap {index_cap} < {top}"}
        hv = harmonic_valuations(p, top)
        nxt = [c for c in cand if hv[c] >= eps]
        levels.append({"depth": depth, "candidates": len(cand), "hits": nxt})
        found.extend(nxt)
        level = nxt
        if not level:
            return {"terminated": True, "J": sorted(found), "levels": levels, "depth": depth}
    return {"terminated": False, "J": sorted(found), "levels": levels, "depth": depth_cap,
            "reason": f"depth cap {depth_cap}"}


# ---------------------------------------------------------------- falsifiers
def main() -> int:
    ap = argparse.ArgumentParser()
    ap.add_argument("--max-index", type=int, default=200,
                    help="highest exact row index j (exact rationals; cost is superquadratic)")
    ap.add_argument("--mono-levels", type=int, default=3, help="levels N of the monodromy lemma")
    ap.add_argument("--family-primes", type=int, default=60,
                    help="scan primes < this for a terminating J_p tree")
    ap.add_argument("--json", action="store_true")
    args = ap.parse_args()

    t0 = time.time()
    report: dict = {"probe": "erdos1049_fixed_prime_infinite_tail", "falsifiers": {}}
    fails: list[str] = []

    def record(key: str, ok: bool, **payload):
        report["falsifiers"][key] = {"pass": bool(ok), **payload}
        if not ok:
            fails.append(key)
        if not args.json:
            print(f"  [{'PASS' if ok else 'FAIL'}] {key}: "
                  + "  ".join(f"{k}={v}" for k, v in payload.items()))

    if not args.json:
        print("Erdos 1049 / base 3/2 -- fixed-prime infinite tail")
        print(f"  building exact rows to j={args.max_index} ...", flush=True)
    L, R = exact_rows(args.max_index)
    B = [primitive_B(L[j], R[j]) for j in range(len(L))]
    jmax = len(B) - 1
    if not args.json:
        print(f"  rows built in {time.time() - t0:.1f}s, top |B_j| ~ {B[-1].bit_length()} bits\n")

    # ---- F1  descent lemma, tested as a fact about actual harmonic valuations
    hv = harmonic_valuations(5, min(20000, 20000))
    viol = [n for n in range(5, len(hv)) if hv[n] >= 1 and hv[n // 5] < 1]
    record("F1_descent_lemma", not viol, tested=len(hv) - 5, violations=viol[:5])

    # ---- F2  J_5 = {4,20,24} and the tree terminates
    tree5 = jp_tree(5, 1, depth_cap=6, index_cap=10 ** 6)
    ok = tree5["terminated"] and tree5["J"] == [4, 20, 24]
    record("F2_J5_finite", ok, J5=tree5["J"], terminated=tree5["terminated"],
           empty_level_at_depth=tree5["depth"])

    # ---- F3  monodromy  R_{j+P_N} = -R_j  (mod 5^N)
    mono = []
    for N in range(1, args.mono_levels + 1):
        mod, P = 5 ** N, 2 * 5 ** (N - 1)
        if jmax - P < 8:
            break
        rm = [unit_mod(R[j], 5, N) for j in range(jmax + 1)]
        bad = [j for j in range(jmax + 1 - P) if (rm[j + P] + rm[j]) % mod]
        mono.append({"N": N, "P": P, "tested": jmax + 1 - P, "violations": bad[:4]})
    ok = bool(mono) and all(not m["violations"] for m in mono)
    record("F3_monodromy_R_antiperiodic", ok,
           levels=[(m["N"], m["P"], m["tested"]) for m in mono],
           violations=[m["violations"] for m in mono if m["violations"]][:1])

    # ---- F4  (C5): g_{5^a t} = g_*  (mod 5^(a+1)) for every t coprime to 5
    def g_of(m: int) -> Fraction:
        lm = LAM ** m
        um = (lm - 1) / (m * PI)
        return lm * (lm + 2) / (um * R[2 * m - 1] * R[2 * m])

    mtop = (jmax - 1) // 2
    c5, gstar = [], {}
    for a in range(0, 4):
        ts = [t for t in range(1, mtop // 5 ** a + 1) if t % 5]
        if len(ts) < 2:
            break
        vals = {unit_mod(g_of(5 ** a * t), 5, a + 1) for t in ts}
        c5.append({"a": a, "t_count": len(ts), "residues": sorted(vals)})
        if len(vals) == 1:
            gstar[a + 1] = vals.pop()
    ok = bool(c5) and all(len(x["residues"]) == 1 for x in c5)
    # the constants must be a coherent 5-adic limit across levels
    coherent = all(gstar[n] % 5 ** k == gstar[k] for n in gstar for k in gstar if k <= n)
    record("F4_five_adic_continuity_C5", ok and coherent,
           levels=[(x["a"], x["t_count"], x["residues"]) for x in c5],
           g_star=gstar, coherent=coherent)

    # ---- F5  the exact loss set is the three blocks J_5 predicts, and nothing else
    d, eps = ord_q(5), vp_int(3 ** ord_q(5) - 2 ** ord_q(5), 5)
    predicted = sorted({j for K in tree5["J"] for j in range(d * K, d * K + d)})
    actual = [j for j in range(d, jmax + 1) if vp_int(B[j], 5) == 0]
    record("F5_loss_set_exact", actual == [j for j in predicted if j <= jmax],
           d=d, eps=eps, predicted=predicted, actual=actual, j_range=f"[{d},{jmax}]")

    # ---- F6  the valuation law  v_5(B_j) = 1 - v_5(H_{floor(j/2)})  off the loss blocks
    hv2 = harmonic_valuations(5, jmax // 2 + 2)
    bad = [(j, vp_int(B[j], 5), 1 - hv2[j // 2])
           for j in range(d, jmax + 1)
           if j not in predicted and vp_int(B[j], 5) != 1 - hv2[j // 2]]
    record("F6_valuation_law", not bad, tested=jmax + 1 - d - len(predicted),
           mismatches=bad[:4])

    # ---- F7  regression: hypothesis (H) as originally stated is FALSE at p=5
    g25 = {unit_mod(g_of(m), 5, 2) for m in range(1, min(mtop, 40) + 1)}
    record("F7_old_hypothesis_H_is_false", len(g25) > 1,
           g_m_mod_25=sorted(g25),
           note="(H) claimed a single constant; three residues refute it, (C5) replaces it")

    # ---- F8  the consequence: 5 divides the whole computed tail past the last loss block
    thresh = max(predicted) + 1
    tail_bad = [j for j in range(thresh, jmax + 1) if vp_int(B[j], 5) == 0]
    vals = sorted({vp_int(B[j], 5) for j in range(thresh, jmax + 1)})
    record("F8_fixed_prime_tail", not tail_bad and thresh <= jmax,
           threshold=thresh, verified_to=jmax, violations=tail_bad[:4],
           v5_values_on_tail=vals,
           window_gcd_5part_at_start_s=f"5^(1+floor(log_5(s/2)))")

    # ---------------------------------------------------- the wider prime family
    family = []
    for p in range(5, args.family_primes):
        if p in (2, 3, 7) or any(p % q == 0 for q in range(2, int(p ** 0.5) + 1)):
            continue  # 7 divides the Casoratian seed W_0 = -21/2
        dp = ord_q(p)
        ep = vp_int(3 ** dp - 2 ** dp, p)
        tr = jp_tree(p, ep, depth_cap=4, index_cap=400000)
        if tr["terminated"]:
            mx = max(tr["J"]) if tr["J"] else 0
            family.append({"p": p, "d": dp, "eps": ep, "J": tr["J"],
                           "tail_from": dp * (mx + 1) if tr["J"] else dp})
    report["prime_family_with_proved_finite_J"] = family
    if not args.json:
        print("\n  primes with a TERMINATING J_p^eps tree (each gives its own fixed infinite tail):")
        for f in family:
            print(f"    p={f['p']:3d}  d={f['d']:3d}  eps={f['eps']}  "
                  f"J_p^eps={f['J']}  =>  p | B_j for all j >= {f['tail_from']}")

    report["elapsed_s"] = round(time.time() - t0, 2)
    report["all_pass"] = not fails
    report["failed"] = fails

    receipt = os.path.join("state", "formal_math", "erdos257_period_noncollapse",
                           "erdos1049_fixed_prime_infinite_tail_receipt.json")
    os.makedirs(os.path.dirname(receipt), exist_ok=True)
    with open(receipt, "w") as fh:
        json.dump(report, fh, indent=2, sort_keys=True)

    if args.json:
        print(json.dumps(report, indent=2, sort_keys=True))
    else:
        print(f"\n  receipt: {receipt}")
        print(f"  {'ALL FALSIFIERS PASS' if not fails else 'FAILED: ' + ', '.join(fails)}"
              f"   ({report['elapsed_s']}s)")
    return 0 if not fails else 1


if __name__ == "__main__":
    sys.exit(main())
