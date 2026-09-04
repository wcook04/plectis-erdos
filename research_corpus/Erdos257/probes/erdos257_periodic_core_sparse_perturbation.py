#!/usr/bin/env python3
"""Erdos 257: falsification probes for the periodic-core / sparse-perturbation theorem.

Theorem under test (proof note
`formal_math/erdos257_period_noncollapse/ErdosProblems/Erdos257/PeriodicCoreSparsePerturbation.md`):

  Let A0 be an infinite union of residue classes modulo m (more generally an infinite
  P-invariant support), and let S1 subset A0, S2 disjoint from A0 be sets with
  sum_{s in S1 u S2} 1/s < infinity.  Then for A = (A0 \\ S1) u S2 the value
  y_A(t) = sum_{a in A} 1/(t^a - 1) is irrational for every integer base t >= 2.

The proof is elementary (Erdos-1948 sockets forced by CRT on the periodic core, plus the
gcd-orbit summable majorant on the sparse part).  A theorem cannot be falsified by
computation, but each load-bearing lemma can, and the quantitative skeleton of the averaging
step can be measured.  This script records:

  P1  socket lemma: if j distinct primes p == 1 (mod m) exactly divide n then 2^j | tau_{A0}(n)
      for A0 a union of residue classes mod m.  Exhaustive over n <= N_MAX for many (m, R).
      Control: with primes NOT == 1 (mod m) the divisibility FAILS (counterexamples printed),
      so the hypothesis is load-bearing, not decorative.  Also the k-free supports (weak
      invariance) and the base-t socket p^{t-1} || n => t^j | tau.
  P2  AP-average divisor bound: for every Y, Lambda, a,
        sum_{n <= Y, n == a (Lambda)} d(n) <= 2 Y d(gcd(a,Lambda)) (log Y + 1) / Lambda + 2 sqrt(Y).
      Exhaustive over a grid.
  P3  gcd-orbit atom mean: for t >= 2, L, d >= 1 and T >= 1, with atoms a_N = t^{N mod d}/(t^d-1),
        (1/T) sum_{u < T} a_{L u} <= 1/d + 1/T,
      exact rationals; plus the exact full-period value g/(d (t^g - 1)), g = gcd(L, d).
  P4  the construction itself for A0 = 2N (even numbers) with the socket at positions
      j = 2, 4 (k = 4): every N in the CRT class has integral head H_N, positive tail,
      and the class mean of R_{N+k}(A0) sits under the proved envelope; the sparse part
      S = {7^k} is measured through Delta_S = R_N(S) - R_0(S) on the class N == 0 (mod 7^3).
  P5  continued-fraction sanity on five instances of the class (weak evidence, recorded as such).

Exact rational arithmetic throughout except the P5 mpmath evaluation and the P4 log envelope.
Run:  ./repo-python formal_math/probes/erdos257_periodic_core_sparse_perturbation.py [--fast]
"""
from __future__ import annotations

import argparse
import json
import math
import sys
import time
from fractions import Fraction
from math import gcd, isqrt

try:
    from sympy import factorint, isprime, primerange
except ImportError:  # pragma: no cover
    print("sympy required", file=sys.stderr)
    raise


# ----------------------------------------------------------------------------- helpers
def divisors_from_fact(fact: dict[int, int]) -> list[int]:
    divs = [1]
    for p, e in fact.items():
        divs = [d * p**i for d in divs for i in range(e + 1)]
    return divs


def tau_periodic(n: int, m: int, R: set[int], fact=None) -> int:
    """tau_{A0}(n) for A0 = {d >= 1 : d mod m in R}."""
    if fact is None:
        fact = factorint(n)
    return sum(1 for d in divisors_from_fact(fact) if d % m in R)


def tau_kfree(n: int, k: int, fact=None) -> int:
    """Number of k-free divisors, enumerated with their exponent vectors (no refactoring)."""
    if fact is None:
        fact = factorint(n)
    cnt = 0
    vecs = [()]
    items = list(fact.items())
    for _, e in items:
        vecs = [v + (i,) for v in vecs for i in range(e + 1)]
    for v in vecs:
        if all(i < k for i in v):
            cnt += 1
    return cnt


def sieve_factor(N: int) -> list[dict[int, int]]:
    """Smallest-prime-factor sieve to factor every n <= N quickly."""
    spf = list(range(N + 1))
    for i in range(2, isqrt(N) + 1):
        if spf[i] == i:
            for j in range(i * i, N + 1, i):
                if spf[j] == j:
                    spf[j] = i
    facts: list[dict[int, int]] = [dict() for _ in range(N + 1)]
    for n in range(2, N + 1):
        f: dict[int, int] = {}
        x = n
        while x > 1:
            p = spf[x]
            f[p] = f.get(p, 0) + 1
            x //= p
        facts[n] = f
    return facts


def crt(residues: list[tuple[int, int]]) -> tuple[int, int]:
    """Solve x == r_i (mod n_i) for pairwise coprime n_i.  Returns (x, prod n_i)."""
    x, mod = 0, 1
    for r, n in residues:
        # solve x + mod*t == r (mod n)
        t = ((r - x) * pow(mod, -1, n)) % n
        x += mod * t
        mod *= n
    return x % mod, mod


# ----------------------------------------------------------------------------- P1
def probe_socket_lemma(N_MAX: int) -> dict:
    facts = sieve_factor(N_MAX)
    cases = [
        (1, {0}),            # A0 = N, tau = d
        (2, {0}),            # even numbers
        (2, {1}),            # odd numbers
        (3, {1}), (3, {2}), (3, {0, 1}), (3, {1, 2}),
        (4, {1}), (4, {2}), (4, {3}), (4, {1, 3}), (4, {0, 2}),
        (5, {1}), (5, {2, 3}), (5, {0, 4}),
        (6, {1}), (6, {5}), (6, {1, 5}), (6, {2, 4}), (6, {0, 3}),
        (7, {3}), (8, {1, 7}), (9, {4}), (10, {1, 9}), (12, {5, 7}),
    ]
    out = {"n_max": N_MAX, "cases": [], "violations": 0, "controls": []}
    for m, R in cases:
        viol = 0
        checked = 0
        max_j = 0
        for n in range(1, N_MAX + 1):
            f = facts[n]
            j = sum(1 for p, e in f.items() if e == 1 and p % m == 1 % m)
            if j == 0:
                continue
            checked += 1
            max_j = max(max_j, j)
            t = tau_periodic(n, m, R, f)
            if t % (2**j) != 0:
                viol += 1
                if viol <= 3:
                    print(f"  P1 VIOLATION m={m} R={sorted(R)} n={n} fact={f} j={j} tau={t}")
        out["cases"].append({"m": m, "R": sorted(R), "checked": checked, "max_j": max_j, "violations": viol})
        out["violations"] += viol
    # control: primes not == 1 (mod m).  For m = 3, R = {1}: p = 2 exactly dividing n.
    ctrl = []
    for m, R, bad_p in [(3, {1}, 2), (3, {1}, 5), (4, {1}, 3), (5, {1}, 2), (6, {1}, 5)]:
        cnt = 0
        ex = None
        for n in range(1, N_MAX + 1):
            f = facts[n]
            if f.get(bad_p, 0) == 1:
                t = tau_periodic(n, m, R, f)
                if t % 2 != 0:
                    cnt += 1
                    if ex is None:
                        ex = (n, t)
        ctrl.append({"m": m, "R": sorted(R), "prime": bad_p, "odd_tau_count": cnt, "first_counterexample": ex})
    out["controls"] = ctrl
    # weak invariance: k-free supports at base 2 (2^j | tau) -- and failure at base 3 for squarefree.
    kfree = []
    for k in (2, 3):
        viol = 0
        checked = 0
        for n in range(1, min(N_MAX, 20000) + 1):
            f = facts[n]
            j = sum(1 for p, e in f.items() if e == 1)
            if j == 0:
                continue
            checked += 1
            if tau_kfree(n, k, f) % (2**j) != 0:
                viol += 1
        kfree.append({"k": k, "checked": checked, "violations": viol})
    out["kfree_base2"] = kfree
    # base-t socket on periodic support: p^{t-1} || n with p == 1 (mod m)  =>  t^j | tau.
    baset = []
    for t_base in (3, 4, 5):
        for m, R in [(1, {0}), (2, {0}), (3, {1}), (4, {1, 3})]:
            viol = 0
            checked = 0
            for n in range(1, N_MAX + 1):
                f = facts[n]
                j = sum(1 for p, e in f.items() if e == t_base - 1 and p % m == 1 % m)
                if j == 0:
                    continue
                checked += 1
                if tau_periodic(n, m, R, f) % (t_base**j) != 0:
                    viol += 1
            baset.append({"base": t_base, "m": m, "R": sorted(R), "checked": checked, "violations": viol})
            out["violations"] += viol
    out["base_t_socket"] = baset
    # squarefree at base 3 cannot socket: tau = 2^omega is never divisible by 3.
    out["squarefree_base3_socket_impossible"] = all(
        (2 ** len(facts[n])) % 3 != 0 for n in range(2, 5000)
    )
    return out


# ----------------------------------------------------------------------------- P2
def probe_ap_divisor_bound(Y_LIST: list[int], LAMBDAS: list[int]) -> dict:
    Ymax = max(Y_LIST)
    # divisor counts up to Ymax by sieve
    d = [0] * (Ymax + 1)
    for e in range(1, Ymax + 1):
        for n in range(e, Ymax + 1, e):
            d[n] += 1
    worst = 0.0
    checked = 0
    worst_case = None
    for Lam in LAMBDAS:
        for a in range(Lam):
            g = gcd(a, Lam) if a else Lam
            dg = sum(1 for e in range(1, g + 1) if g % e == 0)
            for Y in Y_LIST:
                s = sum(d[n] for n in range(a if a else Lam, Y + 1, Lam))
                bound = 2 * Y * dg * (math.log(Y) + 1) / Lam + 2 * math.sqrt(Y)
                ratio = s / bound
                checked += 1
                if ratio > worst:
                    worst, worst_case = ratio, (Lam, a, Y, s, bound)
    return {"checked": checked, "worst_ratio_sum_over_bound": worst, "worst_case": worst_case,
            "holds": worst <= 1.0}


# ----------------------------------------------------------------------------- P3
def probe_gcd_orbit_mean(T_MAX: int) -> dict:
    """Integer form: with den = t^d - 1 and S_T = sum_{u<T} t^{(L u) mod d},
    mean <= 1/d + 1/T  <=>  S_T * d <= den * (T + d)."""
    checked = 0
    worst = Fraction(0)
    exact_ok = True
    for t_base in (2, 3, 5):
        for d in range(1, 41):
            den = t_base**d - 1
            for L in (1, 2, 3, 4, 6, 12, 60, 420, 2520):
                g = gcd(L, d)
                period = d // g
                atoms = [t_base ** ((L * u) % d) for u in range(period)]
                if Fraction(sum(atoms), period * den) != Fraction(g, d * (t_base**g - 1)):
                    exact_ok = False
                    print(f"  P3 exact mean mismatch t={t_base} d={d} L={L}")
                S = 0
                for T in range(1, T_MAX + 1):
                    S += atoms[(T - 1) % period]
                    checked += 1
                    if S * d > den * (T + d):
                        print(f"  P3 VIOLATION t={t_base} d={d} L={L} T={T}")
                    r = Fraction(S * d, den * (T + d))
                    if r > worst:
                        worst = r
    return {"checked": checked, "worst_ratio": float(worst), "holds": worst <= 1, "full_period_formula_exact": exact_ok}


# ----------------------------------------------------------------------------- P4
def rigorous_R_upper(M: int, tau_fn, depth: int) -> tuple[Fraction, Fraction]:
    """Return (lower, upper) rigorous rational bounds for R_M = sum_{i>=1} tau(M+i) 2^{-i},
    using exact tau up to `depth` and tau(n) <= d(n) <= 2 sqrt(n) beyond."""
    head = Fraction(0)
    for i in range(1, depth + 1):
        head += Fraction(tau_fn(M + i), 2**i)
    # tail: sum_{i>depth} 2 sqrt(M+i) 2^{-i} <= 2 * 2^{-depth} * sqrt(M+depth+1) * (1 + small)
    tail_hi = Fraction(4 * (isqrt(M + depth + 1) + 1), 2**depth)
    return head, head + tail_hi


def probe_construction(samples: int, depth: int) -> dict:
    """A0 = 2N, k = 4, socket positions j = 2 (two odd primes) and j = 4 (four odd primes).
    Class: N == 0 (mod 2), N == 0 (mod 7^3) [sparse part S = {7^k}], N + 2 == p (mod p^2)
    for p in {3, 5}, N + 4 == p (mod p^2) for p in {11, 13, 17, 19}."""
    k = 4
    conds = [(0, 2), (0, 7**3)]
    socket = {2: [3, 5], 4: [11, 13, 17, 19]}
    for j, ps in socket.items():
        for p in ps:
            conds.append(((p - j) % (p * p), p * p))
    N0, Lam = crt(conds)
    if N0 == 0:
        N0 = Lam

    def tau_even(n: int) -> int:
        if n % 2:
            return 0
        f = factorint(n // 2)
        return math.prod(e + 1 for e in f.values())

    S = [7**e for e in range(1, 60)]

    rows = []
    t0 = time.time()
    for u in range(samples):
        N = N0 + u * Lam
        # head integrality
        head_terms = [tau_even(N + j) for j in range(1, k + 1)]
        head = sum(Fraction(h, 2**j) for j, h in enumerate(head_terms, start=1))
        head_int = head.denominator == 1
        lo, hi = rigorous_R_upper(N + k, tau_even, depth)
        # Delta_S exact for d <= N + depth, tail bound beyond
        dS = Fraction(0)
        for d in S:
            if d <= N:
                r = N % d
                if r == 0:
                    continue
                # (2^r - 1)/(2^d - 1) < 2^{r-d+1}: upper bound, exact only when d is small.
                dS += Fraction(pow(2, r) - 1, 2**d - 1) if d <= 64 else Fraction(1, 2 ** min(d - r - 1, 400))
            else:
                # d > N: 2^{N mod d} = 2^N and (2^N - 1)/(2^d - 1) < 2^{N-d+1}; upper bound only.
                dS += Fraction(1, 2 ** min(d - N - 1, 400))
        rows.append({"N": N, "head_terms": head_terms, "head_integral": head_int,
                     "R_lo": float(lo), "R_hi": float(hi), "Z_hi": float(hi / 2**k + dS),
                     "DeltaS": float(dS)})
    dt = time.time() - t0
    X = N0 + (samples - 1) * Lam
    mean_R_hi = sum(r["R_hi"] for r in rows) / len(rows)
    # proved envelope for the class mean (note, Lemma AP): for i small the gcd with Lam is
    # gcd(k + i, 2 * 7^3) only, d(g) <= d(2*343) = 8; envelope 8 * 8 * (log(2X) + 1) is generous.
    envelope = 8 * 8 * (math.log(2 * X) + 1)
    return {"k": k, "Lambda": Lam, "N0": N0, "samples": samples, "depth": depth,
            "all_heads_integral": all(r["head_integral"] for r in rows),
            "all_tails_positive": all(r["R_lo"] > 0 for r in rows),
            "mean_R_upper": mean_R_hi, "max_R_upper": max(r["R_hi"] for r in rows),
            "min_R_lower": min(r["R_lo"] for r in rows),
            "log_X": math.log(X), "proved_envelope_on_class_mean": envelope,
            "mean_under_envelope": mean_R_hi <= envelope,
            "min_Z_upper": min(r["Z_hi"] for r in rows), "max_DeltaS": max(r["DeltaS"] for r in rows),
            "seconds": dt, "first_rows": rows[:3]}


# ----------------------------------------------------------------------------- P5
def probe_cf(instances: dict[str, list[int]], digits: int) -> dict:
    import mpmath as mp
    mp.mp.dps = digits + 20
    out = {}
    for name, A in instances.items():
        y = mp.mpf(0)
        for a in A:
            y += 1 / (mp.mpf(2) ** a - 1)
        # continued fraction of y to 60 partial quotients
        x = y
        pq = []
        for _ in range(60):
            q = int(mp.floor(x))
            pq.append(q)
            fr = x - q
            if fr < mp.mpf(10) ** (-(digits - 5)):
                break
            x = 1 / fr
        out[name] = {"value_head": mp.nstr(y, 30), "max_partial_quotient_first60": max(pq[1:]),
                     "partial_quotients_head": pq[:20]}
    return out


def main() -> int:
    sys.stdout.reconfigure(line_buffering=True)
    ap = argparse.ArgumentParser()
    ap.add_argument("--fast", action="store_true")
    ap.add_argument("--json", type=str, default=None)
    args = ap.parse_args()
    fast = args.fast
    receipt = {"probe": "erdos257_periodic_core_sparse_perturbation", "fast": fast}

    print("P1 socket lemma ...")
    receipt["P1"] = probe_socket_lemma(60000 if fast else 300000)
    print(json.dumps({k: v for k, v in receipt["P1"].items() if k != "cases"}, indent=1))
    print("  cases:", [(c["m"], c["R"], c["max_j"], c["violations"]) for c in receipt["P1"]["cases"]])

    print("P2 AP-average divisor bound ...")
    receipt["P2"] = probe_ap_divisor_bound([1000, 5000, 20000, 60000] if fast else [1000, 5000, 20000, 100000, 300000],
                                           [1, 2, 3, 4, 6, 7, 12, 30, 36, 60, 210, 720])
    print(json.dumps(receipt["P2"], indent=1))

    print("P3 gcd-orbit atom mean ...")
    receipt["P3"] = probe_gcd_orbit_mean(200 if fast else 600)
    print(json.dumps(receipt["P3"], indent=1))

    print("P4 socket construction on 2N u {7^k} ...")
    receipt["P4"] = probe_construction(20 if fast else 80, 44 if fast else 56)
    print(json.dumps({k: v for k, v in receipt["P4"].items() if k != "first_rows"}, indent=1))
    print("  first rows:", receipt["P4"]["first_rows"])

    print("P5 continued fractions ...")
    B = 1500
    odd_sq = [n * n for n in range(1, 60, 2) if n * n <= B]
    inst = {
        "2N u {7^k}": sorted(set(range(2, B, 2)) | {7, 49, 343}),
        "2N u odd squares": sorted(set(range(2, B, 2)) | set(odd_sq)),
        "3N u {2^j}": sorted(set(range(3, B, 3)) | {2, 4, 8, 16, 32, 64, 128, 256, 512, 1024}),
        "odd \\ odd squares": sorted(set(range(1, B, 2)) - set(odd_sq)),
        "2N \\ {2^j} u {p^2 : p odd prime}": sorted((set(range(2, B, 2)) - {2, 4, 8, 16, 32, 64, 128, 256, 512, 1024})
                                                | {p * p for p in primerange(3, 39)}),
    }
    receipt["P5"] = probe_cf(inst, 450)
    print(json.dumps(receipt["P5"], indent=1))

    ok = (receipt["P1"]["violations"] == 0 and receipt["P2"]["holds"] and receipt["P3"]["holds"]
          and receipt["P4"]["all_heads_integral"] and receipt["P4"]["all_tails_positive"]
          and receipt["P4"]["mean_under_envelope"])
    receipt["all_lemma_probes_pass"] = ok
    if args.json:
        with open(args.json, "w", encoding="utf-8") as fh:
            json.dump(receipt, fh, indent=1, ensure_ascii=False)
    print("ALL LEMMA PROBES PASS:", ok)
    return 0 if ok else 1


if __name__ == "__main__":
    sys.exit(main())
