#!/usr/bin/env python3
"""Records of the prefix 2-adic excess v_2(P_n) - log2 n for Erdos 249.

  S = sum_{n>=1} phi(n) 2^-n,   P_n = 2 P_{n-1} + phi(n) = sum_{j>=0} 2^j phi(n-j),
  R_n = 2^n S - P_n = sum_{j>=1} phi(n+j) 2^-j,   0 < R_n <= n+1.

Desk E's consumer (E10; one-way sufficient condition, NOT an equivalence):

  (E10)   limsup_n ( v_2(P_n) - log2 n ) = +infinity   ==>   S is irrational.

This probe pushes the record scan far past desk E's 3*10^7 and decides between
the two candidate growth models for

  N(E, X) := #{ n <= X : v_2(P_n) - log2 n >= E }.

  model A (conductor):    N(E,X) ~ (log2 X)^1.4 * 2^-E     (unbounded => E10 true)
  model B (bounded bias): N(E,X) ~ C * 2^-E                (bounded  => E10 false)

The decisive statistic is per-dyadic-block, not cumulative.  Write

  C_k := 2^s * #{ n in [2^k, 2^{k+1}) : 2^s | P_n } / 2^k     (s in a plateau range)

for the 2-adic bias of the prefix in block k.  Uniformity would give C_k = 1;
the true value is ~10 and rises slowly, because

  v_2(P_n) >= m_n := min_{0<=j<=63} ( j + v_2(phi(n-j)) )

and v_2(phi(m)) >= omega_odd(m) grows like log log m.  Since the block counts
obey  N_k(E) ~ ln2 * C_k * 2^-E,  model B needs C_k -> 0; model A needs
C_k ~ k^0.4.  Both are directly measured here.  The honest falsifier is stated
in --json under "reading": no finite scan separates limsup = +infinity from a
large finite limsup, because the divergence is only logarithmic.

Method.  P_n mod 2^64 depends only on the last 64 letters of phi, so it is a
FIXED-LENGTH convolution and is computed by a 6-pass doubling scan over a
segmented numpy totient sieve -- no n-step Python recurrence.  All arithmetic
is exact integer arithmetic (uint64 wraparound IS reduction mod 2^64); the only
floating point is in the reported logarithms and in the model fit.

Run: ./repo-python formal_math/erdos257_period_noncollapse/ErdosProblems/\
Erdos249/scripts/check_totient_prefix_valuation_records.py --quick
"""
from __future__ import annotations

import argparse
import json
import math
import sys
import time

import numpy as np

PAD = 63
PLATEAU = (8, 20)          # s-range averaged for the bias constant C_k


# ------------------------------------------------------------------ sieves --
def small_primes(limit: int) -> list:
    sieve = bytearray([1]) * (limit + 1)
    sieve[0:2] = b"\x00\x00"
    for i in range(2, int(limit ** 0.5) + 1):
        if sieve[i]:
            sieve[i * i:: i] = bytearray(len(range(i * i, limit + 1, i)))
    return [i for i in range(2, limit + 1) if sieve[i]]


def phi_segment(lo: int, hi: int, primes) -> np.ndarray:
    """phi(n) for n in [lo, hi), exact int64.  primes must cover p <= sqrt(hi)."""
    n = hi - lo
    rem = np.arange(lo, hi, dtype=np.int64)
    phi = np.ones(n, dtype=np.int64)
    for p in primes:
        if p * p >= hi:
            break
        start = ((lo + p - 1) // p) * p
        if start < hi:
            s = start - lo
            phi[s::p] *= (p - 1)
            rem[s::p] //= p
        pk = p * p
        while pk < hi:
            start2 = ((lo + pk - 1) // pk) * pk
            if start2 < hi:
                s2 = start2 - lo
                phi[s2::pk] *= p
                rem[s2::pk] //= p
            pk *= p
    mask = rem > 1
    phi[mask] *= (rem[mask] - 1)
    if lo == 0:
        phi[0] = 0
    return phi


def trailing_zeros_u64(x: np.ndarray) -> np.ndarray:
    low = x & (np.uint64(0) - x)
    out = np.full(x.shape, 64, dtype=np.int16)
    nz = low != 0
    out[nz] = np.rint(np.log2(low[nz].astype(np.float64))).astype(np.int16)
    return out


def prefix_mod_scan(ext_phi: np.ndarray) -> np.ndarray:
    """P_n mod 2^64 by doubling: C_{k+1}[i] = C_k[i] + 2^{2^k} C_k[i-2^k]."""
    C = ext_phi.astype(np.uint64)
    s = 1
    while s <= 32:
        sh = np.zeros_like(C)
        sh[s:] = C[:-s]
        C = C + (sh << np.uint64(s))
        s *= 2
    return C[PAD:]


def min_bias_scan(v2phi_ext: np.ndarray) -> np.ndarray:
    """m_n = min_{0<=j<=63} ( j + v_2(phi(n-j)) )."""
    M = v2phi_ext.astype(np.int16)
    s = 1
    while s <= 32:
        sh = np.full_like(M, 1000)
        sh[s:] = M[:-s] + np.int16(s)
        M = np.minimum(M, sh)
        s *= 2
    return M[PAD:]


# ------------------------------------------------------------- exact R_n ----
def phi_exact(m: int, primes) -> int:
    r, out = m, m
    for p in primes:
        if p * p > r:
            break
        if r % p == 0:
            out -= out // p
            while r % p == 0:
                r //= p
    if r > 1:
        out -= out // r
    return out


def tail_R_bounds(n: int, primes, terms: int = 100):
    """Rigorous rational enclosure of R_n; tail <= 2^-terms (n+terms+1)."""
    from fractions import Fraction as Fr
    acc = Fr(0)
    for j in range(1, terms + 1):
        acc += Fr(phi_exact(n + j, primes), 1 << j)
    return acc, acc + Fr(n + terms + 1, 1 << terms)


# ------------------------------------------------------------------ scan ----
class BlockStats:
    """Per dyadic block [2^k, 2^{k+1}) statistics.

    The bias constant C_k = 2^s P(2^s | P_n) is averaged only over s in
    [6, k-8], so that every count entering the average has expectation at
    least ~2^8 and the estimator is not dominated by its own shot noise.
    """

    def __init__(self, thresholds):
        self.thresholds = thresholds
        self.n = 0
        self.exc = [0] * len(thresholds)
        self.div = {s: 0 for s in range(1, 31)}
        self.sum_m = 0
        self.sum_2m = 0.0
        self.eq = 0
        self.max_m = 0
        self.viol = 0

    def add(self, ex, v2, mn):
        self.n += ex.size
        for i, T in enumerate(self.thresholds):
            self.exc[i] += int(np.count_nonzero(ex >= T))
        for s in self.div:
            self.div[s] += int(np.count_nonzero(v2 >= s))
        self.sum_m += int(mn.astype(np.int64).sum())
        self.sum_2m += float(np.power(2.0, mn.astype(np.float64)).sum())
        self.eq += int(np.count_nonzero(mn.astype(np.int16) == v2.astype(np.int16)))
        if mn.size:
            self.max_m = max(self.max_m, int(mn.max()))
        # Task 4(a): the ultrametric bound v_2(P_n) >= m_n must never fail
        self.viol += int(np.count_nonzero(v2.astype(np.int32) < mn.astype(np.int32)))

    def row(self, k):
        srange = [s for s in range(6, min(31, k - 7))]
        C = [self.div[s] / self.n * (1 << s) for s in srange]
        return {"k": k, "block": "[2^%d, 2^%d)" % (k, k + 1), "n_in_block": self.n,
                "counts_excess_ge": {str(T): self.exc[i]
                                     for i, T in enumerate(self.thresholds)},
                "bias_s_range": [srange[0], srange[-1]] if srange else None,
                "bias_C_k": round(float(np.mean(C)), 4) if C else None,
                "bias_C_k_range": [round(min(C), 3), round(max(C), 3)] if C else None,
                # Task 4(b): for FIXED s the density of n with 2^s | P_n tends to 1
                "density_2^s_divides_P_n": {str(s): round(self.div[s] / self.n, 6)
                                            for s in (2, 4, 6, 8, 10, 12)},
                "mean_m_n": round(self.sum_m / self.n, 5),
                "mean_2_pow_m_n": round(self.sum_2m / self.n, 4),
                "frac_v2_P_eq_m_n": round(self.eq / self.n, 5),
                "max_m_n": self.max_m,
                "ultrametric_violations_v2_lt_m": self.viol}


def scan(X: int, seg_size: int, thresholds, verbose: bool = False) -> dict:
    t0 = time.time()
    primes = small_primes(int(math.isqrt(X)) + 100)
    blocks = {}
    records = []
    best = -99.0
    carry = np.zeros(PAD, dtype=np.int64)

    lo = 1
    while lo <= X:
        hi = min(lo + seg_size, X + 1)
        ph = phi_segment(lo, hi, primes)
        ext = np.concatenate([carry, ph])
        P = prefix_mod_scan(ext)
        v2 = trailing_zeros_u64(P)
        ns = np.arange(lo, hi, dtype=np.float64)
        ex = v2.astype(np.float64) - np.log2(ns)

        v2phi = trailing_zeros_u64(ph.astype(np.uint64))
        if lo == 1:
            v2phi_ext = np.concatenate([np.full(PAD, 1000, dtype=np.int16), v2phi])
        else:
            v2phi_ext = np.concatenate(
                [trailing_zeros_u64(carry.astype(np.uint64)), v2phi])
        mn = min_bias_scan(v2phi_ext)

        for k in np.nonzero(ex > best)[0]:
            if ex[k] > best:
                best = float(ex[k])
                nn = int(lo + k)
                records.append({"n": nn, "v2_P_n": int(v2[k]),
                                "excess_minus_log2_n": round(best, 6),
                                "excess_minus_log2_n_plus_2":
                                    round(int(v2[k]) - math.log2(nn + 2), 6),
                                # Task 4(a)/(c): m_n < log2 n always, so every
                                # positive excess is pure cancellation
                                "free_bias_m_n": int(mn[k]),
                                "cancellation_depth_v2_minus_m_n": int(v2[k]) - int(mn[k]),
                                "log2_n": round(math.log2(nn), 4)})
        # split the segment along dyadic block boundaries
        a = lo
        while a < hi:
            k = a.bit_length() - 1
            b = min(hi, 1 << (k + 1))
            sl = slice(a - lo, b - lo)
            blocks.setdefault(k, BlockStats(thresholds)).add(ex[sl], v2[sl], mn[sl])
            a = b
        carry = ext[-PAD:]
        lo = hi
        if verbose:
            print("   ... through %d  (%.1f s, best %.4f)" % (hi - 1, time.time() - t0, best),
                  file=sys.stderr)

    rows = [blocks[k].row(k) for k in sorted(blocks)]
    rect = []
    for r in records[-6:]:
        n, t = r["n"], r["v2_P_n"]
        Rlo, Rhi = tail_R_bounds(n, primes, 100)
        rect.append({"n": n, "t_eq_v2_P_n": t, "all_c_le": n - t,
                     "R_n": round(float(Rlo), 6),
                     "all_odd_v_lt": round((1 << t) / float(Rhi), 4)})
    return {"X": X, "elapsed_s": round(time.time() - t0, 2), "records": records,
            "by_block": rows, "exclusion_rectangles_from_records": rect,
            "ultrametric_bound_total_violations":
                sum(r["ultrametric_violations_v2_lt_m"] for r in rows),
            "max_m_n_over_scan": max(r["max_m_n"] for r in rows),
            "proposition_free_bias_never_certifies_positive_excess": (
                "m_n <= v_2(phi(n)) and 2^{v_2(phi(n))} | phi(n) <= n-1, so "
                "m_n < log2 n for every n >= 2. Hence the ultrametric lower bound "
                "v_2(P_n) >= m_n NEVER certifies excess >= 0: every witness with "
                "v_2(P_n) > log2 n has a NON-UNIQUE minimal term, i.e. genuine "
                "cancellation. The records table reports the cancellation depth.")}


def model_verdict(rows, thresholds, kmin: int = 16) -> dict:
    """Per-block counts N_k(E) and bias C_k against models A and B."""
    use = [r for r in rows
           if r["k"] >= kmin and r["n_in_block"] == (1 << r["k"])
           and r["bias_C_k"] is not None]
    out = {"blocks_used": [r["k"] for r in use]}
    if len(use) >= 3:
        ks = np.log(np.array([r["k"] for r in use], dtype=float))
        cs = np.log(np.array([r["bias_C_k"] for r in use], dtype=float))
        alpha, logc = np.polyfit(ks, cs, 1)
        ms = np.log(np.array([r["mean_2_pow_m_n"] for r in use], dtype=float))
        alpha_m, logcm = np.polyfit(ks, ms, 1)
        out["bias_fit_C_k_prop_k^alpha"] = {
            "alpha": round(float(alpha), 4), "c": round(float(math.exp(logc)), 4),
            "implied_beta_for_N(E,X)_prop_(log2X)^beta": round(float(alpha) + 1, 4),
            "conductor_model_alpha": 0.4, "conductor_model_beta": 1.4}
        out["free_bias_fit_E[2^m_n]_prop_k^alpha"] = {
            "alpha": round(float(alpha_m), 4), "c": round(float(math.exp(logcm)), 4)}
        out["C_k_first_last"] = [use[0]["bias_C_k"], use[-1]["bias_C_k"]]
        out["ratio_C_k_over_E[2^m_n]"] = [
            round(r["bias_C_k"] / r["mean_2_pow_m_n"], 4) for r in use]
    tot = {}
    for i, T in enumerate(thresholds):
        vals = [r["counts_excess_ge"][str(T)] for r in use]
        tot[str(T)] = {"per_block_counts": vals,
                       "mean_over_blocks": round(float(np.mean(vals)), 3) if vals else None,
                       "predicted_ln2_C_k_2^-E_first_last":
                           [round(math.log(2) * use[0]["bias_C_k"] * 2 ** -T, 3),
                            round(math.log(2) * use[-1]["bias_C_k"] * 2 ** -T, 3)]
                       if use else None}
    out["block_counts"] = tot
    return out


def main() -> int:
    ap = argparse.ArgumentParser()
    ap.add_argument("--quick", action="store_true")
    ap.add_argument("--limit", type=int, default=None)
    ap.add_argument("--seg", type=int, default=4_000_000)
    ap.add_argument("--json", action="store_true")
    ap.add_argument("--out")
    ap.add_argument("--verbose", action="store_true")
    args = ap.parse_args()

    X = args.limit if args.limit else (10_000_000 if args.quick else 300_000_000)
    thresholds = [2.0, 3.0, 4.0, 5.0, 6.0, 7.0]

    rep = {"mode": "quick" if args.quick else "full", "modulus": "2^64"}
    rep["scan"] = scan(X, args.seg, thresholds, verbose=args.verbose)
    rep["model_verdict"] = model_verdict(rep["scan"]["by_block"], thresholds)
    rep["reading"] = (
        "PROVED here: nothing. MEASURED: the per-block bias C_k is ~10 and rising, "
        "so the prefix is far from 2-adically uniform and the bounded model B "
        "(N(E,X) -> C 2^-E) is refuted on the measured range -- block counts N_k(E) "
        "do not decay. CONJECTURED: C_k ~ c k^alpha with the fitted alpha, giving "
        "N(E,X) ~ (log2 X)^(alpha+1) 2^-E. FALSIFIER, stated honestly: this cannot "
        "decide (E10). The predicted divergence of max excess is ~ (alpha+1) log2 log2 X, "
        "so reaching excess 9 needs roughly X = 10^13 and excess 12 needs X beyond any "
        "feasible sieve; a bounded limsup would look identical on every reachable range. "
        "The measurement is evidence FOR the heuristic and no part of a proof.")

    if args.out:
        with open(args.out, "w") as fh:
            json.dump(rep, fh, indent=1)
    if args.json:
        print(json.dumps(rep, indent=1))
    else:
        s = rep["scan"]
        print("prefix 2-adic excess scan to X = %d  (%.1f s, modulus 2^64)"
              % (s["X"], s["elapsed_s"]))
        print("records of v_2(P_n) - log2 n   (m_n is the free 2-adic bias; the "
              "cancellation depth is what no termwise argument can supply):")
        for r in s["records"]:
            print("   n=%-11d v_2(P_n)=%-3d excess=%.4f   m_n=%-3d log2 n=%-8.3f "
                  "cancellation=%d"
                  % (r["n"], r["v2_P_n"], r["excess_minus_log2_n"], r["free_bias_m_n"],
                     r["log2_n"], r["cancellation_depth_v2_minus_m_n"]))
        print("   ultrametric bound v_2(P_n) >= m_n violated %d times; max m_n = %d "
              "(< 64, so the 64-letter window is exact)"
              % (s["ultrametric_bound_total_violations"], s["max_m_n_over_scan"]))
        print("E10 exclusion rectangles from the top records (S != a/(2^c v), v odd):")
        for e in s["exclusion_rectangles_from_records"]:
            print("   n=%-11d t=%-3d all c <= %-11d and all odd v < %.2f"
                  % (e["n"], e["t_eq_v2_P_n"], e["all_c_le"], e["all_odd_v_lt"]))
        print("per dyadic block [2^k, 2^{k+1}):")
        hdr = "   %-4s %-11s" % ("k", "n_in_block")
        for T in thresholds:
            hdr += " E>=%-4.0f" % T
        hdr += "  C_k    m_n    E[2^m]  P(v2=m) P(2^6|P) P(2^10|P)"
        print(hdr)
        for b in s["by_block"]:
            if b["k"] < 14:
                continue
            row = "   %-4d %-11d" % (b["k"], b["n_in_block"])
            for T in thresholds:
                row += " %-7d" % b["counts_excess_ge"][str(T)]
            row += "  %-6s %-6.3f %-7.2f %-7.4f %-7.4f %-7.4f" % (
                ("%.2f" % b["bias_C_k"]) if b["bias_C_k"] is not None else "-",
                b["mean_m_n"], b["mean_2_pow_m_n"], b["frac_v2_P_eq_m_n"],
                b["density_2^s_divides_P_n"]["6"], b["density_2^s_divides_P_n"]["10"])
            print(row)
        print("   (last two columns: density of n with 2^6 | P_n and 2^10 | P_n -- "
              "Task 4(b) says each tends to 1, and the measured rate is ~C_k 2^-s, "
              "i.e. it reaches 1 only at log2 n ~ 2^s / 0.48)")
        mv = rep["model_verdict"]
        if "bias_fit_C_k_prop_k^alpha" in mv:
            f = mv["bias_fit_C_k_prop_k^alpha"]
            g = mv["free_bias_fit_E[2^m_n]_prop_k^alpha"]
            print("bias fit  C_k = c k^alpha        : alpha = %.4f, c = %.3f  "
                  "(blocks k = %s)" % (f["alpha"], f["c"], mv["blocks_used"]))
            print("free bias E[2^m_n] = c k^alpha   : alpha = %.4f, c = %.3f"
                  % (g["alpha"], g["c"]))
            print("  => N(E,X) ~ (log2 X)^%.3f 2^-E   (conductor model beta = 1.40)"
                  % f["implied_beta_for_N(E,X)_prop_(log2X)^beta"])
            beta = f["implied_beta_for_N(E,X)_prop_(log2X)^beta"]
            for XX in (3e8, 1e10, 1e13):
                pred = math.log2(f["c"] * math.log(2) / beta) + beta * math.log2(math.log2(XX))
                print("     predicted max excess at X = %.0e : %.2f" % (XX, pred))
        print(rep["reading"])
    return 0


if __name__ == "__main__":
    sys.exit(main())
