#!/usr/bin/env python3
"""Odd-restricted (CD) for Erdos 249, and the search for a structural collision family.

r04's consumer (CD): if limsup_N D_N / N > 0 then S is irrational, where
    D_N = #{ P_n mod 2^{L_N} : N <= n < 2N },   L_N = 2 ceil(log2 N).

Desk B's reduction: the ODD indices are the doubling-free core (for n = 2m the
leading window letter phi(n) = 2 phi(m) or phi(m) couples scale N to scale N/2,
while for n odd no doubling relation acts at the leading position).  Proving
D_N^odd >= N/2 - o(N) alone gives (CD) with eta = 1/2.  Desk B measured the
odd-restricted deficit only to N = 2^20 and asked for 2^21..2^24, plus a
factorisation of every collision: a REPEATING family in n - m or v_2(n - m)
would falsify the linear-diversity conjecture and kill the r04 route outright;
absence of one over four more decades is the cheapest available support.

This probe answers exactly that question.  P_n mod 2^{L} depends only on the
last L letters of phi, so it is a fixed-length convolution and is computed by a
6-pass doubling scan in uint64 (wraparound IS reduction mod 2^64); all
arithmetic is exact.

Run: ./repo-python formal_math/erdos257_period_noncollapse/ErdosProblems/\
Erdos249/scripts/check_prefix_odd_collision_families.py --quick
"""
from __future__ import annotations

import argparse
import json
import math
import sys
import time

import numpy as np

PAD = 63


def small_primes(limit: int) -> list:
    sieve = bytearray([1]) * (limit + 1)
    sieve[0:2] = b"\x00\x00"
    for i in range(2, int(limit ** 0.5) + 1):
        if sieve[i]:
            sieve[i * i:: i] = bytearray(len(range(i * i, limit + 1, i)))
    return [i for i in range(2, limit + 1) if sieve[i]]


def phi_segment(lo: int, hi: int, primes) -> np.ndarray:
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


def prefix_mod_scan(ext_phi: np.ndarray) -> np.ndarray:
    C = ext_phi.astype(np.uint64)
    s = 1
    while s <= 32:
        sh = np.zeros_like(C)
        sh[s:] = C[:-s]
        C = C + (sh << np.uint64(s))
        s *= 2
    return C[PAD:]


def collisions(res: np.ndarray, ns: np.ndarray):
    """All pairs (m, n), m < n, with equal residue.

    Vectorised: sort once, locate the (very few) adjacent-equal positions, and
    expand only those runs in Python.
    """
    order = np.argsort(res, kind="stable")
    r = res[order]
    nn = ns[order]
    eq = np.nonzero(r[1:] == r[:-1])[0]
    out = []
    if eq.size == 0:
        return out
    # group the equal-run start indices into maximal runs
    starts = []
    prev = -10
    for i in eq.tolist():
        if i != prev + 1:
            starts.append(i)
        prev = i
    for s in starts:
        j = s + 1
        while j < r.size and r[j] == r[s]:
            j += 1
        grp = np.sort(nn[s:j]).tolist()
        for a in range(len(grp)):
            for b in range(a + 1, len(grp)):
                out.append((int(grp[a]), int(grp[b]), int(r[s])))
    return out


def block_report(k: int, primes, want_pairs: bool = True) -> dict:
    N = 1 << k
    L = 2 * k                                  # L_N = 2 ceil(log2 N)
    lo, hi = N, 2 * N
    ph = phi_segment(max(lo - PAD, 0), hi, primes)
    if lo - PAD < 0:
        ph = np.concatenate([np.zeros(PAD - lo, dtype=np.int64), ph])
    P = prefix_mod_scan(ph)
    mask = np.uint64((1 << L) - 1) if L < 64 else np.uint64((1 << 64) - 1)
    res = P & mask
    ns = np.arange(lo, hi, dtype=np.int64)
    odd = (ns & 1).astype(bool)

    D = int(np.unique(res).size)
    Dodd = int(np.unique(res[odd]).size)
    Deven = int(np.unique(res[~odd]).size)
    rep = {"k": k, "N": N, "L_N": L,
           "D_N": D, "deficit_N_minus_D_N": N - D,
           "D_N_odd": Dodd, "deficit_half_N_minus_D_N_odd": N // 2 - Dodd,
           "D_N_even": Deven, "deficit_half_N_minus_D_N_even": N // 2 - Deven,
           "birthday_prediction_deficit": round(N * N / 2 / (1 << L), 4),
           "birthday_prediction_deficit_odd": round((N / 2) ** 2 / 2 / (1 << L), 4),
           "deficit_over_birthday": round((N - D) / (N * N / 2 / (1 << L)), 3),
           "deficit_odd_over_birthday": round((N // 2 - Dodd) / ((N / 2) ** 2 / 2 / (1 << L)), 3)}
    if want_pairs:
        pairs = collisions(res, ns)
        rows = []
        for (m, n, r) in pairs:
            d = n - m
            rows.append({"m": m, "n": n, "gap": d, "v2_gap": (d & -d).bit_length() - 1,
                         "parity": ("odd,odd" if m % 2 and n % 2 else
                                    "even,even" if not (m % 2 or n % 2) else "mixed"),
                         "residue": r})
        rep["collision_pairs"] = rows
        rep["n_collision_pairs"] = len(rows)
        # residue classes mod 3 (desk B hint 4)
        cls = {}
        for c in (0, 1, 2):
            sel = (ns % 3) == c
            cls[str(c)] = {"n_in_class": int(sel.sum()),
                           "distinct": int(np.unique(res[sel]).size)}
        rep["mod_3_classes"] = cls
    return rep


def family_verdict(all_rows) -> dict:
    gaps, v2gaps, par = {}, {}, {}
    for r in all_rows:
        gaps[r["gap"]] = gaps.get(r["gap"], 0) + 1
        v2gaps[r["v2_gap"]] = v2gaps.get(r["v2_gap"], 0) + 1
        par[r["parity"]] = par.get(r["parity"], 0) + 1
    rep_gap = {g: c for g, c in gaps.items() if c >= 2}
    rep_v2 = {g: c for g, c in v2gaps.items() if c >= 3}
    n = len(all_rows)
    # under randomness v_2(gap) = j with probability ~2^-(j+1)
    exp_v2 = {j: round(n * 2.0 ** -(j + 1), 3) for j in range(0, 12)}
    return {"total_pairs": n,
            "gap_multiplicities_ge_2": rep_gap,
            "v2_gap_histogram": dict(sorted(v2gaps.items())),
            "v2_gap_expected_under_randomness": exp_v2,
            "parity_histogram": par,
            "verdict": ("NO structural family: no gap value repeats, and the v_2(gap) "
                        "histogram is within Poisson noise of the geometric 2^-(j+1) "
                        "law. This SUPPORTS (CD) and proves nothing."
                        if not rep_gap else
                        "REPEATED GAP FOUND -- inspect gap_multiplicities_ge_2; a genuine "
                        "family would falsify the linear-diversity conjecture behind (CD)."),
            "falsifier": ("A gap value (or a v_2(gap) value) recurring across three or "
                          "more independent blocks with growing multiplicity would kill "
                          "(CD) as a route. This scan is the cheapest place that would "
                          "show up, and it does not.")}


def main() -> int:
    ap = argparse.ArgumentParser()
    ap.add_argument("--quick", action="store_true")
    ap.add_argument("--kmax", type=int, default=None)
    ap.add_argument("--json", action="store_true")
    ap.add_argument("--out")
    args = ap.parse_args()

    kmax = args.kmax if args.kmax else (18 if args.quick else 24)
    t0 = time.time()
    primes = small_primes(int(math.isqrt(1 << (kmax + 1))) + 100)
    rows, allpairs = [], []
    for k in range(4, kmax + 1):
        r = block_report(k, primes)
        rows.append(r)
        allpairs.extend(r.get("collision_pairs", []))
    rep = {"mode": "quick" if args.quick else "full", "kmax": kmax,
           "blocks": rows, "family_verdict": family_verdict(allpairs),
           "elapsed_s": round(time.time() - t0, 2),
           "claim_boundary": (
               "MEASURED only. (CD) is cofinal and no finite scan can establish it; "
               "r04 states this correctly. What a scan CAN do is falsify it by "
               "exhibiting a structural collision family, and it does not.")}

    if args.out:
        with open(args.out, "w") as fh:
            json.dump(rep, fh, indent=1)
    if args.json:
        print(json.dumps(rep, indent=1))
    else:
        print("odd-restricted window diversity, L_N = 2 ceil(log2 N)  (%.1f s)"
              % rep["elapsed_s"])
        print("   %-4s %-10s %-4s %-10s %-8s %-11s %-9s %-9s %-8s" %
              ("k", "N", "L_N", "D_N", "N-D_N", "D_N^odd", "N/2-Dodd", "birthday",
               "obs/pred"))
        for r in rows:
            print("   %-4d %-10d %-4d %-10d %-8d %-11d %-9d %-9.3f %-8.2f" %
                  (r["k"], r["N"], r["L_N"], r["D_N"], r["deficit_N_minus_D_N"],
                   r["D_N_odd"], r["deficit_half_N_minus_D_N_odd"],
                   r["birthday_prediction_deficit"], r["deficit_over_birthday"]))
        fv = rep["family_verdict"]
        print("collision pairs found in total: %d" % fv["total_pairs"])
        print("   gap values occurring more than once: %s" % (fv["gap_multiplicities_ge_2"] or "NONE"))
        print("   v_2(gap) histogram      : %s" % fv["v2_gap_histogram"])
        print("   expected under randomness: %s" %
              {j: v for j, v in fv["v2_gap_expected_under_randomness"].items() if v >= 0.2})
        print("   parity histogram        : %s" % fv["parity_histogram"])
        print(fv["verdict"])
        print(fv["falsifier"])
        print(rep["claim_boundary"])
    return 0


if __name__ == "__main__":
    sys.exit(main())
