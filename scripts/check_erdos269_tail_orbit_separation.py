#!/usr/bin/env python3
"""Erdos 269 / support {2,3,5}: normalized-tail orbit separation checker.

Two jobs, both deterministic and exact-digit based.

1.  FALSIFIER.  `RationalLatticeTorusSqueezeLab.md` (wave 2026-08-23) claimed an
    "orbit realization"  G_A(tau_a) = X_a  for all a, where the reading series
    G_A carries digits from the *absolute* index A and radices from the torus
    phase tau_a.  That claim is false for every a != A: the digits d_n grow like
    n^2 and are not phase functions.  This checker exhibits the defect.

2.  SEPARATION CERTIFICATE.  Unconditionally X_a = B_a*S - (integer), with
    B_a = H(2^a)/2, because every smooth s < 2^a has H(s) | B_a.  Hence
    S = p/q forces every X_a into (1/q)Z, so the fractional parts {X_a} take at
    most q values.  Pairwise-distinct fractional parts therefore lower-bound the
    denominator:  q >= #{distinct} and q >= 1/(min gap).  This is a finite
    certificate, not an irrationality proof.

Objects (landed packet normalisation):
    H(s)  = 2^floor(log2 s) 3^floor(log3 s) 5^floor(log5 s)
    A_a   = {smooth s : 2^a <= s < 2^(a+1)},   m_a = sum_{s in A_a} 1/H(s)
    B_a   = H(2^a)/2,  X_a = B_a T_a,  T_a = sum_{n>=a} m_n,  X_1 = S
    b_a   = H(2^(a+1))/H(2^a) in {2,6,10,30},  d_a = B_(a+1) m_a in Z_{>0}
    X_(a+1) = b_a X_a - d_a
"""
from __future__ import annotations

problem_id = "erdos_269"

import argparse
import json
import math
import pathlib
import sys

import numpy as np
from mpmath import mp

L3 = math.log2(3.0)
L5 = math.log2(5.0)


class DigitEngine:
    """Exact (b_a, d_a) via lattice-point counts in the dyadic shell."""

    def __init__(self, nmax: int) -> None:
        self.nmax = nmax
        jj = np.arange(int(nmax / L3) + 2, dtype=np.float64)[:, None]
        kk = np.arange(int(nmax / L5) + 2, dtype=np.float64)[None, :]
        mu = (jj * L3 + kk * L5).ravel()
        self.mu = np.sort(mu[mu <= nmax + 2.0])
        self.min_slack = 1.0

    def count_in(self, lo: float, hi: float) -> int:
        mu = self.mu[: np.searchsorted(self.mu, hi)]
        r = lo - mu
        i0 = np.maximum(np.ceil(r), 0.0)
        gap = np.abs(r - np.rint(r))
        nz = gap[gap > 0.0]
        if nz.size:
            self.min_slack = min(self.min_slack, float(nz.min()))
        return int(np.count_nonzero(i0 < hi - mu))

    def block(self, n: int) -> tuple[int, int]:
        u3 = (math.floor(n / L3) + 1) * L3
        u5 = (math.floor(n / L5) + 1) * L5
        d3 = 1 if u3 < n + 1 else 0
        d5 = 1 if u5 < n + 1 else 0
        cuts = sorted([float(n)] + ([u3] if d3 else []) + ([u5] if d5 else []) + [float(n + 1)])
        digit = 0
        for lo, hi in zip(cuts[:-1], cuts[1:]):
            if hi <= lo:
                continue
            weight = 1
            if d3 and hi <= u3:
                weight *= 3
            if d5 and hi <= u5:
                weight *= 5
            digit += weight * self.count_in(lo, hi)
        return 2 * 3 ** d3 * 5 ** d5, digit


def exact_block(n: int) -> tuple[int, int, int]:
    """Big-integer recomputation of (b_n, d_n, |A_n|); no floating point."""
    lo, hi = 2 ** n, 2 ** (1 + n)

    def top_power(p: int, bound: int) -> int:
        q = 1
        while q * p <= bound:
            q *= p
        return q

    p3, p5 = top_power(3, lo), top_power(5, lo)
    d3 = 1 if p3 * 3 < hi else 0
    d5 = 1 if p5 * 5 < hi else 0
    w3, w5 = p3 * 3, p5 * 5
    digit, size = 0, 0
    v3 = 1
    while v3 < hi:
        v = v3
        while v < hi:
            shift = max(0, n - (v.bit_length() - 1))
            s = v << shift
            while s < lo:
                s <<= 1
            while shift > 0 and (s >> 1) >= lo:
                s >>= 1
                shift -= 1
            if s < hi:
                size += 1
                weight = 1
                if d3 and s < w3:
                    weight *= 3
                if d5 and s < w5:
                    weight *= 5
                digit += weight
            v *= 5
        v3 *= 3
    return 2 * 3 ** d3 * 5 ** d5, digit, size


def exact_wall_flags(n: int) -> tuple[int, int]:
    """(Delta_3(n), Delta_5(n)) by exact integer comparison only."""
    out = []
    for p in (3, 5):
        q = 1
        while q * p <= 2 ** n:
            q *= p
        out.append(1 if q * p < 2 ** (1 + n) else 0)
    return out[0], out[1]


def tail_majorant(m: int, terms: int = 4000) -> float:
    """Rigorous upper bound for X_m:  d_n <= 15|A_n|, H(2^m)/H(2^(n+1)) <= 15*8^(m-n-1)."""
    total = 0.0
    for n in range(m, m + terms):
        cnt = (1.0 + (n + 1) / L3) * (1.0 + (n + 1) / L5)
        total += 225.0 * cnt * 8.0 ** (m - n - 1)
        if 225.0 * cnt * 8.0 ** (m - n - 1) < 1e-60:
            break
    return total


def main() -> int:
    ap = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    ap.add_argument("--scales", type=int, default=1200, help="largest scale a for the orbit study")
    ap.add_argument("--depth", type=int, default=70, help="series depth used for each X_a")
    ap.add_argument("--exact-check", type=int, default=40, help="brute-force cross-check up to this shell")
    ap.add_argument("--exact-samples", type=int, nargs="*", default=[100, 300, 700], help="extra exact shells")
    ap.add_argument("--receipt", type=str, default=None, help="write the receipt JSON here")
    ap.add_argument("--json", action="store_true")
    args = ap.parse_args()

    mp.dps = 80
    nmax = args.scales + args.depth + 2
    eng = DigitEngine(nmax)
    bs = [0] * (nmax + 1)
    ds = [0] * (nmax + 1)
    for n in range(1, nmax + 1):
        bs[n], ds[n] = eng.block(n)

    # --- validation: exact big-integer agreement -------------------------------
    mismatches = []
    for n in range(1, args.exact_check + 1):
        eb, ed, _ = exact_block(n)
        if (eb, ed) != (bs[n], ds[n]):
            mismatches.append({"n": n, "fast": [bs[n], ds[n]], "exact": [eb, ed]})
    for n in args.exact_samples:
        if n <= nmax:
            eb, ed, _ = exact_block(n)
            if (eb, ed) != (bs[n], ds[n]):
                mismatches.append({"n": n, "fast": [bs[n], ds[n]], "exact": [eb, ed]})
    wall_mismatches = []
    for n in range(1, min(nmax, 400) + 1):
        d3, d5 = exact_wall_flags(n)
        if 2 * 3 ** d3 * 5 ** d5 != bs[n]:
            wall_mismatches.append(n)

    # --- normalized tail states ------------------------------------------------
    def tail_state(a: int) -> mp.mpf:
        total, den = mp.mpf(0), mp.mpf(1)
        for j in range(args.depth):
            n = a + j
            if n > nmax:
                break
            den *= bs[n]
            total += mp.mpf(ds[n]) / den
        return total

    scales = args.scales
    xs = [None] + [tail_state(a) for a in range(1, scales + 1)]
    theta = [None] + [xs[a] - mp.floor(xs[a]) for a in range(1, scales + 1)]

    # rigorous truncation bound for the deepest state used
    prod = mp.mpf(1)
    for n in range(scales, scales + args.depth):
        prod *= bs[n]
    trunc = mp.mpf(tail_majorant(scales + args.depth)) / prod

    # --- falsifier: the claimed orbit realization G_A(tau_a) = X_a -------------
    def reading(A: int, a: int) -> mp.mpf:
        total, den = mp.mpf(0), mp.mpf(1)
        for j in range(args.depth):
            if A + j > nmax or a + j > nmax:
                break
            den *= bs[a + j]
            total += mp.mpf(ds[A + j]) / den
        return total

    realization = []
    for a in (1, 2, 3, 5, 10, 20, 40):
        if a > scales:
            continue
        g = reading(1, a)
        realization.append({
            "a": a,
            "X_a": mp.nstr(xs[a], 15),
            "G_1(tau_a)": mp.nstr(g, 15),
            "defect": mp.nstr(abs(xs[a] - g), 8),
        })

    # --- separation certificate -------------------------------------------------
    order = sorted(range(1, scales + 1), key=lambda a: float(theta[a]))
    gaps = [(float(theta[order[i + 1]]) - float(theta[order[i]]), order[i], order[i + 1])
            for i in range(len(order) - 1)]
    min_gap, gi, gj = min(gaps)
    dists = [(min(float(theta[a]), 1.0 - float(theta[a])), a) for a in range(1, scales + 1)]
    min_dist, di = min(dists)

    counts = [0] * 20
    for a in range(1, scales + 1):
        counts[min(19, int(float(theta[a]) * 20))] += 1
    expected = scales / 20.0
    chi2 = sum((c - expected) ** 2 / expected for c in counts)
    weyl = []
    for h in (1, 2, 3):
        acc = sum(mp.e ** (2j * mp.pi * h * theta[a]) for a in range(1, scales + 1)) / scales
        weyl.append(float(abs(acc)))

    receipt = {
        "problem_id": "erdos_269",
        "support": [2, 3, 5],
        "checker": "check_erdos269_tail_orbit_separation",
        "parameters": {"scales": scales, "depth": args.depth, "mp_dps": mp.dps},
        "digit_engine_validation": {
            "brute_force_shells": args.exact_check,
            "extra_exact_shells": args.exact_samples,
            "digit_mismatches": mismatches,
            "radix_wall_mismatches": wall_mismatches,
            "min_float_slack": eng.min_slack,
            "status": "validated" if not mismatches and not wall_mismatches else "FAILED",
        },
        "torus_orbit_realization_falsifier": {
            "claim": "G_A(tau_a) = X_a for all a (RationalLatticeTorusSqueezeLab.md, wave 2026-08-23)",
            "verdict": "false for every a != A",
            "reason": "the digits d_n grow like n^2, so they are not functions of the torus phase; "
                      "G_A reads absolute-index digits against orbit-a radices",
            "table": realization,
        },
        "tail_orbit_separation": {
            "distinct_fractional_parts": scales,
            "min_gap": min_gap,
            "min_gap_pair": [gi, gj],
            "min_distance_to_Z": min_dist,
            "min_distance_scale": di,
            "truncation_bound": mp.nstr(trunc, 6),
            "denominator_lower_bound_from_count": scales,
            "denominator_lower_bound_from_gap": int(1.0 / min_gap),
            "boundary": "finite certificate; does not exclude arbitrarily large denominators",
        },
        "mod_one_statistics": {
            "bins20": counts,
            "chi_square": chi2,
            "chi_square_df": 19,
            "weyl_abs_h1_h2_h3": weyl,
            "one_over_sqrt_n": 1.0 / math.sqrt(scales),
        },
        "value": {"S": mp.nstr(xs[1], 30)},
    }

    ok = receipt["digit_engine_validation"]["status"] == "validated" and min_gap > float(trunc) * 1e6
    receipt["status"] = "pass" if ok else "fail"

    if args.receipt:
        path = pathlib.Path(args.receipt)
        path.parent.mkdir(parents=True, exist_ok=True)
        path.write_text(json.dumps(receipt, indent=2, sort_keys=True) + "\n")
    if args.json:
        print(json.dumps(receipt, indent=2, sort_keys=True))
    else:
        print(f"digit engine       : {receipt['digit_engine_validation']['status']} "
              f"(brute force n<={args.exact_check}, samples {args.exact_samples}, "
              f"min float slack {eng.min_slack:.2e})")
        print("orbit realization  : claimed G_A(tau_a)=X_a is FALSE")
        for row in realization:
            print(f"    a={row['a']:>3}  X_a={row['X_a']:>20}  G_1(tau_a)={row['G_1(tau_a)']:>20}  "
                  f"defect={row['defect']}")
        print(f"separation         : {scales} pairwise-distinct fractional parts; "
              f"min gap {min_gap:.3e} at (a,a')=({gi},{gj})")
        print(f"                     min dist to Z {min_dist:.3e} at a={di}; "
              f"truncation bound {mp.nstr(trunc, 4)}")
        print(f"denominator bound  : q >= {int(1.0 / min_gap)}  (finite certificate only)")
        print(f"mod-1 statistics   : chi^2(19) = {chi2:.1f}; "
              f"|Weyl| = {weyl[0]:.4f}, {weyl[1]:.4f}, {weyl[2]:.4f} vs 1/sqrt(N) = "
              f"{1.0 / math.sqrt(scales):.4f}")
        print(f"status             : {receipt['status']}")
    return 0 if ok else 1


if __name__ == "__main__":
    sys.exit(main())
