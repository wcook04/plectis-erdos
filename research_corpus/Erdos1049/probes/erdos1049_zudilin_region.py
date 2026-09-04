"""Erdős #1049: the rational-base region of the Zudilin (14,12,14;27) homogenisation.

Region: reduced bases a/b (a > b >= 1 coprime) with theta := log b / log a < theta*,
theta* = C_0 / C_1 with C_1 = 1091/2, C_0 = 266 - (3/pi^2)(225 - J),
J = sum over the thirteen omega = 1 intervals [u, v) of (psi_1(u) - psi_1(v)),
psi_1(x) = sum_{k >= 0} 1/(k + x)^2 (trigamma).  Everything at mp.dps = 60.

Outputs (stdout and a JSON receipt):
  * theta* to 50 digits (mpmath polygamma, cross-checked by nsum of the series to
    48 digits) and a rigorous rational bracket from finite trigamma sums;
  * every coprime a/b with a <= 60 inside the region, with its margin
    theta* - log b / log a, and the closest misses;
  * the base 3/2: theta = log 2 / log 3, gap, and the value mu = C_1/C_0 would
    have to take (mu < log 3 / log 2 = 1.585 < 2, impossible for an
    irrationality-exponent bound of an irrational number);
  * the Lean-facing rational certificate: the smallest truncation K such that
    the finite rational sum J_K (k < K) together with pi > 157/50 already gives
    C_0 > 88371/400 = (81/200) C_1.
"""
from __future__ import annotations

import json
import math
import os
import sys
from fractions import Fraction as Fr

from mpmath import mp, mpf, log, pi, polygamma, nstr

mp.dps = 60

AL0, AL1, AL2, BE = 14, 12, 14, 27
C00, C01, C11, C21, C12, C22 = AL0 + AL1 + AL2 - BE, AL0, AL1, AL2, BE - AL1, BE - AL2
M_DIR = max(C00, C01, C11, C21, C12, C22)
C1 = Fr((AL0 + AL1 + AL2) * BE) - Fr(AL1 ** 2 + AL2 ** 2 + BE ** 2, 2)
C0_POLY = Fr(AL1 ** 2, 2) + AL0 * AL1 + (BE - AL2) * (AL2 - AL1)
assert C1 == Fr(1091, 2) and C0_POLY == 266 and M_DIR == 15


def omega(x: Fr) -> int:
    fl = lambda c: (c * x).numerator // (c * x).denominator
    return max(0, fl(C21) + fl(C22) - fl(C11) - fl(C12), fl(C01) + fl(C21) - fl(C00) - fl(C12))


def omega_intervals():
    bps = sorted({Fr(k, c) for c in (C00, C01, C11, C21, C12, C22) for k in range(c + 1)})
    ints = []
    for u, v in zip(bps, bps[1:]):
        w = omega((u + v) / 2)
        assert w in (0, 1)
        if w == 1:
            if ints and ints[-1][1] == u:
                ints[-1] = (ints[-1][0], v)
            else:
                ints.append((u, v))
    return ints


INTS = omega_intervals()
assert len(INTS) == 13
PAPER = "[1/14,1/12) [1/7,1/6) [3/14,1/4) [2/7,1/3) [5/14,2/5) [3/7,7/15) [1/2,8/15) [4/7,3/5) [9/14,2/3) [5/7,11/15) [11/14,4/5) [6/7,13/15) [13/14,14/15)"
assert " ".join(f"[{u},{v})" for u, v in INTS) == PAPER


def psi1(x: Fr):
    return polygamma(1, mpf(x.numerator) / x.denominator)


J = sum(psi1(u) - psi1(v) for u, v in INTS)
C0 = mpf(C0_POLY.numerator) / C0_POLY.denominator - 3 / pi ** 2 * (M_DIR ** 2 - J)
C1m = mpf(C1.numerator) / C1.denominator
THETA = C0 / C1m
MU = C1m / C0


def partial_J(K: int) -> Fr:
    """Exact rational lower bound: sum_{k<K} (1/(k+u)^2 - 1/(k+v)^2) over the intervals."""
    tot = Fr(0)
    for u, v in INTS:
        for k in range(K):
            tot += 1 / (k + u) ** 2 - 1 / (k + v) ** 2
    return tot


def tail_upper(K: int) -> Fr:
    """Rational upper bound for the tail sum_{k>=K} (1/(k+u)^2 - 1/(k+v)^2).

    For u < v: 1/(k+u)^2 - 1/(k+v)^2 <= 2(v-u)/(k+u)^3 and
    sum_{k>=K} 1/(k+u)^3 <= 1/(2 (K-1+u)^2)  (integral comparison, K >= 1)."""
    tot = Fr(0)
    for u, v in INTS:
        tot += (v - u) / (K - 1 + u) ** 2
    return tot


def main() -> int:
    out = {}
    print("theta* = C0/C1 =", nstr(THETA, 50))
    print("mu     = C1/C0 =", nstr(MU, 40), "  (Zudilin 2004 Theorem 1: 2.46497868...)")
    print("C0 =", nstr(C0, 40), "  J =", nstr(J, 40))
    out["theta_star"] = nstr(THETA, 50)
    out["mu"] = nstr(MU, 40)
    out["C0"] = nstr(C0, 40)
    out["C1"] = str(C1)
    out["J"] = nstr(J, 40)

    # Independent 50-digit cross-check of J by direct series summation (nsum), and a
    # rigorous rational bracket from finite sums with the integral tail bound.
    from mpmath import nsum, inf
    J_series = sum(nsum(lambda k: 1 / (k + mpf(u.numerator) / u.denominator) ** 2 - 1 / (k + mpf(v.numerator) / v.denominator) ** 2, [0, inf]) for u, v in INTS)
    print("J by nsum of the trigamma series:", nstr(J_series, 50), " |diff| =", nstr(abs(J - J_series), 5))
    assert abs(J - J_series) < mpf(10) ** -48
    out["J_nsum_cross_check"] = nstr(J_series, 50)
    K = 1000
    Jlo, Jhi = partial_J(K), partial_J(K) + tail_upper(K)
    th_lo = (mpf(C0_POLY.numerator) / C0_POLY.denominator - 3 / pi ** 2 * (M_DIR ** 2 - mpf(Jlo.numerator) / Jlo.denominator)) / C1m
    th_hi = (mpf(C0_POLY.numerator) / C0_POLY.denominator - 3 / pi ** 2 * (M_DIR ** 2 - mpf(Jhi.numerator) / Jhi.denominator)) / C1m
    print(f"rational finite-sum bracket with K={K}: {nstr(th_lo, 20)} < theta* < {nstr(th_hi, 20)}")
    assert th_lo < THETA < th_hi
    out["bracket_K"] = K
    out["theta_lower_finite"] = nstr(th_lo, 20)
    out["theta_upper_finite"] = nstr(th_hi, 20)

    # Region enumeration a <= 60
    inside, misses = [], []
    for a in range(2, 61):
        for b in range(1, a):
            if math.gcd(a, b) != 1:
                continue
            th = log(b) / log(a)
            margin = THETA - th
            row = (a, b, nstr(th, 20), nstr(margin, 12))
            if th < THETA:
                inside.append(row)
            else:
                misses.append((margin, row))
    misses.sort(key=lambda t: -t[0])
    print(f"\ncoprime a/b, a <= 60, inside the region (log b/log a < theta*): {len(inside)} bases")
    noninteger = [r for r in inside if r[1] > 1]
    print("  non-integer members:", " ".join(f"{a}/{b}" for a, b, _, _ in noninteger))
    print("  members with b >= 3:", " ".join(f"{a}/{b}" for a, b, _, _ in noninteger if b >= 3))
    print("  closest misses (outside, smallest |margin|):")
    for margin, row in misses[:8]:
        print("    ", f"{row[0]}/{row[1]}", "theta =", row[2], " theta* - theta =", row[3])
    print("  tightest members:")
    for row in sorted(inside, key=lambda r: mpf(r[3]))[:6]:
        print("    ", f"{row[0]}/{row[1]}", "theta =", row[2], " margin =", row[3])
    out["inside_a_le_60"] = [f"{a}/{b}" for a, b, _, _ in inside]
    out["inside_noninteger_a_le_60"] = [f"{a}/{b}" for a, b, _, _ in noninteger]
    out["closest_misses"] = [{"base": f"{r[0]}/{r[1]}", "theta": r[2], "theta_star_minus_theta": r[3]} for _, r in misses[:8]]

    # 31/4 and 3/2
    th314 = log(4) / log(31)
    th32 = log(2) / log(3)
    print("\n31/4: theta =", nstr(th314, 30), " margin theta* - theta =", nstr(THETA - th314, 20), " (81/200 = 0.405 sits between)")
    print("3/2 : theta =", nstr(th32, 30), " gap theta - theta* =", nstr(th32 - THETA, 20))
    print("      theta* would have to exceed log2/log3, i.e. mu = C1/C0 < log3/log2 =", nstr(log(3) / log(2), 20),
          "< 2: impossible for an irrationality-exponent bound of an irrational number (Dirichlet).")
    print("      C1 log 2 - C0 log 3 =", nstr(C1m * log(2) - C0 * log(3), 20), "(> 0: the homogenised forms grow)")
    bv = mpf(1) / 2 - 1 / pi ** 2
    print("Bundschuh-Vaananen 1/2 - 1/pi^2 =", nstr(bv, 30), "  31/4 inside BV:", th314 < bv)
    out["theta_31_4"] = nstr(th314, 40)
    out["theta_3_2"] = nstr(th32, 40)
    out["gap_3_2"] = nstr(th32 - THETA, 30)
    out["bv_threshold"] = nstr(bv, 40)

    # The delta strip beyond Bundschuh-Vaananen: coprime r/s with
    # mu_Z log s < log r < mu_BV log s, i.e. s^2.46498 < r < s^2.50828, for s <= 12.
    mu_bv = 2 * pi ** 2 / (pi ** 2 - 2)
    print("\nZudilin-normalised statement: F(r/s) irrational whenever log r > c log s with")
    print("   c = C1/C0 = mu =", nstr(MU, 30), "  (Bundschuh-Vaananen: c_BV = 2 pi^2/(pi^2 - 2) =", nstr(mu_bv, 20) + ")")
    strip = []
    for s_ in range(2, 13):
        lo = s_ ** MU
        hi = s_ ** mu_bv
        rs = [r for r in range(int(lo) + 1, int(hi) + 1) if math.gcd(r, s_) == 1 and lo < r < hi]
        strip.append((s_, nstr(lo, 8), nstr(hi, 8), rs))
        print(f"   s = {s_:2d}: s^mu = {nstr(lo, 8):>10}  s^mu_BV = {nstr(hi, 8):>10}  new bases r/s: {rs}")
    out["delta_strip_s_le_12"] = [{"s": s_, "s_pow_mu": lo, "s_pow_mu_bv": hi, "new_r": rs} for s_, lo, hi, rs in strip]
    out["c_zudilin_normalisation"] = nstr(MU, 40)
    out["c_bv_normalisation"] = nstr(mu_bv, 40)

    # Lean-facing certificate: smallest K with the pi > 157/50 rational argument
    target = Fr(81, 200) * C1
    assert target == Fr(88371, 400)
    pi_lo = Fr(157, 50)
    for Kc in range(1, 40):
        JK = partial_J(Kc)
        c0_lo = C0_POLY - Fr(3) / pi_lo ** 2 * (M_DIR ** 2 - JK)
        if c0_lo > target:
            break
    print(f"\nLean certificate: K = {Kc} trigamma terms per interval, J_K = {float(JK):.6f}, "
          f"C0 >= 266 - 3(225 - J_K)/(157/50)^2 = {float(c0_lo):.6f} > 88371/400 = {float(target):.6f}")
    print("   J_K as an exact rational has denominator with", len(str(JK.denominator)), "digits")
    out["lean_certificate"] = {"K": Kc, "J_K_float": float(JK), "C0_lower_float": float(c0_lo)}
    # Upper side: J <= psi_1(1/14) - psi_1(14/15) < psi_1(1/14) < 196 + pi^2/6 < 198 => C0 < 266
    print("Upper side: J <", nstr(psi1(Fr(1, 14)), 12), "< 198, so C0 < 266 and theta* < 266/545.5 =", 266 / 545.5, "< 1/2")
    out["upper_side"] = "J < psi_1(1/14) < 198 hence C0 < 266 and theta* < 532/1091 < 1/2"

    receipt_dir = os.path.join(
        os.path.dirname(os.path.dirname(os.path.abspath(__file__))),
        "..", "state", "formal_math", "erdos257_period_noncollapse", "erdos1049_zudilin_region")
    receipt_dir = os.path.normpath(receipt_dir)
    os.makedirs(receipt_dir, exist_ok=True)
    with open(os.path.join(receipt_dir, "region_receipt.json"), "w", encoding="utf-8") as fh:
        json.dump(out, fh, ensure_ascii=False, indent=1)
    print("receipt:", os.path.join(receipt_dir, "region_receipt.json"))
    return 0


if __name__ == "__main__":
    sys.exit(main())
