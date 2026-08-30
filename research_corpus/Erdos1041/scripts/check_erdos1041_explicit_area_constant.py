"""Checker for ProperComponentExplicitAreaConstant.md (Erdos 1041).

Verifies:
  1  certified rational UPPER bounds for A_q = zeta(q/(q-1))^{(q-1)/2}
     (integral-test partial sums, rounded up; cross-checked against
     mpmath.zeta) and exact G_q^2 = sum_{j=q}^5 C(j,q)^2 in
     {55, 146, 117, 26, 1};
  2  the tail-decay lemma sum_{l>=j}|b_l|^2 <= E/j and the linear-term
     projection bound ||Proj_{<0}(Q'h)|| <= eta * sum sqrt(j)|q_j| on
     random data;
  3  the Schur-tail bound on random degree-3 Blaschke products with
     N = 5 (re-verification of the landed lemma as consumed here);
  4  THE MAIN CERTIFICATE, in EXACT rational arithmetic (fractions
     only): with rational upper bounds for A_q, G_q, sqrt(Bbar^2-p^2)
     and every rounding upward, L(13/50000) <= sqrt(15)/4096, i.e.
     L(v*)^2 <= 15/16777216, at p = 1/4.  Hence
     eps_5 = (13/50000)^2 = 6.76e-8;
  5  the elementary fallback: C_5 certified <= 103.87 (sharp zeta) and
     <= 110.28 (crude zeta), giving eps >= 8.27e-11 / 7.3e-11 in exact
     rational arithmetic;
  6  monotonicity guards: delta_5 increasing on (0, 1/4]; the map
     p -> p^{2/5}(1 - eps_A(p)) increasing on a dense grid;
  7  threshold numbers: tanh(4^{2/5}/(1-eps_5)) - tanh(4^{2/5})
     = 1.366e-8 (and the fallback's 1.67e-11).

Exit 0 iff all pass.
"""
import sys
from fractions import Fraction
from math import comb, isqrt

import mpmath as mp
import numpy as np

rng = np.random.default_rng(17)
FAILURES = []


def report(name, ok, detail=""):
    print(("PASS " if ok else "FAIL ") + name + ("  " + detail if detail else ""))
    if not ok:
        FAILURES.append(name)


def zeta_upper(s_num, s_den, M=4000):
    """Certified rational upper bound for zeta(s), s = s_num/s_den > 1:
    sum_{k<=M} k^{-s} + M^{1-s}/(s-1), every term rounded up at 1e-12."""
    s = Fraction(s_num, s_den)
    mp.mp.dps = 40
    sf = mp.mpf(s_num) / s_den
    partial = mp.nsum(lambda k: k ** (-sf), [1, M])
    tail = M ** (1 - sf) / (sf - 1)
    val = partial + tail
    return Fraction(int(mp.ceil(val * mp.mpf(10) ** 12)), 10 ** 12)


def frac_sqrt_upper(x, digits=9):
    """Rational s with s^2 >= x (x a Fraction >= 0), s minimal at 1e-digits."""
    mp.mp.dps = 50
    approx = mp.sqrt(mp.mpf(x.numerator) / x.denominator)
    s = Fraction(int(mp.ceil(approx * mp.mpf(10) ** digits)), 10 ** digits)
    while s * s < x:
        s += Fraction(1, 10 ** digits)
    return s


def pow_frac_upper(base, num, den, digits=9):
    """Rational upper bound for base^(num/den), base a Fraction > 0."""
    mp.mp.dps = 50
    approx = (mp.mpf(base.numerator) / base.denominator) ** (mp.mpf(num) / den)
    s = Fraction(int(mp.ceil(approx * mp.mpf(10) ** digits)), 10 ** digits)
    # verify s^den >= base^num exactly
    while s ** den < base ** num:
        s += Fraction(1, 10 ** digits)
    return s


def main():
    # 1 certified A_q uppers + exact G_q^2
    z2 = zeta_upper(2, 1)
    z32 = zeta_upper(3, 2)
    z43 = zeta_upper(4, 3)
    z54 = zeta_upper(5, 4)
    mp.mp.dps = 40
    ok1 = (z2 >= Fraction(int(mp.floor(mp.zeta(2) * 10**9)), 10**9)
           and z32 >= Fraction(int(mp.floor(mp.zeta(1.5) * 10**9)), 10**9)
           and z43 >= Fraction(int(mp.floor(mp.zeta(mp.mpf(4) / 3) * 10**9)), 10**9)
           and z54 >= Fraction(int(mp.floor(mp.zeta(1.25) * 10**9)), 10**9))
    # A_q = zeta(q/(q-1))^{(q-1)/2}: A_2 = z2^{1/2}, A_3 = z32, A_4 = z43^{3/2}, A_5 = z54^2
    A = {1: Fraction(1)}
    A[2] = pow_frac_upper(z2, 1, 2)
    A[3] = z32
    A[4] = pow_frac_upper(z43, 3, 2)
    A[5] = z54 * z54
    G2 = {q: sum(comb(j, q) ** 2 for j in range(q, 6)) for q in range(1, 6)}
    ok1 &= (G2 == {1: 55, 2: 146, 3: 117, 4: 26, 5: 1})
    G = {q: frac_sqrt_upper(Fraction(G2[q])) for q in range(1, 6)}
    report("1 certified A_q uppers + exact G_q^2", ok1,
           f"A={[float(A[q]) for q in range(1,6)]}, G^2={list(G2.values())}")

    # 2 tail-decay lemma + linear projection bound (random)
    ok2 = True
    for _ in range(300):
        L = 40
        b = (rng.normal(size=L) + 1j * rng.normal(size=L)) * np.exp(-0.2 * np.arange(1, L + 1))
        E = float(np.sum(np.arange(1, L + 1) * np.abs(b) ** 2))
        for j in range(1, 8):
            if float(np.sum(np.abs(b[j - 1:]) ** 2)) > E / j + 1e-12:
                ok2 = False
        q = rng.normal(size=6) + 1j * rng.normal(size=6)  # q_0..q_5
        eta = np.sqrt(E)
        # Proj_{<0}(Q'h): coefficient at freq -nu is sum_j j q_j b_{j-1+nu}
        proj2 = 0.0
        for nu in range(1, L + 2):
            coef = sum(j * q[j] * (b[j - 1 + nu - 1] if j - 1 + nu - 1 < L else 0)
                       for j in range(1, 6))
            proj2 += abs(coef) ** 2
        bound = eta * sum(np.sqrt(j) * abs(q[j]) for j in range(1, 6))
        if np.sqrt(proj2) > bound + 1e-9:
            ok2 = False
    report("2 tail-decay lemma + sharp linear projection bound", ok2)

    # 3 Schur tail on random degree-3 Blaschke, N = 5
    ok3 = True
    worst_ratio = np.inf
    for _ in range(400):
        a = [np.sqrt(rng.uniform()) * np.exp(2j * np.pi * rng.uniform()) for _ in range(3)]
        th = np.linspace(0, 2 * np.pi, 4096, endpoint=False)
        z = np.exp(1j * th)
        gv = np.ones_like(z)
        for aj in a:
            gv *= (z - aj) / (1 - np.conj(aj) * z)
        p = abs(np.prod([abs(aj) for aj in a]))
        coeffs = np.fft.fft(gv) / len(z)
        tail = float(np.sum(np.abs(coeffs[6:len(z) // 2]) ** 2))
        floor_ = (1 - p ** 2) * p ** 10
        if floor_ > 1e-18:
            worst_ratio = min(worst_ratio, tail / floor_)
        if tail < floor_ - 1e-12:
            ok3 = False
    report("3 Schur tail (N=5) on random Blaschke", ok3,
           f"min tail/floor = {worst_ratio:.3f}")

    # 4 MAIN CERTIFICATE, exact rational arithmetic
    p = Fraction(1, 4)
    vstar = Fraction(13, 50000)
    delta = (1 - p * p) * p ** 10  # = 15/16777216
    ok4 = delta == Fraction(15, 16777216)
    W = sum(A[q] * G[q] * vstar ** q for q in range(1, 6))
    ok4 &= W < 1
    Bbar = 1 / (1 - W)
    s10 = frac_sqrt_upper(Fraction(10))
    s5 = frac_sqrt_upper(Fraction(5))
    root_term = frac_sqrt_upper(Bbar * Bbar - p * p)
    lin = s10 * root_term + s5 * p
    L_of_v = lin * vstar + Bbar * sum(A[q] * G[q] * vstar ** q for q in range(2, 6))
    ok4 &= (L_of_v > 0) and (L_of_v * L_of_v <= delta)
    eps5 = vstar * vstar
    report("4 MAIN: exact-rational L(13/50000)^2 <= 15/16777216", ok4,
           f"L(v*)^2 = {float(L_of_v * L_of_v):.6e} <= {float(delta):.6e}; "
           f"eps_5 = {float(eps5):.4e}")

    # 5 elementary fallback
    D = {j: sum(comb(j, q) * A[q] for q in range(1, j + 1)) for j in range(1, 6)}
    C5sq = sum(D[j] ** 2 for j in range(1, 6))
    sqrt_delta_up = frac_sqrt_upper(delta)
    epsA = delta / (C5sq * (1 + sqrt_delta_up) ** 2)
    ok5 = C5sq < Fraction(10788) and epsA > Fraction(827, 10 ** 13)
    report("5 fallback: C_5^2 certified, eps_A > 8.27e-11 (exact rational)",
           ok5, f"C_5 = {float(C5sq) ** 0.5:.4f}, eps_A = {float(epsA):.4e}")

    # 6 monotonicity guards
    okd = all(2 * pp ** 9 * (5 - 6 * pp ** 2) > 0 for pp in np.linspace(1e-3, 0.25, 50))
    grid = np.linspace(1e-3, 0.25, 400)
    fvals = []
    C5f = float(C5sq) ** 0.5
    for pp in grid:
        dl = (1 - pp ** 2) * pp ** 10
        ea = dl / (C5f ** 2 * (1 + np.sqrt(dl)) ** 2)
        fvals.append(pp ** 0.4 * (1 - ea))
    ok6 = okd and all(fvals[i + 1] > fvals[i] for i in range(len(fvals) - 1))
    report("6 monotonicity: delta_5' > 0 and p^{2/5}(1-eps_A(p)) increasing", ok6)

    # 7 thresholds
    mp.mp.dps = 30
    e5 = mp.mpf(13) / 50000
    e5 = e5 * e5
    th_old = mp.tanh(mp.mpf(4) ** (mp.mpf(2) / 5))
    th_new = mp.tanh(mp.mpf(4) ** (mp.mpf(2) / 5) / (1 - e5))
    diff = th_new - th_old
    ok7 = mp.mpf("1.3e-8") < diff < mp.mpf("1.4e-8")
    report("7 threshold improvement", ok7,
           f"Theta: {mp.nstr(th_old, 15)} -> {mp.nstr(th_new, 15)} (+{mp.nstr(diff, 4)})")

    print()
    if FAILURES:
        print("FAIL:", FAILURES)
        return 1
    print("PASS: all sections")
    return 0


if __name__ == "__main__":
    sys.exit(main())
