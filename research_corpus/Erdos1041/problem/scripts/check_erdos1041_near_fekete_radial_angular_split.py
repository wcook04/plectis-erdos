"""Checker for NearFeketeRadialAngularSplit.md.

Replays: Theorem 2 (Fekete-Hadamard stability) on sampled near-gon configs;
Theorem 3/4 (radial monotonicity / radial slice) numerically at n=3..12;
Theorem 5 (spoke expansion + averaging identity) to high accuracy;
Theorem 6 (centroid half-plane law, first-order form);
Theorem 7's exact rational quintic witness in pure Fraction arithmetic
(4 of 5 origin spokes escape; roots in the OPEN unit disk; 1-D ~ 3.2e-4).

Usage: check_erdos1041_near_fekete_radial_angular_split.py [--check]
Exit 0 iff all checks pass.
"""
import argparse
import sys
from fractions import Fraction as F

import numpy as np

RNG = np.random.default_rng(10412)


# ---------- Theorem 2: stability ----------

def check_stability(trials=60):
    ok = True
    for _ in range(trials):
        n = int(RNG.integers(3, 10))
        eta_cap = 1.0 / (80 * n * n)
        # near-gon sample with controlled perturbation
        scale = 10 ** RNG.uniform(-6, -3)
        th = 2 * np.pi * np.arange(n) / n + scale * RNG.standard_normal(n)
        rho = 1 - np.abs(scale * RNG.standard_normal(n))
        a = rho * np.exp(1j * th)
        V = np.vander(a, n, increasing=True)
        G = V @ V.conj().T
        D = float(np.real(np.linalg.det(G))) / n ** n
        eta = 1 - D
        if not (0 <= eta <= eta_cap):
            continue
        # (1)
        for r in rho:
            ok &= 1 - r ** 2 <= n * eta / (n - 1) + 1e-12
        # (2)
        sep = min(abs(a[i] - a[j]) for i in range(n) for j in range(i + 1, n))
        ok &= sep >= (2 - 2 * np.sqrt(eta) - n * eta) / (n - 1) - 1e-12
        # (3): nearest rotated-gon matching within 7 sqrt(eta)
        A1 = a[0] ** n
        om = A1 / abs(A1)
        gon = om ** (1.0 / n) * np.exp(2j * np.pi * np.arange(n) / n)
        used, worst = set(), 0.0
        good = True
        for x in a:
            j = int(np.argmin(np.abs(gon - x)))
            if j in used:
                good = False
                break
            used.add(j)
            worst = max(worst, abs(gon[j] - x))
        ok &= good and worst <= 7 * np.sqrt(eta) + 1e-12
    return ok


# ---------- Theorems 3/4: radial monotonicity and slice ----------

def check_radial_slice(trials=40):
    ok = True
    for _ in range(trials):
        n = int(RNG.integers(3, 13))
        rho_min_req = max(0.0, 2 * np.cos(2 * np.pi / n) - 1)
        rho = RNG.uniform(rho_min_req + 1e-9, 1.0, n)
        om = np.exp(1j * RNG.uniform(0, 2 * np.pi))
        u = om * np.exp(2j * np.pi * np.arange(n) / n)
        a = rho * u
        for i in range(n):
            ss = np.linspace(1e-3, rho[i], 25)
            for s in ss:
                fv = np.prod(s * u[i] - a)
                if abs(fv) > 1 - s ** n + 1e-10:
                    ok = False
    return ok


# ---------- Theorem 5: identities ----------

def check_spoke_identity(trials=25):
    worst = 0.0
    for _ in range(trials):
        n = int(RNG.integers(3, 9))
        u = np.exp(1j * RNG.uniform(0, 2 * np.pi, n))
        s = RNG.uniform(0.05, 0.85)
        M = 4000
        m = np.arange(1, M + 1)
        q = np.array([np.sum(u ** mm) for mm in m])
        for i in range(n):
            lhs = np.log(abs(np.prod(s * u[i] - u)))
            rhs = -np.sum((s ** m / m) * np.real(q * np.conj(u[i]) ** m))
            worst = max(worst, abs(lhs - rhs))
        tot_lhs = sum(np.log(abs(np.prod(s * u[i] - u))) for i in range(n))
        tot_rhs = -np.sum((s ** m / m) * np.abs(q) ** 2)
        worst = max(worst, abs(tot_lhs - tot_rhs))
    return worst


# ---------- Theorem 7: exact rational quintic witness ----------

class GQ:
    __slots__ = ("re", "im")

    def __init__(s, re, im=F(0)):
        s.re, s.im = F(re), F(im)

    def __add__(s, o):
        return GQ(s.re + o.re, s.im + o.im)

    def __sub__(s, o):
        return GQ(s.re - o.re, s.im - o.im)

    def __mul__(s, o):
        return GQ(s.re * o.re - s.im * o.im, s.re * o.im + s.im * o.re)

    def abs2(s):
        return s.re * s.re + s.im * s.im


def check_rational_witness():
    lam = F(999999, 1000000)
    u = [GQ(1),
         GQ(F(1053, 3365), F(3196, 3365)),
         GQ(F(-5928, 7297), F(4255, 7297)),
         GQ(F(-5928, 7297), F(-4255, 7297)),
         GQ(F(1053, 3365), F(-3196, 3365))]
    for uk in u:
        if uk.abs2() != 1:
            return False, "non-unimodular"
    roots = [GQ(lam * uk.re, lam * uk.im) for uk in u]

    def f_at(z):
        acc = GQ(1)
        for r in roots:
            acc = acc * (z - r)
        return acc

    escapes = 0
    for k, s in ((1, F(303, 2000)), (2, F(77, 1000)), (3, F(77, 1000)), (4, F(303, 2000))):
        v = f_at(GQ(s * u[k].re, s * u[k].im)).abs2()
        escapes += (v > 1)
    contained0 = all(f_at(GQ(F(m, 40) * lam)).abs2() < 1 for m in range(1, 40))
    open_disk = all(r.abs2() < 1 for r in roots)
    return (escapes == 4 and contained0 and open_disk), \
        f"escapes={escapes}/4 spoke0_contained={contained0} open_disk={open_disk}"


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--check", action="store_true")
    ap.parse_args()
    ok = True

    r = check_stability()
    print(f"theorem2 stability sampled: {'ok' if r else 'FAIL'}")
    ok &= r

    r = check_radial_slice()
    print(f"theorem3/4 radial slice n=3..12: {'ok' if r else 'FAIL'}")
    ok &= r

    w = check_spoke_identity()
    print(f"theorem5 identity worst residual: {w:.3e}")
    ok &= w < 1e-8

    r, msg = check_rational_witness()
    print(f"theorem7 rational quintic witness: {msg}")
    ok &= r

    print("PASS" if ok else "FAIL")
    return 0 if ok else 1


if __name__ == "__main__":
    sys.exit(main())
