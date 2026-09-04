#!/usr/bin/env python3
"""Erdos 1041: checks for MonotoneTurningProof.md.

The claim is that the tangent offset t turns monotonically along BOTH descending
branches at the hub of g(zeta) = zeta^n + n zeta -- statement (T) of
NearFeketeCuspLaw.md section 7, previously measured to 7.7e-9.

Write lam = 1/(n-1), theta = (n-1) arg(zeta), a = (1-lam)theta/2, b = (1+lam)theta/2,
c_n = sin(pi lam)/lam, and

    W_pm(theta) = sin(lam theta)/lam  +/-  sin(theta)
    K_+(theta)  = (  sin a / sin b )^lam  W_+(theta)      [ Im g on the curve {Y=0} ]
    K_-(theta)  = ( -cos a / cos b )^lam  W_-(theta)      [ Im g on the curve {X=0} ]

MASTER IDENTITY (the whole proof):

    d/dtheta log K_+ = (1-lam^2) sin^2(theta) / ( 2 sin a sin b W_+ )
    d/dtheta log K_- = (1-lam^2) sin^2(theta) / ( 2 cos a cos b W_- )

with K_+(pi) = K_-(pi) = c_n.  Sections A-F below check each link in the chain.

Usage: ./repo-python formal_math/probes/erdos1041_monotone_turning.py [--max-n 12]
"""
from __future__ import annotations
import argparse, cmath, math
import numpy as np


def branch(n: int, smax: float, npts: int, which: int) -> np.ndarray:
    """Descending branch `which` (0 = Gamma_1, alpha=0; 1 = Gamma_2, alpha=2pi/n)."""
    zc = cmath.exp(1j * math.pi / (n - 1)); v = (n - 1) * zc
    gpp = n * (n - 1) * zc ** (n - 2); gppp = n * (n - 1) * (n - 2) * zc ** (n - 3)
    a0 = cmath.sqrt(2 / gpp) * (1 if which == 0 else -1); b0 = -gppp / (3 * gpp ** 2)
    coef = np.zeros(n + 1, dtype=complex); coef[0] = 1; coef[n - 1] = n
    ss = np.concatenate(([0.0], np.geomspace(1e-10, smax, npts)))
    zs = np.empty(len(ss), dtype=complex); zs[0] = zc
    for k in range(1, len(ss)):
        s = ss[k]
        if s < 1e-6:
            zs[k] = zc + a0 * s + b0 * s * s
        else:
            c = coef.copy(); c[n] = -(v + s * s); rt = np.roots(c)
            pred = zs[k - 1] + (zs[k - 1] - zs[k - 2]) if k > 1 else zs[0]
            zs[k] = rt[np.argmin(np.abs(rt - pred))]
    return zs[1:]


def main() -> int:
    ap = argparse.ArgumentParser()
    ap.add_argument("--max-n", type=int, default=12)
    args = ap.parse_args()
    ok = True

    # ---------------------------------------------------------------- A
    print("A. Master identity, symbolically exact")
    import sympy as sp
    L, T = sp.symbols('L T', positive=True)
    a, b = (1 - L) * T / 2, (1 + L) * T / 2
    for tag, W, pre, den in (
        ("K+", sp.sin(L * T) / L + sp.sin(T), (sp.sin(a) / sp.sin(b)) ** L, sp.sin(a) * sp.sin(b)),
        ("K-", sp.sin(L * T) / L - sp.sin(T), (-sp.cos(a) / sp.cos(b)) ** L, sp.cos(a) * sp.cos(b)),
    ):
        d = sp.simplify(sp.expand_trig(sp.simplify(
            sp.diff(sp.log(pre * W), T) - (1 - L ** 2) * sp.sin(T) ** 2 / (2 * den * W))))
        ok &= (d == 0)
        print(f"   dlog{tag}/dtheta - (1-lam^2)sin^2/(2 den W) = {d}")

    # ---------------------------------------------------------------- B
    import mpmath as mp
    mp.mp.dps = 50
    Kp = lambda L, t: (mp.sin((1 - L) * t / 2) / mp.sin((1 + L) * t / 2)) ** L * (mp.sin(L * t) / L + mp.sin(t))
    Km = lambda L, t: (-mp.cos((1 - L) * t / 2) / mp.cos((1 + L) * t / 2)) ** L * (mp.sin(L * t) / L - mp.sin(t))
    print("\nB. K_+(pi) = K_-(pi) = c_n, and the four sign regimes the identity forces")
    print(f"{'n':>4} {'K+(pi)-c':>11} {'K-(pi)-c':>11} {'max K+-c':>11} {'min K+-c':>11} "
          f"{'min K--c':>11} {'max K--c':>11} {'min W+':>9} {'min W-':>9}")
    print(f"{'':>4} {'':>11} {'':>11} {'th<pi':>11} {'th>pi':>11} {'th<pi*':>11} {'th>pi':>11}")
    for n in [3, 4, 5, 6, 8, 12, 20, 50, 200]:
        L = mp.mpf(1) / (n - 1); c = mp.sin(mp.pi * L) / L
        hi = 2 * mp.pi / (1 + L); lo = mp.pi / (1 + L); hiX = min(hi, mp.pi / (1 - L))
        scan = lambda f, x0, x1, N=1200: [f(L, x0 + (x1 - x0) * mp.mpf(i) / N) - c for i in range(1, N)]
        Wp = [mp.sin(L * (hi * mp.mpf(i) / 1200)) / L + mp.sin(hi * mp.mpf(i) / 1200) for i in range(1, 1200)]
        Wm = [mp.sin(L * (hi * mp.mpf(i) / 1200)) / L - mp.sin(hi * mp.mpf(i) / 1200) for i in range(1, 1200)]
        vals = (Kp(L, mp.pi) - c, Km(L, mp.pi) - c, max(scan(Kp, 0, mp.pi)), min(scan(Kp, mp.pi, hi)),
                min(scan(Km, lo, mp.pi)), max(scan(Km, mp.pi, hiX)), min(Wp), min(Wm))
        ok &= abs(vals[0]) < mp.mpf('1e-40') and abs(vals[1]) < mp.mpf('1e-40')
        ok &= vals[2] < 0 and vals[3] > 0 and vals[4] > 0 and vals[5] < 0
        ok &= vals[6] > 0 and vals[7] > 0
        print(f"{n:>4} " + " ".join(f"{mp.nstr(v, 4):>11}" for v in vals[:6])
              + f" {mp.nstr(vals[6], 4):>9} {mp.nstr(vals[7], 4):>9}")
    print("   (th<pi* = (pi/(1+lam), pi), where {X=0} exists on the Gamma_1 side)")

    # ---------------------------------------------------------------- C
    print("\nC. Lemma S2 wall: the ray arg zeta = 2pi/n meets Im g = c_n once, at Z0,")
    print("   and Re g(Z0) < Re g(zeta_c) -- so Z0 is not on a descending branch.")
    print(f"{'n':>5} {'r0':>10} {'Re g(Z0)':>12} {'Re g(zc)':>12} {'gap':>11}")
    for n in [3, 4, 5, 6, 8, 12, 20, 50, 200, 1000]:
        cn = (n - 1) * mp.sin(mp.pi / (n - 1)); r0 = cn / (n * mp.sin(2 * mp.pi / n))
        gap = (n - 1) * mp.cos(mp.pi / (n - 1)) - (r0 ** n + n * r0 * mp.cos(2 * mp.pi / n))
        ok &= (r0 < 1) and (gap > 0)
        print(f"{n:>5} {float(r0):>10.6f} {float(r0**n + n*r0*mp.cos(2*mp.pi/n)):>12.6f} "
              f"{float((n-1)*mp.cos(mp.pi/(n-1))):>12.6f} {float(gap):>11.6f}")

    # ---------------------------------------------------------------- D/E/F
    print("\nD. On the traced branches: X = r^{n-1}cos b + cos a, Y = r^{n-1}sin b - sin a.")
    print("   Gamma_1 needs X>0,Y>0 (dt/dsigma >= 0);  Gamma_2 needs X<0,Y>0 (dt/dsigma <= 0).")
    print("   dt/dsigma = ((n-1)/n) Im(N^2)/|N|^4 with N = g'/(n zeta^{(n-2)/2}); it blows up at")
    print("   the hub, where N -> 0, so its sign is read off X*Y, which stays well conditioned.")
    print(f"{'n':>3} {'G1 min X':>10} {'G1 min Y':>10} {'G1 min dt*':>11} "
          f"{'G2 max X':>10} {'G2 min Y':>10} {'G2 max dt*':>11} {'signs':>6} {'res':>6}")
    for n in range(3, args.max_n + 1):
        pc = math.pi / (n - 1); cn = (n - 1) * math.sin(pc)
        row, frac, sgn = [], 1.0, True
        for which in (0, 1):
            z = branch(n, min(10 ** (0.5 * n + 2), 1e6), 20000, which)
            r = np.abs(z); phi = np.angle(z)
            on = np.abs(np.imag(z ** n + n * z) - cn) < 1e-6
            assert on.sum() > 0.5 * len(z), f"tracer resolved too little at n={n}, branch {which}"
            frac = min(frac, float(on.mean()))
            A, B = (n - 2) * phi / 2, n * phi / 2
            X = r ** (n - 1) * np.cos(B) + np.cos(A)
            Y = r ** (n - 1) * np.sin(B) - np.sin(A)
            N = (z ** (n - 1) + 1) / z ** ((n - 2) / 2)
            dt = (n - 1) / n * np.imag(N ** 2) / np.abs(N) ** 4
            good = on & (np.abs(X) > 1e-8) & (np.abs(Y) > 1e-8)
            sgn &= bool(np.all(np.sign(dt[good]) == np.sign(X[good] * Y[good])))
            if which == 0:
                ok_s = bool(np.all(phi[on] > 0) and np.all(phi[on] < pc + 1e-12))
                ok_s &= bool(X[on].min() > -1e-8 and Y[on].min() > -1e-8)
                ok_s &= bool(dt[good].min() > 0)
                row += [X[on].min(), Y[on].min(), dt[good].min()]
            else:
                ok_s = bool(np.all(phi[on] > pc - 1e-12) and np.all(phi[on] < 2 * math.pi / n + 1e-12))
                ok_s &= bool(X[on].max() < 1e-8 and Y[on].min() > -1e-8)
                ok_s &= bool(dt[good].max() < 0)
                row += [X[on].max(), Y[on].min(), dt[good].max()]
            sgn &= ok_s
        print(f"{n:>3} {row[0]:>10.2e} {row[1]:>10.2e} {row[2]:>11.2e} "
              f"{row[3]:>10.2e} {row[4]:>10.2e} {row[5]:>11.2e} {str(sgn):>6} {frac:>6.3f}")
        ok &= sgn
    print("   (dt* = over points with |X|,|Y| > 1e-8, i.e. off the hub's coordinate singularity.)")

    # ---------------------------------------------------------------- E
    print("\nE. Far field of Gamma_2 by direct root-finding (no continuation):")
    print("   Y(R) = (n-2)sin(2pi/n)/2 - c_n/(2R) + O(R^-2) > 0, fixing the sign of Y on Gamma_2.")
    print(f"{'n':>3} {'R':>7} {'Y(R)':>12} {'limit':>12} {'Y-limit':>11} {'-c_n/2R':>11} {'resid':>9}")
    for n in range(3, args.max_n + 1):
        cn = (n - 1) * mp.sin(mp.pi / (n - 1)); lim = (n - 2) * mp.sin(2 * mp.pi / n) / 2
        R = mp.mpf(10) ** 4
        # On |zeta| = R put phi = 2pi/n - delta and solve Im g = c_n in the scaled
        # variable: the raw equation carries a factor R^n ~ 1e48, which puts the
        # residual far below any sane root tolerance while delta is still wrong.
        # Solve in the rescaled unknown m = delta * R^{n-1} = O(1): in the raw
        # variable dF/ddelta ~ n R^{n-1}, so no root tolerance is both meetable
        # and meaningful.  In m the problem is O(1)-conditioned.
        sc = R ** (n - 1)
        F = lambda m: -sc * mp.sin(n * m / sc) + n * mp.sin(2 * mp.pi / n - m / sc) - cn / R
        m = mp.findroot(F, (mp.sin(2 * mp.pi / n) / 2, 2 * mp.sin(2 * mp.pi / n)), solver='bisect')
        delta = m / sc
        ph = 2 * mp.pi / n - delta
        Y = R ** (n - 1) * mp.sin(n * delta / 2) - mp.sin((n - 2) * ph / 2)
        ok &= (Y > 0) and abs((Y - lim) + cn / (2 * R)) < mp.mpf('1e-6') * lim
        print(f"{n:>3} {float(R):>7.0e} {float(Y):>12.7f} {float(lim):>12.7f} {float(Y-lim):>11.3e} "
              f"{float(-cn/(2*R)):>11.3e} {float((Y-lim)+cn/(2*R)):>9.2e}")

    # ---------------------------------------------------------------- F
    print("\nF. K_pm - c_n vanishes to order THREE at theta = pi (sin^2 in the identity),")
    print("   with the constants the identity forces.  This is the general-n form of the")
    print("   (y-1)^3 factor found at n=3 in ConeBoundBranchGeometry.md section 5.")
    print(f"{'n':>4} {'(K+-c)/e^3':>13} {'+(1-L^2)/6cos^2':>16} {'(K--c)/e^3':>13} {'-(1-L^2)/6sin^2':>16}")
    for n in [3, 5, 8, 12, 30]:
        L = mp.mpf(1) / (n - 1); c = mp.sin(mp.pi * L) / L; e = mp.mpf('1e-5')
        got = ((Kp(L, mp.pi + e) - c) / e ** 3, (Km(L, mp.pi + e) - c) / e ** 3)
        want = ((1 - L ** 2) / (6 * mp.cos(L * mp.pi / 2) ** 2),
                -(1 - L ** 2) / (6 * mp.sin(L * mp.pi / 2) ** 2))
        ok &= all(abs(g_ - w) < mp.mpf('1e-3') * abs(w) for g_, w in zip(got, want))
        print(f"{n:>4} {float(got[0]):>13.7f} {float(want[0]):>16.7f} "
              f"{float(got[1]):>13.5f} {float(want[1]):>16.5f}")

    print("\nOK" if ok else "\nFAILED")
    return 0 if ok else 1


if __name__ == "__main__":
    raise SystemExit(main())
