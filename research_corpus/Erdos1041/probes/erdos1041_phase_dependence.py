#!/usr/bin/env python3
"""Erdos 1041: checks for PhaseDependenceOfKappa.md.

NearFeketeCuspLaw.md section 2 writes kappa_n(phi) = beta_1 + beta_2, but after
its own rescaling z = rho e^{i psi} zeta (psi = phi/(n-1)) the model
g(zeta) = zeta^n + n zeta is phi-FREE -- so a single branch pair cannot carry the
phi-dependence its section 3 sweep measures (kappa_3 runs 0.608..0.813).

Where phi actually enters: the far field wants f + m real positive, so in the
g-plane the descending ray leaves the critical value along e^{-i delta} with
delta = n phi/(n-1), and a branch lies in Im(e^{i delta} g) = const.  Write

    cand(delta) = C(delta) - (D_1(delta) + D_2(delta))

for the two-branch deficit at hub 0 in that direction.  Since g(omega zeta) =
omega g(zeta) for omega = e^{2 pi i/(n-1)}, hub j in direction delta is hub 0 in
direction delta + 2 pi j/(n-1).  min_c L(c) is a MINIMUM over curves, so

    (H)  kappa_n(phi) = max_{j=0..n-2} cand( n phi/(n-1) + 2 pi j/(n-1) ).

Checked here: (H) against the sweep values the cusp law's own verifier reports,
that a single candidate is NOT kappa_n(phi) (it goes negative), and the rotated
master identity plus K_pm^delta(pi) = c_n(delta).

Usage: ./repo-python formal_math/probes/erdos1041_phase_dependence.py
"""
from __future__ import annotations
import cmath, math
import numpy as np

# From scripts/check_erdos1041_near_fekete_cusp_law.py --part phase (12 samples).
SWEEP = {3: (0.608021632576, 0.812598415034), 4: (1.0301196657, 1.12291152414)}


def branch_d(n: int, delta: float, which: int, smax: float, npts: int) -> np.ndarray:
    """Descending branch of Im(e^{i delta} g) = const at hub 0, direction e^{-i delta}."""
    zc = cmath.exp(1j * math.pi / (n - 1)); v = (n - 1) * zc
    gpp = n * (n - 1) * zc ** (n - 2); gppp = n * (n - 1) * (n - 2) * zc ** (n - 3)
    e = cmath.exp(-1j * delta)
    a0 = cmath.sqrt(2 * e / gpp) * (1 if which == 0 else -1)
    b0 = -gppp * e * e / (3 * gpp ** 2)
    coef = np.zeros(n + 1, dtype=complex); coef[0] = 1; coef[n - 1] = n
    ss = np.concatenate(([0.0], np.geomspace(1e-10, smax, npts)))
    zs = np.empty(len(ss), dtype=complex); zs[0] = zc
    for k in range(1, len(ss)):
        s = ss[k]
        if s < 1e-6:
            zs[k] = zc + a0 * s + b0 * s * s
        else:
            c = coef.copy(); c[n] = -(v + s * s * e); rt = np.roots(c)
            pred = zs[k - 1] + (zs[k - 1] - zs[k - 2]) if k > 1 else zs[0]
            zs[k] = rt[np.argmin(np.abs(rt - pred))]
    return zs[1:]


def cand(n: int, delta: float, npts: int = 12000) -> float:
    """C - (D_1 + D_2) for the branch pair at hub 0 in direction e^{-i delta}."""
    smax = min(10 ** (0.5 * n + 2), 1e6); tot = 0.0
    ss = np.concatenate(([0.0], np.geomspace(1e-10, smax, npts)))[1:]
    for w in (0, 1):
        z = branch_d(n, delta, w, smax, npts)
        cnd = (n - 1) * math.sin(math.pi / (n - 1) + delta)
        on = np.abs(np.imag(cmath.exp(1j * delta) * (z ** n + n * z)) - cnd) < 1e-6
        if on.sum() < 100:
            return float("nan")
        gp = n * (z ** (n - 1) + 1.0)
        al_raw = np.angle(z[on][-1])
        k = round((n * al_raw + delta) / (2 * math.pi))
        al = (2 * k * math.pi - delta) / n
        Lam = np.trapezoid((2 * ss / np.abs(gp))[on], ss[on])
        chord = cmath.exp(-1j * al) * (z[on][-1] - cmath.exp(1j * math.pi / (n - 1)))
        tot += math.cos(math.pi / (n - 1) - al) - (Lam - chord.real)
    return tot


def main() -> int:
    ok = True

    print("A. The rotated master identity, symbolically exact at general delta")
    import sympy as sp
    L, T, d = sp.symbols('L T d', positive=True)
    at = (1 - L) * T / 2 - d / 2; bt = (1 + L) * T / 2 + d / 2; mu = bt - at
    for tag, W, pre, den in (
        ("K+", sp.sin(mu) / L + sp.sin(T), (sp.sin(at) / sp.sin(bt)) ** L, sp.sin(at) * sp.sin(bt)),
        ("K-", sp.sin(mu) / L - sp.sin(T), (-sp.cos(at) / sp.cos(bt)) ** L, sp.cos(at) * sp.cos(bt)),
    ):
        r = sp.simplify(sp.expand_trig(sp.simplify(
            sp.diff(sp.log(pre * W), T) - (1 - L ** 2) * sp.sin(T) ** 2 / (2 * den * W))))
        ok &= (r == 0)
        print(f"   dlog{tag}^delta/dT - (1-lam^2)sin^2T/(2 den W) = {r}")

    import mpmath as mp
    mp.mp.dps = 40
    print("\nB. K_pm^delta(pi) = c_n(delta) = sin(pi lam + delta)/lam, the rotated critical value")
    for n in (3, 5, 9):
        Lm = mp.mpf(1) / (n - 1)
        for dd in (mp.mpf(0), mp.mpf('0.37'), mp.mpf('1.9')):
            a_ = (1 - Lm) * mp.pi / 2 - dd / 2; b_ = (1 + Lm) * mp.pi / 2 + dd / 2
            Kp = (mp.sin(a_) / mp.sin(b_)) ** Lm * (mp.sin(b_ - a_) / Lm)
            Km = (-mp.cos(a_) / mp.cos(b_)) ** Lm * (mp.sin(b_ - a_) / Lm)
            c = mp.sin(mp.pi * Lm + dd) / Lm
            ok &= abs(Kp - c) < mp.mpf('1e-30') and abs(Km - c) < mp.mpf('1e-30')
            print(f"   n={n:>2} delta={float(dd):.2f}  K+-c={mp.nstr(Kp-c,3):>10} "
                  f"K--c={mp.nstr(Km-c,3):>10}  c={float(c):>9.6f}")

    print("\nC. (H): kappa_n(phi) = max_j cand(...), against the cusp law's sweep")
    print("   The tracer's quadrature bar is ~1e-4 (see BridgeIdentityProof.md section 5).")
    for n in (3, 4):
        lo_s, hi_s = SWEEP[n]
        print(f"\n   n={n}   sweep min={lo_s:.6f}  max={hi_s:.6f}")
        hdr = "  ".join(f"{'j=%d' % j:>10}" for j in range(n - 1))
        print(f"   {'phi/(2pi/n)':>12} {hdr}  {'max_j':>10}")
        got = []
        for i in range(7):
            phi = (2 * math.pi / n) * i / 6
            d0 = n * phi / (n - 1)
            vals = [cand(n, (d0 + 2 * math.pi * j / (n - 1)) % (2 * math.pi)) for j in range(n - 1)]
            got.append((i, max(vals), min(vals)))
            print(f"   {phi/(2*math.pi/n):>12.4f} " + "  ".join(f"{v:>10.6f}" for v in vals)
                  + f"  {max(vals):>10.6f}")
        at0 = [m for i, m, _ in got if i == 0][0]
        ok &= abs(at0 - lo_s) < 3e-4                     # phi = 0 reproduces the sweep minimum
        ok &= min(m for _, m, _ in got) >= at0 - 3e-4    # phi = 0 IS the minimum over phi
        ok &= min(v for _, _, v in got) < 0.0            # a single candidate goes NEGATIVE
        # Only grid points the 12-sample sweep actually hits may be range-checked.
        # Sweep is phi_j = 2 pi j/12; our grid is phi_i = (2 pi/n)(i/6); they coincide
        # iff j = 2i/n is an integer, i.e. iff n divides 2i.  (n=3 -> i in {0,3,6};
        # n=4 -> i in {0,2,4,6}.)  At n=4, i=3 gives 1.134055, which the sweep skips.
        for i, m, _ in got:
            if (2 * i) % n == 0:
                ok &= (lo_s - 3e-4) <= m <= (hi_s + 3e-4)
    print("\n   A single candidate goes negative, so cand(delta) alone is NOT kappa_n(phi);")
    print("   the maximum over the n-1 hubs is.  That is where the phi-dependence lives.")

    print("\nD. The C - B identity.  With u = gamma_1 in [0, 2pi/n), v = 2pi/n - u and")
    print("   q = (n-2)/4, the cone half-angles are T_k = (n-2)|gamma_k|/2, and")
    print("        (C - B) cos(qu) cos(qv)  =  cos(pi/n) cos( n(u-v)/4 ).")
    print("   Each step of the proof, symbolic in n:")
    nn, U, V = sp.symbols('n u v')
    w_ = 2 * sp.pi / nn; qq = (nn - 2) / sp.Integer(4); pp = qq + 1
    steps = [("p - q - 1", pp - qq - 1),
             ("(pu + qv) - (u + qw)", pp * U + qq * (w_ - U) - (U + qq * w_)),
             ("(pu - qv) - (nu/2 - qw)", pp * U - qq * (w_ - U) - (nn * U / 2 - qq * w_)),
             ("w/2 + qw - pi/2", w_ / 2 + qq * w_ - sp.pi / 2),
             ("nw/4 - qw - pi/n", nn * w_ / 4 - qq * w_ - sp.pi / nn)]
    for name, ex in steps:
        val = sp.simplify(ex); ok &= (val == 0)
        print(f"      {name:>26} = {val}")
    print("   so the (u+qw),(v+qw) pair collapses through cos(pi/2) = 0 and the other")
    print("   pair through cos(pi/n).  Positivity of every factor:")
    print(f"{'n':>6} {'max qu':>10} {'< pi/2':>9} {'cos(pi/n)':>10} {'max|n(u-v)/4|':>14} "
          f"{'min (C-B) on (0,2pi/n)':>23}")
    for n in [3, 4, 5, 6, 8, 12, 20, 50, 200, 1000]:
        wq = mp.mpf(n - 2) / 4 * (2 * mp.pi / n)
        w2 = 2 * mp.pi / n
        cb = lambda t: (mp.cos(mp.pi / n) * mp.cos(n * (2 * t - w2) / 4)
                        / (mp.cos((n - 2) * t / 4) * mp.cos((n - 2) * (w2 - t) / 4)))
        lo = min(cb(w2 * mp.mpf(i) / 3000) for i in range(1, 3000))
        # closed form must agree with the raw C - B
        for f in ('0.02', '0.31', '0.5', '0.93'):
            t = w2 * mp.mpf(f); r = w2 - t; qn = mp.mpf(n - 2) / 4
            raw = (mp.cos(t) + mp.cos(r)) - (mp.tan(qn * t) * mp.sin(t) + mp.tan(qn * r) * mp.sin(r))
            ok &= abs(raw - cb(t)) < mp.mpf('1e-30')
        ok &= (wq < mp.pi / 2) and (lo > 0)
        print(f"{n:>6} {float(wq):>10.6f} {str(wq < mp.pi/2):>9} {float(mp.cos(mp.pi/n)):>10.6f} "
              f"{float(mp.pi/2):>14.6f} {mp.nstr(lo, 6):>23}")
    print("   C - B > 0 on the OPEN interval, = 0 exactly at u = 0 and u = 2pi/n.")

    print("\nOK" if ok else "\nFAILED")
    return 0 if ok else 1


if __name__ == "__main__":
    raise SystemExit(main())
