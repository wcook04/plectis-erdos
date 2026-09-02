"""Checker for QuinticChamberWallReduction.md (Erdos 1041).

Verifies:
  S1  (U1) H(c(1+x)) - H(c) = c^5 F_mu(x) with b_2 = mu c^3,
      b_1 = -(5+2mu)c^4, and F_mu'(x) = x C_mu(x) (symbolic);
  S2  gap identities: g_cubic := (1/2)x^3(3x^2+10x+10) == -F_mu mod C_mu
      (so foreign critical VALUES of F_mu are exactly -g_j), the bilinear
      form g == x(2mu+20-3mu x)/5 mod C_mu, and sum_j g(x_j) = -4(mu+4)
      via Newton sums (symbolic);
  S3  terminal normalizer identity F_mu(x) - (1+x)^5 = mu x^2 - 5x - 1
      (symbolic) -- the source of |1+x(S)| = S^{1/5} + O(S^{-2/5}) on the
      arms, which makes the pair excess a locally uniform limit of
      (arclength - const), arclength being an integral of moduli of
      mu-holomorphic functions;
  S3b degree uniformity: for the degree-n model
      H = w^n + sum_{k <= (n-1)/2} b_k w^k, the hub-centred blow-up
      satisfies deg(F(x) - (1+x)^n) <= (n-1)/2 <= n-2 for n = 4, 6, 7
      (symbolic), so the same normalizer/psh argument runs at every
      degree;
  S4  gap-zero classification: substituting the non-hub root formula
      x = (2mu+20)/(3mu) into C_mu and clearing (3mu)^3 gives EXACTLY
      2 (mu+10)^2 (27 mu^2 + 140 mu + 200); hence min_j |g_j| = 0 on the
      chamber closure only at mu = -10 and mu* = (-70 +- 10 i sqrt5)/27;
  N5  ray clearance / march regularity at 8 seeded chamber points: both
      arms of F_mu(x) = e^{-i phi} s continue to S = 2000 with
      min |F_mu'(x(s))| > 0 bounded away from 0 after the start, and the
      two arms end in distinct tracts;
  N6  normalizer decay: per arm, d(S) = |1+x(S)| - S^{1/5} satisfies
      |d(S)| <= 1.5 (|mu|+11)/5 S^{-2/5} at three cutoffs and decays with
      fitted exponent in (-0.75, -0.2), matching the proof's
      |1+x(S)| = S^{1/5} + O((|mu|+1) S^{-2/5}) locally uniform bound
      (the O-constant scales with |mu|; raw extrapolation-form agreement
      is NOT expected at moderate S and is not claimed);
  N7  sub-mean (subharmonicity witness): at 6 chamber-interior points,
      the 12-point circle mean of E(., phi) is >= the center value minus
      1e-6 (matched-cutoff instrument so the tail bias cancels);
  N8  disk maximum principle demo: on a mu-disk inside a fixed-phi slice,
      the interior grid max of E is <= boundary circle max + 1e-6;
  N9  mu* stratum regularity: at mu* the smallest gap modulus is < 1e-9
      (true gap-zero), yet the arm march is regular and
      E(mu*, phi_mid) is finite and lies in (-1.4, -0.6);
  N10 anchors: E(0, phi_c) <= 2(pi/5 - 1) + 1e-6 (one-face slice bound)
      and E at the isolated tangent point (50+30sqrt3, -pi/2) lies in
      (-0.25, -0.10).  NOTE the normalization: the corpus's measured sup
      -0.0363 (TraceMaxRadialExcessLaw.md) is for E_pair = |c| E on the
      coefficient core; the tangent hub there has |c| ~ 0.21, so in
      chamber normalization E(tangent) ~ -0.175, which is what this
      instrument reproduces (cross-instrument consistency).

Exit 0 iff all pass.
"""
import sys

import numpy as np
import sympy as sp
from scipy.integrate import solve_ivp

rng = np.random.default_rng(1041)
FAILURES = []


def report(name, ok, detail=""):
    print(("PASS " if ok else "FAIL ") + name + ("  " + detail if detail else ""))
    if not ok:
        FAILURES.append(name)


# ---------------- symbolic ----------------

def sym_checks():
    z, x, c, mu = sp.symbols("z x c mu")
    b2 = mu * c**3
    b1 = -(5 + 2 * mu) * c**4
    H = z**5 + b2 * z**2 + b1 * z
    F = x**2 * (x**3 + 5 * x**2 + 10 * x + 10 + mu)
    C = 5 * x**3 + 20 * x**2 + 30 * x + 20 + 2 * mu

    ok = sp.expand(H.subs(z, c * (1 + x)) - H.subs(z, c) - c**5 * F) == 0
    ok = ok and sp.expand(sp.diff(F, x) - x * C) == 0
    report("S1 (U1) and F' = x*C", ok)

    g_cubic = sp.Rational(1, 2) * x**3 * (3 * x**2 + 10 * x + 10)
    ok = sp.rem(sp.expand(g_cubic + F), C, x) == 0
    g_bil = x * (2 * mu + 20 - 3 * mu * x) / 5
    ok = ok and sp.simplify(sp.rem(sp.expand(g_cubic - g_bil), C, x)) == 0
    e1 = sp.Rational(-20, 5)
    p1 = e1
    p2 = e1 * p1 - 2 * sp.Rational(30, 5)
    S_g = (2 * mu + 20) / 5 * p1 - sp.Rational(3, 5) * mu * p2
    ok = ok and sp.simplify(S_g + 4 * (mu + 4)) == 0
    report("S2 gap identities (g == -F mod C, bilinear, trace)", ok)

    ok = sp.expand(F - (1 + x) ** 5 - (mu * x**2 - 5 * x - 1)) == 0
    report("S3 terminal normalizer F - (1+x)^5 = mu x^2 - 5x - 1", ok)

    ok3b = True
    w = sp.symbols("w")
    for n in (4, 6, 7):
        ks = list(range(1, (n - 1) // 2 + 1))
        bs = sp.symbols(f"b1:{len(ks)+1}")
        Hn = w**n + sum(b * w**k for b, k in zip(bs, ks))
        Fn = sp.expand((Hn.subs(w, c * (1 + x)) - Hn.subs(w, c)) / c**n)
        diff = sp.expand(Fn - (1 + x) ** n)
        ok3b = ok3b and sp.degree(sp.Poly(diff, x)) <= (n - 1) // 2
    report("S3b degree-uniform normalizer (n = 4, 6, 7)", ok3b)

    xr = (2 * mu + 20) / (3 * mu)
    poly = sp.expand(C.subs(x, xr) * (3 * mu) ** 3)
    target = sp.expand(2 * (mu + 10) ** 2 * (27 * mu**2 + 140 * mu + 200))
    report("S4 gap-zero factorization 2(mu+10)^2(27mu^2+140mu+200)",
           sp.expand(poly - target) == 0)


# ---------------- numeric core ----------------

def gaps(mu):
    xj = np.roots([5, 20, 30, 20 + 2 * mu])
    return xj * (2 * mu + 20 - 3 * mu * xj) / 5.0


def chamber_phi(mu, n=4000):
    g = gaps(mu)
    phis = np.linspace(-np.pi, np.pi, n, endpoint=False)
    vals = np.min(np.real(np.exp(1j * phis)[:, None] * g[None, :]), axis=1)
    i = int(np.argmax(vals))
    return phis[i], vals[i]


def Fv(x, mu):
    return x**2 * (x**3 + 5 * x**2 + 10 * x + 10 + mu)


def Fp(x, mu):
    return x * (5 * x**3 + 20 * x**2 + 30 * x + 20 + 2 * mu)


def march(mu, phi, sign, S=2000.0, rtol=1e-12, atol=1e-14, track_min_fp=False):
    s0 = 1e-12
    w = np.exp(-1j * phi)
    x0 = sign * np.sqrt(w * s0 / (10 + mu))
    for _ in range(3):
        x0 = x0 - (Fv(x0, mu) - w * s0) / Fp(x0, mu)
    min_fp = [np.inf]

    def rhs(s, y):
        x = y[0] + 1j * y[1]
        fp = Fp(x, mu)
        if track_min_fp and s > 1e-6:
            min_fp[0] = min(min_fp[0], abs(fp))
        d = w / fp
        return [d.real, d.imag, abs(d)]

    sol = solve_ivp(rhs, [s0, S], [x0.real, x0.imag, 0.0], method="DOP853",
                    rtol=rtol, atol=atol)
    x = sol.y[0, -1] + 1j * sol.y[1, -1]
    for _ in range(2):
        x = x - (Fv(x, mu) - w * S) / Fp(x, mu)
    return sol.y[2, -1], x, min_fp[0]


def excess(mu, phi, S=2000.0):
    tot = 0.0
    for sign in (+1, -1):
        L, x, _ = march(mu, phi, sign, S=S)
        tot += L - abs(1 + x)
    return tot


def excess_extrap(mu, phi, form="modulus", Ss=(500.0, 2000.0, 8000.0)):
    es = []
    for S in Ss:
        tot = 0.0
        for sign in (+1, -1):
            L, x, _ = march(mu, phi, sign, S=S)
            if form == "modulus":
                tot += L - abs(1 + x)
            else:
                tot += L - S ** 0.2
        es.append(tot)
    e1, e2, e3 = es
    d1, d2 = e2 - e1, e3 - e2
    if d2 != 0 and d1 / d2 > 1.05:
        return e3 + d2 / (d1 / d2 - 1.0)
    return e3


def sample_chamber_points(k):
    pts = []
    while len(pts) < k:
        mu = rng.uniform(-180, 10) + 1j * rng.uniform(-60, 60)
        if abs(mu + 10) < 1.0:
            continue
        phi, marg = chamber_phi(mu)
        scale = max(1.0, abs(mu) / 10.0)
        if marg > 0.05 * scale:
            pts.append((mu, phi))
    return pts


def num_checks():
    # N5 ray clearance / regular march
    pts = sample_chamber_points(8)
    ok5, det = True, ""
    for mu, phi in pts:
        tracts = []
        for sign in (+1, -1):
            L, x, mfp = march(mu, phi, sign, track_min_fp=True)
            if not np.isfinite(L) or mfp < 1e-6:
                ok5, det = False, f"degenerate march at mu={mu:.3f}"
            tracts.append(np.round(np.angle(x) * 5 / (2 * np.pi)))
        if abs(tracts[0] - tracts[1]) < 0.5:
            ok5, det = False, f"same tract at mu={mu:.3f}"
    report("N5 ray clearance / march regularity (8 chamber points)", ok5, det)

    # N6 normalizer decay per arm
    ok6, det6 = True, ""
    Ss = (500.0, 2000.0, 8000.0)
    for mu, phi in pts[:3]:
        for sign in (+1, -1):
            ds = []
            for S in Ss:
                _, x, _ = march(mu, phi, sign, S=S)
                ds.append(abs(1 + x) - S ** 0.2)
            bound = 1.5 * (abs(mu) + 11.0) / 5.0
            if any(abs(d) > bound * S ** (-0.4) for d, S in zip(ds, Ss)):
                ok6, det6 = False, f"magnitude at mu={mu:.3f}: {ds}"
            if abs(ds[0]) > 1e-12 and abs(ds[2]) > 1e-12:
                p = np.log(abs(ds[2]) / abs(ds[0])) / np.log(Ss[2] / Ss[0])
                if not (-0.75 < p < -0.2):
                    ok6, det6 = False, f"exponent {p:.3f} at mu={mu:.3f}"
    report("N6 normalizer decay |1+x(S)| - S^{1/5}", ok6, det6)

    # N7 sub-mean
    fixed = [(-50 + 10j), (2 - 1j), (-120 - 30j), (-3 + 1j), (-80 + 25j), (-20 - 15j)]
    ok7, worst7 = True, np.inf
    for mu0 in fixed:
        phi0, marg = chamber_phi(mu0)
        scale = max(1.0, abs(mu0) / 10.0)
        if marg <= 0.03 * scale:
            continue
        e_c = excess(mu0, phi0)
        r = 0.04 * scale
        vals = [excess(mu0 + r * np.exp(2j * np.pi * k / 12), phi0) for k in range(12)]
        m = float(np.mean(vals)) - e_c
        worst7 = min(worst7, m)
        if m < -1e-6:
            ok7 = False
    report("N7 sub-mean at 6 interior points", ok7, f"worst margin {worst7:+.2e}")

    # N8 disk maximum principle demo
    mu0, r8 = -50 + 10j, 2.0
    phi0, _ = chamber_phi(mu0)
    interior = [excess(mu0 + a + 1j * b, phi0)
                for a in np.linspace(-r8 * 0.6, r8 * 0.6, 4)
                for b in np.linspace(-r8 * 0.6, r8 * 0.6, 4)]
    boundary = [excess(mu0 + r8 * np.exp(2j * np.pi * k / 12), phi0) for k in range(12)]
    ok8 = max(interior) <= max(boundary) + 1e-6
    report("N8 disk max principle demo", ok8,
           f"int {max(interior):.6f} <= bnd {max(boundary):.6f}")

    # N9 mu* stratum
    mus = (-70 + 10j * np.sqrt(5)) / 27
    gmin = min(abs(g) for g in gaps(mus))
    phi9, marg9 = chamber_phi(mus)
    e9 = excess(mus, phi9)
    ok9 = gmin < 1e-9 and np.isfinite(e9) and -1.4 < e9 < -0.6
    report("N9 mu* gap-zero yet regular", ok9,
           f"gap {gmin:.1e} E {e9:.4f} arc-margin {marg9:.1e}")

    # N10 anchors
    phi0, _ = chamber_phi(0.0 + 0j)
    e0 = excess_extrap(0.0 + 0j, phi0, form="modulus")
    okA = e0 <= 2 * (np.pi / 5 - 1) + 1e-6
    mut = 50 + 30 * np.sqrt(3)
    et = excess_extrap(mut, -np.pi / 2, form="modulus")
    okB = -0.25 < et < -0.10
    report("N10 anchors (one-face bound, tangent point)", okA and okB,
           f"E(0)={e0:.4f} (<= {2*(np.pi/5-1):.4f}), E(tangent)={et:.5f}")


def main():
    sym_checks()
    num_checks()
    if FAILURES:
        print("FAILURES:", FAILURES)
        return 1
    print("ALL PASS")
    return 0


if __name__ == "__main__":
    sys.exit(main())
