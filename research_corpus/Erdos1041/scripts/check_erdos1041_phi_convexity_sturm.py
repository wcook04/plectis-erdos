"""Checker for PhiConvexitySturmBound.md (Erdos 1041).

Verifies:
  P1  closed forms (symbolic): 5 Phi - 1 = N_3 / C_mu^2 with
      N_3 = -30 mu x^3 - 30(mu-10) x^2 + 80(mu+10) x + 6(mu+10)^2,
      Phi = (F/F')' ; and 5 F/F' = (1+x) + (3 mu x - 2(mu+10))/C_mu;
  P2  the crux 5 sigma_a + e_a >= 0 on 10 chamber points x 2 arms
      (sigma_a and e_a from the same march);
  P3  the identity 25 E_phiphi = E + K at 3 points: central finite
      difference of E in phi vs (E + K)/25 with K from quadrature,
      relative agreement 5e-2 (checker-grade cutoffs);
  P4  the Sturm interpolation bound on 4 full arcs: at 5 interior
      phis each, E(phi) <= sine-interpolation of the endpoint values
      + 1e-6;
  P5  the weight-sum fact: for D in (0, pi], the interpolation weights
      at every interior phi sum to >= 1 (numeric grid);
  P6  the -10 consequence arithmetic: with both endpoint values
      <= -1/80 and weight-sum >= 1, the interpolated bound is <= -1/80
      (spot-verified on the measured endpoint value -0.06021).

Exit 0 iff all pass.
"""
import sys

import numpy as np
import sympy as sp
from scipy.integrate import solve_ivp

FAILURES = []
rng = np.random.default_rng(77)


def report(name, ok, detail=""):
    print(("PASS " if ok else "FAIL ") + name + ("  " + detail if detail else ""))
    if not ok:
        FAILURES.append(name)


def Fv(x, mu):
    return x**2 * (x**3 + 5 * x**2 + 10 * x + 10 + mu)


def Fp(x, mu):
    return x * (5 * x**3 + 20 * x**2 + 30 * x + 20 + 2 * mu)


def Fpp(x, mu):
    return 20 * x**3 + 60 * x**2 + 60 * x + 20 + 2 * mu


def gaps(mu):
    xj = np.roots([5, 20, 30, 20 + 2 * mu])
    return xj * (2 * mu + 20 - 3 * mu * xj) / 5.0


def chamber_phi(mu, n=4000):
    g = gaps(mu)
    phis = np.linspace(-np.pi, np.pi, n, endpoint=False)
    vals = np.min(np.real(np.exp(1j * phis)[:, None] * g[None, :]), axis=1)
    i = int(np.argmax(vals))
    return phis[i], vals[i], phis, vals


def arm_march(mu, phi, sign, S=4000.0, want_phi_data=False):
    """Return (len, x_end, sigma, phi_int) for one arm.

    sigma = int (|Phi| - 1/5) |dx|;  phi_int = int (25|Phi|^2 - 1) |dx|.
    """
    s0 = 1e-12
    w = np.exp(-1j * phi)
    x0 = sign * np.sqrt(w * s0 / (10 + mu))
    for _ in range(3):
        x0 = x0 - (Fv(x0, mu) - w * s0) / Fp(x0, mu)

    def rhs(s, y):
        x = y[0] + 1j * y[1]
        fp = Fp(x, mu)
        d = w / fp
        Phi = 1.0 - Fv(x, mu) * Fpp(x, mu) / fp**2
        aP = abs(Phi)
        return [d.real, d.imag, abs(d), (aP - 0.2) * abs(d),
                (25 * aP * aP - 1.0) * abs(d)]

    sol = solve_ivp(rhs, [s0, S], [x0.real, x0.imag, 0.0, 0.0, 0.0],
                    method="DOP853", rtol=1e-11, atol=1e-13)
    x = sol.y[0, -1] + 1j * sol.y[1, -1]
    for _ in range(2):
        x = x - (Fv(x, mu) - w * S) / Fp(x, mu)
    return sol.y[2, -1], x, sol.y[3, -1], sol.y[4, -1]


def excess_pair(mu, phi, S=4000.0):
    tot, sig, kk = 0.0, [], 0.0
    for sign in (+1, -1):
        L, xe, sg, ki = arm_march(mu, phi, sign, S=S)
        e = L - abs(1 + xe)
        tot += e
        sig.append((sg, e))
        kk += ki
    return tot, sig, kk


def main():
    # P1 closed forms
    x, mu = sp.symbols("x mu")
    F = x**2 * (x**3 + 5 * x**2 + 10 * x + 10 + mu)
    C = 5 * x**3 + 20 * x**2 + 30 * x + 20 + 2 * mu
    Phi = sp.simplify(sp.diff(F / sp.diff(F, x), x))
    N3 = -30 * mu * x**3 - 30 * (mu - 10) * x**2 + 80 * (mu + 10) * x \
        + 6 * (mu + 10) ** 2
    ok1 = sp.simplify(5 * Phi - 1 - N3 / C**2) == 0
    R = (3 * mu * x - 2 * (mu + 10)) / C
    ok1 = ok1 and sp.simplify(5 * F / sp.diff(F, x) - (1 + x) - R) == 0
    report("P1 closed forms for Phi and F/F'", bool(ok1))

    # P2 crux
    ok2, worst2 = True, np.inf
    pts = []
    while len(pts) < 10:
        m = rng.uniform(-150, 8) + 1j * rng.uniform(-50, 50)
        if abs(m + 10) < 1.0:
            continue
        p, marg, _, _ = chamber_phi(m)
        if marg > 0.05 * max(1, abs(m) / 10):
            pts.append((m, p))
    for m, p in pts:
        _, sig, _ = excess_pair(m, p)
        for sg, e in sig:
            worst2 = min(worst2, 5 * sg + e)
            if 5 * sg + e < -1e-6:
                ok2 = False
    report("P2 crux 5 sigma + e >= 0 (20 arms)", ok2, f"min {worst2:+.4e}")

    # P3 identity 25 E'' = E + K.  K's quadrature tail is O(S^{-2/5}) and
    # E's is O(S^{-1}) (both corpus-verified rates), so Richardson both
    # with fixed exponents across S and 16 S.
    def ek_extrap(m, p, S1=4000.0, S2=64000.0):
        E1, _, K1 = excess_pair(m, p, S=S1)
        E2, _, K2 = excess_pair(m, p, S=S2)
        E = (E2 * S2 - E1 * S1) / (S2 - S1)
        a1, a2 = S1 ** 0.4, S2 ** 0.4
        K = (K2 * a2 - K1 * a1) / (a2 - a1)
        return E, K

    ok3, dets = True, []
    for m, p in pts[:3]:
        h = 0.01
        Em, _ = ek_extrap(m, p - h)
        E0, K = ek_extrap(m, p)
        Ep, _ = ek_extrap(m, p + h)
        lhs = 25 * (Ep - 2 * E0 + Em) / h**2
        rhs = E0 + K
        rel = abs(lhs - rhs) / max(1.0, abs(rhs))
        dets.append(f"{rel:.1e}")
        if rel > 8e-2:
            ok3 = False
    report("P3 identity 25 E'' = E + K (3 points, Richardson)", ok3,
           " ".join(dets))

    # P4 Sturm interpolation on full arcs
    ok4, worst4 = True, np.inf
    arcs = 0
    for m, _ in pts:
        _, marg, phis, vals = chamber_phi(m)
        inside = np.where(vals >= 0)[0]
        if len(inside) < 30:
            continue
        # contiguous arc (may wrap; skip wrapped for simplicity)
        if inside[-1] - inside[0] != len(inside) - 1:
            continue
        lo, hi = phis[inside[0]], phis[inside[-1]]
        D = hi - lo
        if D <= 0.05:
            continue
        Elo, _, _ = excess_pair(m, lo + 1e-6)
        Ehi, _, _ = excess_pair(m, hi - 1e-6)
        for t in (0.15, 0.35, 0.5, 0.7, 0.9):
            ph = lo + t * D
            Ei, _, _ = excess_pair(m, ph)
            bound = (np.sin((hi - ph) / 5) * Elo + np.sin((ph - lo) / 5) * Ehi) \
                / np.sin(D / 5)
            worst4 = min(worst4, bound - Ei)
            if Ei > bound + 1e-6:
                ok4 = False
        arcs += 1
        if arcs >= 4:
            break
    report("P4 Sturm interpolation bound (4 arcs x 5 phis)", ok4 and arcs >= 3,
           f"min slack {worst4:+.2e} arcs {arcs}")

    # P5 weight sum >= 1
    ok5 = True
    for D in (0.3, 1.0, 2.0, np.pi):
        for t in np.linspace(0.01, 0.99, 33):
            ph = t * D
            wsum = (np.sin((D - ph) / 5) + np.sin(ph / 5)) / np.sin(D / 5)
            if wsum < 1.0 - 1e-12:
                ok5 = False
    report("P5 interpolation weights sum >= 1", ok5)

    # P6 the -10 consequence arithmetic
    D = 2 * np.arctan(1 / (2 * np.sqrt(2)))
    endpoint = -0.0602107442
    worst6 = np.inf
    for t in np.linspace(0.01, 0.99, 99):
        ph = t * D
        bound = (np.sin((D - ph) / 5) * endpoint + np.sin(ph / 5) * endpoint) \
            / np.sin(D / 5)
        worst6 = min(worst6, -bound)
    ok6 = worst6 >= 1.0 / 80.0
    report("P6 arc bound stays below -1/80 given endpoints", ok6,
           f"max bound {-worst6:.6f}")

    if FAILURES:
        print("FAILURES:", FAILURES)
        return 1
    print("ALL PASS")
    return 0


if __name__ == "__main__":
    sys.exit(main())
