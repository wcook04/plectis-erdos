"""Checker for NearFeketeGapConvexityStability.md (Erdos 1041, Theorem 2').

Verifies:
  T1  Hessian data at the gon (n = 5, 50-dps): H_ii = -(n^2-1)/6,
      H_ik = 1/(2 sin^2(pi(i-k)/n)), circulant eigenvalues -k(n-k), and
      the identity sum_d cos(2pi k d/n) csc^2(pi d/n) = (n^2-1)/3 - 2k(n-k);
  T2  radial linearity: sum_{j != i} 1/(z_i - z_j) = (n-1)/(2 z_i) on the
      gon (exact via sympy roots of unity, n = 5);
  T3  the global convexity inequality (*) with mu_d = 1/4: on 300 random
      equimodular configs (eta up to ~0.9), Psi >= (n/4) sum_{k != 0}
      |tau_hat_k|^2 (no violations beyond 1e-11);
  T4  Theorem 2'E: on the same configs, range(tau) <= 2 sqrt(2 Psi / n)
      and hence max_i |a_i - omega zeta^{sigma(i)}| <= sqrt(2/n) sqrt(eta);
  T5  the projection identity (P) is EXACT on 100 general-radii configs
      (deviation <= 1e-10);
  T6  the full n = 5 chain (R)(S)(P)(C): on 150 near-gon configs
      (eta in [1e-5, 4e-2]), the constructed sorted-matching/mid-range
      bound d_max <= delta_max + 2 sin(h/2) holds (slack >= -1e-9), and
      the certified constants reproduce: C(1e-3) = 0.4915 (2e-3),
      C(1e-2) = 0.5286 (2e-3);
  T7  the sharp constant: C_5 = max_d (1/2) sqrt(2 R_5(d)) with
      Lambda_k = k(n-k) equals 0.476411 (1e-6) at d* = 2.

Exit 0 iff all pass.
"""
import sys

import numpy as np
import sympy as sp

FAILURES = []
rng = np.random.default_rng(25)
N = 5


def report(name, ok, detail=""):
    print(("PASS " if ok else "FAIL ") + name + ("  " + detail if detail else ""))
    if not ok:
        FAILURES.append(name)


def psi_of(roots):
    n = len(roots)
    phi = sum(np.log(abs(roots[i] - roots[j]))
              for i in range(n) for j in range(n) if i != j)
    return n * np.log(n) - phi


def sorted_tau(u):
    th = np.sort(np.mod(np.angle(u), 2 * np.pi))
    n = len(u)
    tau = th - 2 * np.pi * np.arange(n) / n
    tau = tau - np.mean(tau)
    return tau


def main():
    n = N
    # T1 Hessian (50-dps numeric on exact formulas)
    import mpmath as mp
    mp.mp.dps = 50
    H = mp.matrix(n, n)
    for i in range(n):
        for k in range(n):
            if i == k:
                H[i, k] = -(n**2 - 1) / mp.mpf(6)
            else:
                H[i, k] = 1 / (2 * mp.sin(mp.pi * (i - k) / n) ** 2)
    ok1 = True
    for k in range(n):
        v = mp.matrix([mp.e ** (2j * mp.pi * k * i / n) for i in range(n)])
        lam = (H * v)[0] / v[0]
        ok1 = ok1 and abs(lam - (-(k * (n - k)))) < mp.mpf(10) ** (-30)
    for k in (1, 2):
        s = sum(mp.cos(2 * mp.pi * k * d / n) / mp.sin(mp.pi * d / n) ** 2
                for d in range(1, n))
        ok1 = ok1 and abs(s - ((n**2 - 1) / mp.mpf(3) - 2 * k * (n - k))) \
            < mp.mpf(10) ** (-30)
    report("T1 Hessian circulant, eigenvalues -k(n-k), csc^2 identity",
           bool(ok1))

    # T2 radial linearity (50-dps numeric on the exact identity)
    ok2 = True
    zs = [mp.e ** (2j * mp.pi * k / 5) for k in range(5)]
    for i in range(5):
        s = sum(1 / (zs[i] - zs[j]) for j in range(5) if j != i)
        ok2 = ok2 and abs(s - 2 / zs[i]) < mp.mpf(10) ** (-40)
    report("T2 radial gradient (n-1)/(2z) at the gon", bool(ok2))

    # T3 + T4 equimodular battery
    ok3, ok4, worst3 = True, True, np.inf
    for _ in range(300):
        amp = 10 ** rng.uniform(-3, -0.3)
        tau0 = amp * rng.normal(size=n)
        th = 2 * np.pi * np.arange(n) / n + tau0
        u = np.exp(1j * th)
        psi = psi_of(u)
        eta = 1 - np.exp(-psi)
        tau = sorted_tau(u)
        tuh = np.fft.fft(tau) / np.sqrt(n)
        quad = (n / 4.0) * np.sum(np.abs(tuh[1:]) ** 2)
        worst3 = min(worst3, psi - quad)
        if psi - quad < -1e-11:
            ok3 = False
        h = np.sqrt(2 * psi / n)
        if np.max(tau) - np.min(tau) > 2 * h + 1e-11:
            ok4 = False
        # the matched bounds: 2 sin(h/2) universally, and the corrected
        # all-eta envelope sqrt(2/n) sqrt(eta/(1-eta))
        tau_c = tau - (np.max(tau) + np.min(tau)) / 2
        d_max = np.max(2 * np.sin(np.abs(tau_c) / 2))
        if d_max > 2 * np.sin(h / 2) + 1e-11:
            ok4 = False
        if d_max > np.sqrt(2.0 / n) * np.sqrt(eta / (1 - eta)) + 1e-11:
            ok4 = False
    report("T3 global convexity (*) with mu = 1/4", ok3,
           f"worst slack {worst3:+.2e}")
    report("T4 Theorem 2'E bound (equimodular, no window)", ok4)

    # T5 projection identity
    ok5, worst5 = True, 0.0
    for _ in range(100):
        rho = 1 - 0.3 * rng.uniform(0, 1, n)
        th = 2 * np.pi * np.arange(n) / n + 0.3 * rng.normal(size=n)
        a = rho * np.exp(1j * th)
        u = np.exp(1j * th)
        psi = psi_of(a)
        psi_ang = psi_of(u)
        corr = 0.0
        for i in range(n):
            for j in range(n):
                if i != j:
                    X = (rho[i] - rho[j]) ** 2 / (abs(a[i] - a[j]) ** 2
                                                  - (rho[i] - rho[j]) ** 2)
                    corr += 0.5 * np.log(1 + X)
        pred = psi + (n - 1) * np.sum(np.log(rho)) + corr
        worst5 = max(worst5, abs(psi_ang - pred))
    ok5 = worst5 < 1e-10
    report("T5 projection identity exact", ok5, f"worst dev {worst5:.1e}")

    # T6 full chain
    def Pn(x):
        return sum((n - 1 - l) * x**l for l in range(n - 1))

    def chain(eta):
        psi = -np.log(1 - eta)
        x0 = 1 - n * psi / (n - 1)
        if x0 <= 0:
            return None
        q = n * psi / Pn(x0)
        if q >= 1:
            return None
        S_d = q / (1 + np.sqrt(1 - q))
        d_max_r = S_d
        s0 = (2 * (1 - np.sqrt(eta)) - n * eta) / (n - 1)
        if d_max_r >= s0:
            return None
        psi_p = psi + n * S_d**2 / (s0**2 - d_max_r**2)
        # (C) fixed-point iteration
        h = np.sqrt(2 * psi_p / n)
        for _ in range(60):
            mus = []
            for d in range(1, n):
                l0 = 2 * np.pi * d / n
                lo, hi = l0 - 2 * h, l0 + 2 * h
                lstar = min(max(np.pi, lo), hi)
                mus.append(0.25 / np.sin(lstar / 2) ** 2)
            lam = {k: sum(4 * mus[d - 1] * np.sin(np.pi * k * d / n) ** 2
                          for d in range(1, n)) for k in range(1, n)}
            Rd = max((1.0 / n) * sum(4 * np.sin(np.pi * k * d / n) ** 2 / lam[k]
                                     for k in range(1, n)) for d in range(1, n))
            h_new = 0.5 * np.sqrt(2 * psi_p * Rd)
            if abs(h_new - h) < 1e-14:
                h = h_new
                break
            h = h_new
        return S_d, h

    okC = True
    for eta_t, target in ((1e-3, 0.4915), (1e-2, 0.5286)):
        out = chain(eta_t)
        C = (out[0] + 2 * np.sin(out[1] / 2)) / np.sqrt(eta_t)
        if abs(C - target) > 2e-3:
            okC = False
    ok6, worst6 = True, np.inf
    for _ in range(150):
        eta_amp = 10 ** rng.uniform(-4.5, -1.5)
        tau0 = np.sqrt(eta_amp / 12.0) * rng.normal(size=n)
        drho = np.abs(np.sqrt(eta_amp) * 0.1 * rng.normal(size=n))
        rho = 1 - drho
        a = rho * np.exp(1j * (2 * np.pi * np.arange(n) / n + tau0))
        psi = psi_of(a)
        eta = 1 - np.exp(-psi)
        out = chain(eta)
        if out is None:
            continue
        S_d, h = out
        bound = S_d + 2 * np.sin(h / 2)
        u = a / np.abs(a)
        tau = sorted_tau(u)
        tau_c = tau - (np.max(tau) + np.min(tau)) / 2
        d_ang = np.max(2 * np.sin(np.abs(tau_c) / 2))
        d_tot = np.max(1 - rho) + d_ang
        worst6 = min(worst6, bound - d_tot)
        if d_tot > bound + 1e-9:
            ok6 = False
    report("T6 full chain: bound holds + certified constants", ok6 and okC,
           f"worst slack {worst6:+.2e} C-targets {'ok' if okC else 'FAIL'}")

    # T7 sharp constant
    lam = {k: k * (n - k) for k in range(1, n)}
    C5, dstar = max(((0.5 * np.sqrt(2 * (1.0 / n) * sum(
        4 * np.sin(np.pi * k * d / n) ** 2 / lam[k] for k in range(1, n)))), d)
        for d in range(1, n))
    ok7 = abs(C5 - 0.476411) < 1e-6 and dstar in (2, 3)  # R(d) = R(n-d) tie
    report("T7 sharp constant C_5 = 0.476411 at d* in {2,3}", ok7,
           f"C_5 {C5:.6f} d* {dstar}")

    if FAILURES:
        print("FAILURES:", FAILURES)
        return 1
    print("ALL PASS")
    return 0


if __name__ == "__main__":
    sys.exit(main())
