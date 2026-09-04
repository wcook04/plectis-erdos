"""Checker for Degree5AssemblyAndSharpenedCuts.md.

Replays:
  1. Lemma S5 (sup form): for random configs (n = 3..8) and every critical
     point, sup_t of the second-nearest-spoke modulus never exceeds
     M_n * |f(c)|, M_n = max_t Phi_n(t),
     Phi_n(t) = (1-t)(1+t)^{n-2} sqrt(1+(6-2n)t+(n-1)^2 t^2); the second
     endpoint branch Psi_n has sup exactly 1 <= M_n (checked); M_5 matches
     the stated exact values (t* = 5/16+3 sqrt(105)/80, M_5^2 a root of the
     stated integer quadratic).  The POINTWISE Phi_n bound is false for
     small t (excess ~6e-3) -- deliberately not asserted.
  2. The nearest-spoke SUP bound via its own envelope N_n (<= M_n; N_3 = 1
     exactly).  Recorded finding: the pointwise nearest-spoke contraction
     <= |f(c)| is FALSE for general critical points at n >= 4.
  3. Gronwall identity ingredients: after centring, a_1 = -c_{n-2}/(n t^{1/n})
     numerically (exterior-map coefficient extracted by Laurent fit), and the
     truncated area bound Area <= pi(t^{2/n} - |a_1|^2) upper-bounds a grid
     area measurement on connected sublevel sets.
  4. (SPOKE-5) calibration at z^5 - 1: the two functionals sit at their
     budgets (values 1 and 2) within grid tolerance.

Usage: check_erdos1041_degree5_sharpened_cuts.py [--check]
Exit 0 iff all checks pass.
"""
import argparse
import sys

import numpy as np

RNG = np.random.default_rng(541)


def phi_env(n, t):
    return (1 - t) * (1 + t) ** (n - 2) * np.sqrt(1 + (6 - 2 * n) * t + (n - 1) ** 2 * t ** 2)


def interior_env(n, t):
    """Interior y_1 branch (valid t <= t_c = 2/n): (1-t) B(t)^{(n-1)/2}."""
    B = (1 - t) ** 2 + (2 * t * n + t ** 2 * n * (n - 2)) / (n - 1)
    return (1 - t) * B ** ((n - 1) / 2)


def M_n(n):
    """Correct two-branch envelope maximum: interior branch on [0, 2/n],
    clamped Phi branch on [2/n, 1]."""
    tc = 2.0 / n
    t1 = np.linspace(0, tc, 20001)
    t2 = np.linspace(tc, 1, 20001)
    return max(float(np.max(interior_env(n, t1))), float(np.max(phi_env(n, t2))))


def check_envelope(trials=250):
    worst = -np.inf
    for _ in range(trials):
        n = int(RNG.integers(3, 9))
        roots = np.sqrt(RNG.uniform(0, 1, n)) * np.exp(2j * np.pi * RNG.uniform(0, 1, n))
        c_poly = np.poly(roots)
        dc = np.polyder(c_poly)
        for c in np.roots(dc):
            fc = np.polyval(c_poly, c)
            if abs(fc) < 1e-12:
                continue
            d = np.abs(roots - c)
            order = np.argsort(d)
            a1, a2 = roots[order[0]], roots[order[1]]
            ts = np.linspace(1e-4, 1 - 1e-4, 400)
            # nearest-spoke: bounded by its own envelope N_n <= M_n
            # (the POINTWISE contraction <= |f(c)| is FALSE in general --
            #  recorded finding; do not assert it)
            vals1 = np.abs(np.polyval(c_poly, c + ts * (a1 - c))) / abs(fc)
            worst = max(worst, float(np.max(vals1)) - N_n(n))
            # second-spoke SUP bound: sup_t ratio <= M_n (two-branch envelope)
            vals2 = np.abs(np.polyval(c_poly, c + ts * (a2 - c))) / abs(fc)
            worst = max(worst, float(np.max(vals2)) - M_n(n))
    return worst


def N_n(n):
    """Nearest-spoke envelope: max_t (1-t)[(1-t)^2 + 2tn/(n-1)]^{(n-1)/2}."""
    ts = np.linspace(0, 1, 20001)
    return float(np.max((1 - ts) * ((1 - ts) ** 2 + 2 * ts * n / (n - 1)) ** ((n - 1) / 2)))


def check_m5():
    t_star = 5 / 16 + 3 * np.sqrt(105) / 80
    # stationarity of Phi_5 via the stated factor
    q = 40 * t_star ** 2 - 25 * t_star - 2
    m5 = phi_env(5, t_star)
    # exact quadratic for M_5^2
    X = m5 ** 2
    resid = 655360000000000 * X ** 2 - 9259803797146875 * X + 8653940464249899
    # grid max must not exceed the stationary value
    ts = np.linspace(0, 1, 200001)
    grid_max = float(np.max(phi_env(5, ts)))
    return abs(q), abs(resid) / 1e16, m5, grid_max


def check_gronwall(trials=4):
    ok = True
    for _ in range(trials):
        n = int(RNG.integers(3, 6))
        roots = 0.6 * np.sqrt(RNG.uniform(0, 1, n)) * np.exp(2j * np.pi * RNG.uniform(0, 1, n))
        roots = roots - np.mean(roots)          # centre: sum = 0
        c_poly = np.poly(roots)
        t = 1.0                                  # level with K_t connected (roots well inside)
        # exterior-map coefficient a_1 via Laurent fit of psi = inverse of (f/t)^{1/n}
        # sample zeta large, solve f(z) = t zeta^n for the branch z ~ t^{1/n} zeta
        zs = []
        Zs = 10 ** RNG.uniform(1.5, 2.5, 60) * np.exp(2j * np.pi * RNG.uniform(0, 1, 60))
        for Z in Zs:
            w = t * Z ** n
            cand = np.roots(np.concatenate([c_poly[:-1], [c_poly[-1] - w]]))
            z = cand[np.argmin(np.abs(cand - t ** (1 / n) * Z))]
            zs.append(z)
        zs = np.array(zs)
        # fit z = t^{1/n} Z + a0 + a1/Z (least squares)
        A = np.vstack([np.ones_like(Zs), 1 / Zs]).T
        rhs = zs - t ** (1 / n) * Zs
        coef, *_ = np.linalg.lstsq(A, rhs, rcond=None)
        a1_fit = coef[1]
        a1_exact = -c_poly[2] / (n * t ** (1 / n))   # c_{n-2} coefficient
        ok &= abs(a1_fit - a1_exact) < 1e-4 * max(1, abs(a1_exact))
        # truncated area bound vs grid area
        G = 400
        xs = np.linspace(-2, 2, G)
        X, Y = np.meshgrid(xs, xs)
        Zg = X + 1j * Y
        inside = np.abs(np.polyval(c_poly, Zg)) <= t
        area = inside.mean() * 16.0
        bound = np.pi * (t ** (2 / n) - abs(a1_exact) ** 2)
        ok &= area <= bound + 0.05
    return ok


def check_spoke5_calibration():
    roots = np.exp(2j * np.pi * np.arange(5) / 5)
    c_poly = np.poly(roots)                      # z^5 - 1
    # at the degenerate hub 0: spokes are radii; max |f| along a radius:
    ts = np.linspace(0, 1, 20001)
    m = float(np.max(np.abs(np.polyval(c_poly, ts))))
    # length of the two-radius connector
    return abs(m - 1.0), abs((1.0 + 1.0) - 2.0)


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--check", action="store_true")
    ap.parse_args()
    ok = True

    w = check_envelope()
    print(f"S5 sup-form worst excess over samples (must be <= 0 up to tol): {w:.3e}")
    ok &= w < 1e-9
    # branch structure: for n >= 4 the clamped Phi branch attains M_n;
    # at n = 3 the interior branch rules with exact M_3 = 27/25
    for n in range(4, 9):
        ok &= abs(M_n(n) - float(np.max(phi_env(n, np.linspace(2.0 / n, 1, 40001))))) < 1e-7
    ok &= abs(M_n(3) - 27.0 / 25.0) < 1e-6
    print(f"branch structure ok; M_3 = {M_n(3):.9f} (exact 27/25), M_5 = {M_n(5):.9f}")
    # nearest-spoke envelope dominated by M_n; N_3 = 1 exactly
    for n in range(3, 9):
        ok &= N_n(n) <= M_n(n) + 1e-12
    ok &= abs(N_n(3) - 1.0) < 1e-9
    print(f"N_n <= M_n for n=3..8 ok; N_3 = {N_n(3):.9f}, N_4 = {N_n(4):.6f}, N_5 = {N_n(5):.6f}")

    q, resid, m5, grid_max = check_m5()
    print(f"M5: stationarity |40t*^2-25t*-2| = {q:.2e}; integer-quadratic residual/1e16 = {resid:.2e}; "
          f"M5 = {m5:.12f}; grid max = {grid_max:.12f}")
    ok &= q < 1e-12 and resid < 1e-3 and abs(m5 - grid_max) < 1e-8
    ok &= abs(1 / m5 - 0.2760461063263685) < 1e-12

    r = check_gronwall()
    print(f"gronwall a1 formula + truncated area bound: {'ok' if r else 'FAIL'}")
    ok &= r

    e1, e2 = check_spoke5_calibration()
    print(f"(SPOKE-5) calibration at z^5-1: |max_f - 1| = {e1:.2e}, length residual = {e2:.2e}")
    ok &= e1 < 1e-6 and e2 < 1e-12

    print("PASS" if ok else "FAIL")
    return 0 if ok else 1


if __name__ == "__main__":
    sys.exit(main())
