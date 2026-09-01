#!/usr/bin/env python3
"""Verification battery for the 2026-08-28 batch-03 Type B return assimilation.

Landed alongside:
  GlobalTreeAdmissibleProduct.md          (Theorems 1-4 + claim boundary)
  ComponentLifetimeTransportIdentity.md   (Lemma A + Theorem B)

Checks (all must pass, exit 0):
  tree product   R = prod_{i,j} |z_i - c_j| <= 1; exact permutation counting
                 identity prod_pi A(pi) = R^{2(n-1)!}; min_pi A(pi) <= R^(2/n)
                 for path and star trees; selector form; equality family.
  hub budget     exists critical point with |P(c)| <= 1 and two-nearest sum
                 <= 2; per-point d1+d2 <= 2 |P(c)|^(1/n).
  spoke AM-GM    R_i(t)^2 <= (1-t)^2 (1+(2t+s_i t^2)/(n-1))^(n-1); six-root
                 straight-spoke falsifier |P(1/2)| > 1.
  mean lift      angular mean total radial inverse-lift length <= n r^(1/n).
  disc union     canonical-weight converse witness for the weighted-disc
                 representation of the unit lemniscate.
  root rays      prod_i |P(r a_i)| = exp(-sum_m r^m |S_m|^2 / m).
  trinomials     |T(tw)| <= 1 - t^m for centred trinomials with roots in the
                 closed disc; cyclic fibre mean-square identity.
  coarea         L(t) = (1/2pi) int_0^t p(s)/s ds and the alpha = 1/pi
                 integrating-factor identity for P(z) = z^2 - r^2.

Run: python3 research_corpus/Erdos1041/scripts/check_erdos1041_global_tree_admissible_product.py
"""
import cmath
import itertools
import math
import sys

import numpy as np

rng = np.random.default_rng(20260828)
FAILURES = []


def check(name, ok, detail=""):
    print(f"[{'PASS' if ok else 'FAIL'}] {name} {detail}")
    if not ok:
        FAILURES.append(name)


def critical_points(roots):
    coeffs = np.polynomial.polynomial.polyfromroots(roots)
    return np.polynomial.polynomial.polyroots(
        np.polynomial.polynomial.polyder(coeffs))


def random_roots(n, lo=0.2, hi=1.0, power=0.5):
    mags = rng.uniform(lo, hi, n) ** power
    angs = rng.uniform(0, 2 * math.pi, n)
    return mags * np.exp(1j * angs)


# ---------------------------------------------------------------- tree product
def tree_product():
    worst_R, worst_sel = 0.0, 0.0
    for _ in range(300):
        n = int(rng.integers(2, 9))
        z = random_roots(n)
        cs = critical_points(z)
        R = float(np.prod(np.abs(z[:, None] - cs[None, :])))
        worst_R = max(worst_R, R)
        worst_sel = max(worst_sel, float(np.prod(
            np.min(np.abs(z[:, None] - cs[None, :]), axis=1))))
    check("T1 R = prod_{i,j}|z_i-c_j| <= 1", worst_R <= 1 + 1e-9,
          f"worst R={worst_R:.6f}")
    check("T4 selector prod_i dist(z_i, Z(f')) <= 1", worst_sel <= 1 + 1e-9,
          f"worst={worst_sel:.6f}")

    import mpmath as mp
    mp.mp.dps = 30
    for n in (3, 4):
        z = 0.97 * np.exp(1j * np.sort(rng.uniform(0, 2 * math.pi, n)))
        cs = critical_points(z)
        R = mp.mpf(1)
        for i in range(n):
            for j in range(n - 1):
                R *= mp.mpf(abs(z[i] - cs[j]))
        prod_pi = mp.mpf(1)
        for perm in itertools.permutations(range(n)):
            A = mp.mpf(1)
            for j in range(n - 1):
                A *= abs(z[perm[j]] - cs[j]) * abs(z[perm[j + 1]] - cs[j])
            prod_pi *= A
        lhs = prod_pi ** (mp.mpf(1) / mp.factorial(n))
        rhs = R ** (mp.mpf(2) / n)
        check(f"T2 counting identity prod_pi A(pi)=R^(2(n-1)!) n={n}",
              abs(lhs - rhs) <= mp.mpf('1e-12') * max(abs(lhs), abs(rhs)),
              f"geo mean={mp.nstr(lhs, 8)} R^(2/n)={mp.nstr(rhs, 8)}")
        mins = min(float(np.prod([abs(z[perm[j]] - cs[j]) * abs(z[perm[j + 1]] - cs[j])
                                  for j in range(n - 1)]))
                   for perm in itertools.permutations(range(n)))
        check(f"T2 min_pi A(pi) <= R^(2/n) n={n}",
              mins <= float(R) ** (2 / n) + 1e-12,
              f"min={mins:.6f} bound={float(R) ** (2 / n):.6f}")

    n = 4
    z = 0.9 * np.exp(1j * np.sort(rng.uniform(0, 2 * math.pi, n)))
    cs = critical_points(z)
    best = min(
        float(np.prod([abs(z[perm[0]] - cs[k - 1]) * abs(z[perm[k]] - cs[k - 1])
                       for k in range(1, n)]))
        for perm in itertools.permutations(range(n)))
    check("T2 star tree n=4: exists pi with A(pi) <= 1", best <= 1 + 1e-12,
          f"min A={best:.6f}")
    for n in (3, 5, 8):
        z = np.exp(1j * (2 * math.pi * np.arange(n) / n))
        cs = critical_points(z)
        R = float(np.prod(np.abs(z[:, None] - cs[None, :])))
        check(f"T1 equality regular {n}-gon: R=1", abs(R - 1) < 1e-7,
              f"R={R:.12f}")


# ----------------------------------------------------------------- hub budgets
def hub_budgets():
    worst_exists, worst_point = 0.0, 0.0
    for _ in range(300):
        n = int(rng.integers(2, 9))
        z = random_roots(n)
        cs = critical_points(z)
        coeffs = np.polynomial.polynomial.polyfromroots(z)
        vals = np.abs(np.polynomial.polynomial.polyval(cs, coeffs))
        d = np.sort(np.abs(z[:, None] - cs[None, :]), axis=0)
        s2 = d[0] + d[1]
        i = int(np.argmin(vals))
        worst_exists = max(worst_exists, float(s2[i]))
        worst_point = max(worst_point, float(np.max(
            s2 / (2 * np.maximum(vals, 1e-300) ** (1.0 / n)))))
    check("H1 exists c: |P(c)|<=1 and two-nearest sum <= 2",
          worst_exists <= 2 + 1e-9, f"worst sum={worst_exists:.6f}")
    check("H2 per-point d1+d2 <= 2|P(c)|^(1/n)", worst_point <= 1 + 2e-6,
          f"worst ratio={worst_point:.8f}")


# ------------------------------------------------------------- spoke estimate
def spoke_estimate():
    worst = 0.0
    for _ in range(200):
        n = int(rng.integers(2, 8))
        z = random_roots(n)
        cs = critical_points(z)
        c = complex(cs[int(rng.integers(0, n - 1))])
        b = z - c
        i = int(rng.integers(0, n))
        si = abs(b[i]) ** 2 * float(np.sum(1.0 / np.abs(np.delete(b, i)) ** 2))
        for t in np.linspace(0.01, 0.99, 25):
            rhs = (1 - t) ** 2 * (1 + (2 * t + si * t * t) / (n - 1)) ** (n - 1)
            lhs = abs(np.prod((t * b[i] - b) / (-b))) ** 2
            worst = max(worst, lhs / rhs)
    check("S1 spoke AM-GM R_i(t)^2 <= (1-t)^2(1+(2t+s_i t^2)/(n-1))^(n-1)",
          worst <= 1 + 1e-8, f"worst ratio={worst:.10f}")
    al = 2 * math.pi / 5
    roots6 = np.array([1, -1, np.exp(1j * al), -np.exp(1j * al),
                       np.exp(-1j * al), -np.exp(-1j * al)])
    coeffs = np.polynomial.polynomial.polyfromroots(roots6)
    v = abs(np.polynomial.polynomial.polyval(0.5, coeffs))
    check("S2 six-root falsifier: straight spoke |P(1/2)| > 1", v > 1,
          f"|P(1/2)|={v:.6f}")


# ------------------------------------------------------------------ mean lift
def mean_lift():
    def total_lift(zr, r, ntheta=36, ds0=4e-3):
        coeffs = np.polynomial.polynomial.polyfromroots(zr)
        dcoeffs = np.polynomial.polynomial.polyder(coeffs)
        total = 0.0
        for th in np.linspace(0, 2 * math.pi, ntheta, endpoint=False):
            for a0 in zr:
                z, t, length = complex(a0), 0.0, 0.0
                while t < r:
                    dp = abs(np.polynomial.polynomial.polyval(z, dcoeffs))
                    step = min(ds0, (r - t)) / max(dp, 1e-12)
                    znew = z + cmath.exp(1j * th) * step
                    length += abs(znew - z)
                    z = znew
                    t = abs(np.polynomial.polynomial.polyval(z, coeffs))
                    if step < 1e-14:
                        break
                total += length
        return total / ntheta

    for n in (3, 5):
        zr = random_roots(n)
        for r in (0.4, 0.8, 1.0):
            L = total_lift(zr, r)
            bound = n * r ** (1.0 / n)
            if L > bound + 0.03:
                check(f"M1 mean-lift Lambda_bar({r}) <= n r^(1/n), n={n}",
                      False, f"L={L:.4f} bound={bound:.4f}")
                return
    check("M1 mean radial-lift Lambda_bar(r) <= n r^(1/n)", True, "(numerical)")


# --------------------------------------------------------------- disc union
def disc_union():
    for _ in range(200):
        n = int(rng.integers(2, 7))
        z = random_roots(n)
        w = rng.uniform(0, 1.6) * cmath.exp(1j * rng.uniform(0, 2 * math.pi))
        coeffs = np.polynomial.polynomial.polyfromroots(z)
        Pw = abs(np.polynomial.polynomial.polyval(w, coeffs))
        x = np.abs(w - z) ** 2
        lam = (1.0 / x) / np.sum(1.0 / x)
        m = np.sum(lam * z)
        V = np.sum(lam * np.abs(z - m) ** 2)
        G = n * float(np.prod(lam)) ** (1.0 / n)
        inside_disc = (abs(w - m) ** 2 + V) <= G + 1e-12
        inside_lem = Pw <= 1 + 1e-12
        if inside_lem != inside_disc:
            check("D1 canonical-weight disc/lemniscate membership", False,
                  f"|P(w)|={Pw:.6f} n={n}")
            return
    check("D1 canonical weight: z in K iff z in D_lambda (witness form)", True)


# ------------------------------------------------------------------ root rays
def root_rays():
    import mpmath as mp
    mp.mp.dps = 25
    for _ in range(20):
        n = int(rng.integers(3, 9))
        z = np.exp(1j * rng.uniform(0, 2 * math.pi, n))
        r = mp.mpf(float(rng.uniform(0.2, 0.9)))
        coeffs = np.polynomial.polynomial.polyfromroots(z)
        lhs = mp.mpf(1)
        for a in z:
            lhs *= abs(np.polynomial.polynomial.polyval(r * complex(a), coeffs))
        M = 1500
        Sm = [complex(np.sum(z ** m)) for m in range(1, M + 1)]
        rhs = mp.e ** (-sum(r ** m * (abs(Sm[m - 1]) ** 2) / m
                            for m in range(1, M + 1)))
        if abs(lhs - rhs) > mp.mpf('1e-12'):
            check("R1 root-ray power series", False,
                  f"diff={mp.nstr(abs(lhs - rhs), 3)}")
            return
    check("R1 prod_i |P(r a_i)| = exp(-sum_m r^m |S_m|^2/m)", True)


# ----------------------------------------------------------------- trinomials
def trinomials():
    for _ in range(50):
        m = int(rng.integers(2, 9))
        r = int(rng.integers(1, m))
        b, c = complex(rng.normal(), rng.normal()), complex(rng.normal(), rng.normal())
        coeffs = [0.0] * (m + 1)
        coeffs[0], coeffs[r], coeffs[m] = c, b, 1.0
        rt = np.polynomial.polynomial.polyroots(coeffs)
        if np.max(np.abs(rt)) > 1 + 1e-9:
            continue
        w = complex(rt[int(rng.integers(0, m))])
        for t in np.linspace(0, 1, 41):
            if abs(t ** m * w ** m + b * t ** r * w ** r + c) > 1 - t ** m + 1e-9:
                check("TR1 trinomial |T(tw)| <= 1 - t^m", False, f"m={m}")
                return
    check("TR1 centred trinomial safe spokes |T(tw)| <= 1 - t^m", True)
    for _ in range(30):
        h = complex(rng.uniform(-0.5, 0.5), rng.uniform(-0.5, 0.5))
        w = cmath.exp(1j * rng.uniform(0, 2 * math.pi)) * \
            math.sqrt(max(0.0, 1 - abs(h) ** 2)) * rng.uniform(0, 1)
        q = 4
        avg = sum(abs(h + cmath.exp(2j * math.pi * l / q) * w) ** 2
                  for l in range(q)) / q
        if abs(avg - (abs(h) ** 2 + abs(w) ** 2)) > 1e-10:
            check("TR2 cyclic fibre identity", False)
            return
    check("TR2 translated cyclic fibre mean-square identity", True)


# ------------------------------------------------------------------- coarea
def coarea():
    import mpmath as mp
    mp.mp.dps = 30
    r = mp.mpf('0.8')
    alpha = 1 / mp.pi
    r2 = r * r

    def lift_from_r(th, t):
        c, sn = mp.cos(th), mp.sin(th)
        f = lambda s: mp.mpf('0.5') * (
            (s + r2 * c) ** 2 + (r2 * sn) ** 2) ** mp.mpf('-0.25')
        if abs(sn) < mp.mpf('1e-20'):
            return r + mp.sqrt(t - r2) if c < 0 else mp.sqrt(r2 + t) - r
        return mp.quad(f, [0, t])

    def L(t):
        return (2 / mp.pi) * mp.quad(lambda th: lift_from_r(th, t), [0, mp.pi])

    def perimeter(t):
        d = t - r2
        g = lambda phi: t / (2 * ((d * d + 4 * r2 * t *
                                   mp.sin((phi - mp.pi) / 2) ** 2)) ** mp.mpf('0.25'))
        if t < r2:
            return 2 * mp.quad(g, [0, mp.pi, 2 * mp.pi])
        return mp.quad(g, [0, mp.pi, 2 * mp.pi, 3 * mp.pi, 4 * mp.pi])

    def F(t):
        lo = min(t, r2)
        out = (1 / (2 * mp.pi)) * mp.quad(
            lambda s: perimeter(s) / s, [0, lo / 2, lo])
        if t > r2:
            out += (1 / (2 * mp.pi)) * mp.quad(
                lambda s: perimeter(s) / s, [r2, r2 + (t - r2) / 2, t])
        return out

    for tv in ('0.5', '0.63', '0.7', '0.85', '0.97'):
        t = mp.mpf(tv)
        diff = abs(L(t) - F(t))
        scale = max(abs(L(t)), mp.mpf('1e-12'))
        check(f"C1 coarea L(t) = (1/2pi) int_0^t p/s at t={tv} (r=0.8)",
              diff / scale < mp.mpf('1e-4'),
              f"rel={mp.nstr(diff / scale, 3)}")
    t = mp.mpf('0.85')
    h = mp.mpf('1e-3')
    dL = (L(t + h) - L(t - h)) / (2 * h)
    tgt = perimeter(t) / (2 * mp.pi * t)
    check("C2 coarea derivative p/(2 pi t) = L'(t) at t=0.85",
          abs(dL - tgt) / tgt < mp.mpf('1e-4'),
          f"rel={mp.nstr(abs(dL - tgt) / tgt, 3)}")
    L0 = L(t)
    lhs = alpha * t ** (alpha - 1) * L0 + t ** alpha * dL
    rhs = (alpha / 2) * t ** (alpha - 1) * (2 * L0 + perimeter(t))
    check("C3 integrating factor d/dt(t^a L) = (a/2) t^(a-1) (2L+p), a=1/pi",
          abs(lhs - rhs) / abs(rhs) < mp.mpf('1e-4'),
          f"rel={mp.nstr(abs(lhs - rhs) / abs(rhs), 3)}")


def main():
    tree_product()
    hub_budgets()
    spoke_estimate()
    mean_lift()
    disc_union()
    root_rays()
    trinomials()
    coarea()
    print()
    if FAILURES:
        print("FAILURES:", FAILURES)
        sys.exit(1)
    print("ALL CHECKS PASSED")


if __name__ == "__main__":
    main()
