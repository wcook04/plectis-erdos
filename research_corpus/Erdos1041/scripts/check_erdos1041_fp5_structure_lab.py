"""Checker for FreePointFP5StructureLab.md (Erdos 1041).

Verifies:
  F1  star-ray closed form: prod_{t=0}^{4}(1 - u w^t) = 1 - u^5 (symbolic)
      and G_5(R w^j) = (1 - R^10)^{1/5} numerically at several R;
  F2  exact ray law at 0: G_5(t u) - 1 ~ -(1/25) t^2 |q_1(u)|^2 for
      generic u, and ~ -(1/50) t^4 |q_2(u)|^2 on balanced directions
      (q_1 = 0), fitted ratios within 3e-3;
  F3  row ceiling h_j <= H_j on 3000 random closed-disk configs
      (H_j the modulus-only bound from d_jj = 1-rho_j^2 and
      d_jk <= 1 + rho_j rho_k);
  F4  ROWCERT+ ingredient chain: the identity S_5 = 5 - E + sum Psi(h_j)
      (1e-11), the Fourier energy E = (1/5) sum_r |p_r|^2/r (1e-8 with
      r <= 600), Phi increasing on [-3, 3], and the weighted
      Cauchy-Schwarz h_j^2 <= (E/5) L_j on 3000 configs;
  F5  certificate radii: the all-equal-modulus threshold of
      (1/5) sum_j Phi(H_j) L_j = 1 is rho_* = 0.9244519 (2e-5), and the
      m->infty equation (s - log(1+s)) log(1/(1-s)) = log^2(1+s) holds
      at s = 0.803461721264 to 1e-9 (rho_infty = 0.8963603);
  F6  residual arithmetic: (1 - rho_*^10)^{1/5} = 0.885401 (2e-4) -- the
      sup of G_5 on the ROWCERT+ failure set, attained at the 5-star;
  F7  zero-insertion identity S_5(c_1..c_4, 0) = 1 + sum_j B_j^{4/5}
      (1e-11) on random 4-point configs;
  F8  the 1+2+2 graded star beats the exact 5-star at R = 0.9 by
      >= 0.055 in G_5, while staying below 1 by >= 0.015.

Exit 0 iff all pass.
"""
import sys

import numpy as np
import sympy as sp

FAILURES = []
rng = np.random.default_rng(41)


def report(name, ok, detail=""):
    print(("PASS " if ok else "FAIL ") + name + ("  " + detail if detail else ""))
    if not ok:
        FAILURES.append(name)


def G(c):
    c = np.asarray(c, dtype=complex)
    m = len(c)
    d = np.abs(1.0 - np.conj(c)[:, None] * c[None, :])
    rows = np.exp(np.sum(np.log(d), axis=1) / m)
    return float(np.sum(rows) / m), rows, d


def rand_cfg(m=5, rmax=0.95, n=1):
    r = rng.uniform(0, rmax, (n, m)) ** 0.7
    th = rng.uniform(0, 2 * np.pi, (n, m))
    return r * np.exp(1j * th)


def main():
    # F1
    u, w = sp.symbols("u w")
    prod = sp.expand(sp.prod([1 - u * w**t for t in range(5)]))
    cyc = 1 + w + w**2 + w**3 + w**4  # minimal polynomial of a primitive root
    red = sp.rem(sp.Poly(prod, w), sp.Poly(cyc, w)).as_expr()
    ok1 = sp.simplify(sp.expand(red - (1 - u**5))) == 0
    okn = True
    for R in (0.3, 0.7, 0.95):
        c = R * np.exp(2j * np.pi * np.arange(5) / 5)
        g, _, _ = G(c)
        okn = okn and abs(g - (1 - R**10) ** 0.2) < 1e-13
    report("F1 star-ray closed form (symbolic + numeric)", bool(ok1) and okn)

    # F2 ray law
    uvec = rand_cfg(5, 1.0, 1)[0]
    uvec = uvec / np.max(np.abs(uvec))
    q1 = np.sum(uvec)
    ts = (1e-3, 3e-4)
    rats = []
    for t in ts:
        g, _, _ = G(t * uvec)
        rats.append((1.0 - g) / (t**2 * abs(q1) ** 2 / 25.0))
    ok2a = all(abs(r - 1) < 3e-3 for r in rats)
    # balanced direction: pair (a, -a, 0, 0, 0): q1 = 0, q2 = 2a^2
    a = 0.7 + 0.2j
    ub = np.array([a, -a, 0, 0, 0])
    q2 = np.sum(ub**2)
    rats_b = []
    for t in (3e-2, 1e-2):
        g, _, _ = G(t * ub)
        rats_b.append((1.0 - g) / (t**4 * abs(q2) ** 2 / 50.0))
    ok2b = all(abs(r - 1) < 3e-3 for r in rats_b)
    report("F2 exact ray law (generic t^2, balanced t^4)", ok2a and ok2b,
           f"{rats[0]:.5f} {rats_b[0]:.5f}")

    # F3 + F4
    worst3, worst_cs, worst_id, worst_E = -np.inf, -np.inf, 0.0, 0.0
    for _ in range(30):
        C = rand_cfg(5, 0.95, 100)
        for c in C:
            g, rows, d = G(c)
            m = 5
            rho = np.abs(c)
            h = np.log(rows)
            H = (np.log(np.maximum(1 - rho**2, 1e-300))
                 + (np.sum(np.log(1 + rho[:, None] * rho[None, :]), axis=1)
                    - np.log(1 + rho**2))) / m
            worst3 = max(worst3, float(np.max(h - H)))
            E = -np.sum(h)
            L = -np.log(1 - rho**2)
            worst_cs = max(worst_cs, float(np.max(h**2 - (E / m) * L)))
            S = np.sum(rows)
            Psi = np.exp(h) - 1 - h
            worst_id = max(worst_id, abs(S - (m - E + np.sum(Psi))))
            # Fourier energy
            rs = np.arange(1, 601)
            p = np.array([np.sum(c**r) for r in rs])
            E_f = float(np.sum(np.abs(p) ** 2 / rs) / m)
            worst_E = max(worst_E, abs(E - E_f))
    report("F3 row ceiling h_j <= H_j (3000 configs)", worst3 < 1e-12,
           f"max violation {worst3:.2e}")
    phi_grid = np.linspace(-3, 3, 601)
    safe = np.where(np.abs(phi_grid) > 1e-8, phi_grid, 1.0)
    Phi = np.where(np.abs(phi_grid) > 1e-8,
                   (np.exp(safe) - 1 - safe) / safe**2, 0.5)
    ok_phi = bool(np.all(np.diff(Phi) > 0))
    ok4 = worst_id < 1e-11 and worst_E < 1e-8 and worst_cs < 1e-12 and ok_phi
    report("F4 identity + Fourier energy + Phi increasing + Cauchy-Schwarz",
           ok4, f"id {worst_id:.1e} E {worst_E:.1e} CS {worst_cs:.1e}")

    # F5 radii
    def cert_lhs_equal(rho, m=5):
        L = -np.log(1 - rho**2)
        H = (np.log(1 - rho**2) + (m - 1) * np.log(1 + rho**2)) / m
        Ph = (np.exp(H) - 1 - H) / H**2 if abs(H) > 1e-12 else 0.5
        return Ph * L

    lo, hi = 0.8, 0.99
    for _ in range(60):
        mid = 0.5 * (lo + hi)
        if cert_lhs_equal(mid) < 1.0:
            lo = mid
        else:
            hi = mid
    rho_star = 0.5 * (lo + hi)
    s = 0.803461721264
    eq = (s - np.log(1 + s)) * np.log(1 / (1 - s)) - np.log(1 + s) ** 2
    ok5 = abs(rho_star - 0.9244519) < 2e-5 and abs(eq) < 1e-9 \
        and abs(np.sqrt(s) - 0.8963603) < 1e-6
    report("F5 certificate radii (m=5 threshold, m->infty equation)", ok5,
           f"rho_* {rho_star:.7f} eq-residual {eq:.1e}")

    # F6 residual
    res = (1 - rho_star**10) ** 0.2
    report("F6 residual sup G on failure set = 0.885401", abs(res - 0.885401) < 2e-4,
           f"{res:.6f}")

    # F7 zero-insertion identity
    ok7, worst7 = True, 0.0
    for _ in range(200):
        c4 = rand_cfg(4, 0.95, 1)[0]
        c5 = np.concatenate([c4, [0.0]])
        g5, rows5, _ = G(c5)
        d4 = np.abs(1.0 - np.conj(c4)[:, None] * c4[None, :])
        B = np.prod(d4, axis=1) ** 0.25  # the (m-1)-config rows T_j
        S5_pred = 1.0 + np.sum(B ** (4.0 / 5.0))
        worst7 = max(worst7, abs(5 * g5 - S5_pred))
    report("F7 zero-insertion identity", worst7 < 1e-11, f"worst {worst7:.1e}")

    # F8 graded star beats exact star at R = 0.9
    R = 0.9
    conf = R * np.array([1.0,
                         0.728 * np.exp(1j * 0.4281 * np.pi),
                         0.728 * np.exp(-1j * 0.4281 * np.pi),
                         0.677 * np.exp(1j * 0.8101 * np.pi),
                         0.677 * np.exp(-1j * 0.8101 * np.pi)])
    g_conf, _, _ = G(conf)
    g_star = (1 - R**10) ** 0.2
    ok8 = g_conf - g_star >= 0.055 and 1 - g_conf >= 0.015
    report("F8 1+2+2 graded star beats the 5-star at R=0.9", ok8,
           f"G_conf {g_conf:.6f} G_star {g_star:.6f} diff {g_conf-g_star:.4f}")

    if FAILURES:
        print("FAILURES:", FAILURES)
        return 1
    print("ALL PASS")
    return 0


if __name__ == "__main__":
    sys.exit(main())
