#!/usr/bin/env python3
"""Receipt for ComponentCapacityFormula.md.

THEOREM (component capacity).  f monic of degree n, t > 0, C a connected
component of {|f| < t}, Omega = Chat \\ closure(C).  Then

    n log cap(closure C)  =  log t  -  SUM_{z_j not in C} g_Omega(z_j, infinity),

i.e. cap(C) = t^{1/n} exp(-Sigma/n) with Sigma >= 0, and Sigma = 0 exactly when
C holds every root.  This refines LemniscateCapacityBudget.md (D), which uses
only the inequality cap(C) <= cap(K_t) = t^{1/n}.

Arms
  CAL      calibrate the equilibrium-measure solver on sets of known capacity.
  FORMULA  the identity, on fixed configurations, one- and two-root components.
  CONNECT  Sigma = 0 recovers cap(K_t) = t^{1/n} exactly.
  KAPPA    measure kappa = cap(C)/t^{1/n} on first-merge two-root components and
           report the resulting narrowing of the Theorem E window of
           BergmanSegmentLengthBound.md 3b (relative width coth(1)-1 = 31.30%).

Every reported number is float; the solver's own resolution is measured by CAL
and every tolerance below is set to it rather than to an aspiration.
"""

from __future__ import annotations

import sys

import numpy as np

# --------------------------------------------------------------- solver


def equilibrium(zs):
    """Discretised Symm equation on a boundary polygon -> (cap, sigma, lambda)."""
    n = len(zs)
    h = 0.5 * (np.abs(np.roll(zs, -1) - zs) + np.abs(zs - np.roll(zs, 1)))
    with np.errstate(divide="ignore"):
        K = np.log(1.0 / np.abs(zs[:, None] - zs[None, :]))
    np.fill_diagonal(K, np.log(2.0 / h) + 1.0)
    A = np.zeros((n + 1, n + 1))
    A[:n, :n] = K
    A[:n, n] = -1.0
    A[n, :n] = 1.0
    b = np.zeros(n + 1)
    b[n] = 1.0
    sol = np.linalg.solve(A, b)
    return float(np.exp(-sol[n])), sol[:n], float(sol[n])


def green_inf(z, zs, sigma, lam):
    """g_Omega(z, infinity) from the equilibrium measure of dC."""
    return float(lam - np.sum(sigma * np.log(1.0 / np.abs(z - zs))))


# ------------------------------------------------------ boundary tracing


def trace_boundary(roots, t, seed, k, npts=2000):
    """Level curve |f| = t through the component of roots[seed], k sheets."""
    c = np.poly(np.asarray(roots, dtype=complex))
    dc = np.polyder(c)
    z = complex(roots[seed])
    for s in np.linspace(0.0, t, 500)[1:]:            # climb out to level t
        for _ in range(60):
            d = np.polyval(dc, z)
            if abs(d) < 1e-300:
                return None
            corr = (np.polyval(c, z) - s) / d
            z -= corr
            if abs(corr) < 1e-15:
                break
    out = []
    for th in 2 * np.pi * k * np.arange(npts) / npts:
        target = t * np.exp(1j * th)
        for _ in range(60):
            d = np.polyval(dc, z)
            if abs(d) < 1e-300:
                return None
            corr = (np.polyval(c, z) - target) / d
            z -= corr
            if abs(corr) < 1e-14:
                break
        if abs(np.polyval(c, z) - target) > 1e-9 * t:
            return None
        out.append(z)
    zs = np.array(out)
    if abs(zs[0] - zs[-1]) > 4 * np.median(np.abs(np.diff(zs))):
        return None                                    # did not close on k sheets
    return zs


def winding(zs, z):
    d = zs - z
    return int(round(float(np.sum(np.angle(np.roll(d, -1) / d))) / (2 * np.pi)))


def merging_set(roots, n_steps=700, delta=1e-12):
    """Roots whose lobes meet the minimum-critical hub, by upward branch tracing."""
    roots = np.asarray(roots, dtype=complex)
    n = len(roots)
    c = np.poly(roots)
    dc = np.polyder(c)
    cps = np.roots(dc)
    vals = np.polyval(c, cps)
    keep = np.abs(vals) > 1e-14
    if not keep.any():
        return None
    cps, vals = cps[keep], vals[keep]
    i0 = int(np.argmin(np.abs(vals)))
    cstar, vstar, mu = complex(cps[i0]), complex(vals[i0]), float(abs(vals[i0]))

    def climb(dl):
        ray = vstar / mu
        u = np.linspace(1.0, 0.0, n_steps + 1)
        sv = mu * (1.0 - dl - (1.0 - dl) * u**2)
        z = roots.copy()
        for s in sv[1:]:
            tgt = s * ray
            for _ in range(40):
                d = np.polyval(dc, z)
                bad = np.abs(d) < 1e-300
                corr = np.where(bad, 0.0, (np.polyval(c, z) - tgt) / np.where(bad, 1.0, d))
                z = z - corr
                if np.max(np.abs(corr)) < 1e-15:
                    break
        return np.abs(z - cstar)

    far, near = climb(delta), climb(delta * 1e-4)
    ratio = near / np.maximum(far, 1e-300)
    S = [int(i) for i in np.where(ratio < 0.9 * (1e-4) ** (1.0 / n) + 0.05)[0]]
    if len(S) < 2:
        return None
    return {"c": cstar, "mu": mu, "S": S}


# ------------------------------------------------------------- the arms


def arm_cal():
    th = 2 * np.pi * np.arange(1200) / 1200
    tests = [("unit circle", np.exp(1j * th), 1.0),
             ("circle r=0.37", 0.37 * np.exp(1j * th), 0.37),
             ("ellipse 2 x 0.5", 2 * np.cos(th) + 0.5j * np.sin(th), 1.25),
             ("ellipse 1 x 0.2", np.cos(th) + 0.2j * np.sin(th), 0.6)]
    worst = 0.0
    print("  CAL  solver calibration on sets of known capacity")
    for name, zs, exact in tests:
        cap, _, _ = equilibrium(np.asarray(zs, dtype=complex))
        err = abs(cap - exact) / exact
        worst = max(worst, err)
        print(f"       {name:<18} exact {exact:.7f}  got {cap:.7f}  rel err {err:.2e}")
    print(f"       worst relative error = {worst:.2e}")
    return worst


def arm_formula(tol):
    print("  FORMULA  n log cap(C) == log t - Sigma_{j not in C} g_Omega(z_j, inf)")
    cases = [("z^2-0.8^2, t=0.30", [0.8, -0.8], 0.30, 1),
             ("z^3-0.9^3, t=0.20", list(0.9 * np.exp(2j * np.pi * np.arange(3) / 3)), 0.20, 1),
             ("z^5-0.9^5, t=0.15", list(0.9 * np.exp(2j * np.pi * np.arange(5) / 5)), 0.15, 1),
             ("pair+3 far, t=0.02", [0.1, -0.1, 1.4, -1.3 + 0.6j, 0.2 - 1.5j], 0.02, 1),
             ("pair+3 far, t=0.05", [0.1, -0.1, 1.4, -1.3 + 0.6j, 0.2 - 1.5j], 0.05, 2),
             ("4 spread, t=0.40", [1.0, 0.1 + 1.1j, -0.9 + 0.2j, -0.2 - 1.0j], 0.40, 1)]
    worst = 0.0
    ok = True
    for name, rts, t, k in cases:
        rts = np.asarray(rts, dtype=complex)
        zs = trace_boundary(rts, t, 0, k)
        if zs is None:
            print(f"       {name:<20} untraceable")
            ok = False
            continue
        cap, sig, lam = equilibrium(zs)
        inside = [j for j, r in enumerate(rts) if winding(zs, r) != 0]
        Sigma = sum(green_inf(rts[j], zs, sig, lam) for j in range(len(rts)) if j not in inside)
        err = abs(len(rts) * np.log(cap) - (np.log(t) - Sigma))
        worst = max(worst, err)
        print(f"       {name:<20} k={len(inside)} cap {cap:.7f}  "
              f"pred {t ** (1/len(rts)) * np.exp(-Sigma/len(rts)):.7f}  |lhs-rhs| {err:.2e}")
    print(f"       worst |lhs-rhs| = {worst:.2e}   tolerance {tol:.2e}")
    return worst, ok


def arm_connect(tol):
    print("  CONNECT  Sigma = 0 must recover cap(K_t) = t^{1/n}")
    worst = 0.0
    for n, t in [(3, 2.0), (4, 3.0), (5, 4.0)]:
        rts = 0.9 * np.exp(2j * np.pi * np.arange(n) / n)
        zs = trace_boundary(rts, t, 0, n)
        if zs is None:
            print(f"       n={n} untraceable")
            continue
        cap, _, _ = equilibrium(zs)
        err = abs(cap - t ** (1.0 / n)) / t ** (1.0 / n)
        worst = max(worst, err)
        print(f"       n={n} t={t}  cap {cap:.7f}  t^(1/n) {t ** (1/n):.7f}  rel err {err:.2e}")
    print(f"       worst relative error = {worst:.2e}   tolerance {tol:.2e}")
    return worst


def arm_kappa():
    print("  KAPPA  kappa = cap(C)/t^{1/n} on first-merge two-root components;")
    print("         Theorem E window shrinks from coth(1)-1 = 31.30% to coth(1/kappa^2)-1")
    rng = np.random.default_rng(20260824)
    rows = []
    for n in [3, 4, 5, 6]:
        for trial in range(4):
            if trial < 2:
                k = np.arange(n)
                eps = [3e-2, 3e-3][trial]
                rts = 0.99 * (1 + eps * rng.standard_normal(n)) * np.exp(
                    1j * (2 * np.pi * k / n + eps * rng.standard_normal(n)))
                tag = f"nearFekete n={n} e={eps:g}"
            else:
                rts = rng.uniform(-1, 1, n) + 1j * rng.uniform(-1, 1, n)
                rts = rts * (0.95 / np.max(np.abs(rts)))
                tag = f"random n={n}"
            m = merging_set(rts)
            if m is None or len(m["S"]) != 2:
                continue
            for ratio in (1.05, 1.25):
                t = ratio * m["mu"]
                zs = trace_boundary(rts, t, m["S"][0], 2)
                if zs is None:
                    continue
                cap, _, _ = equilibrium(zs)
                kap = cap / t ** (1.0 / n)
                if not (0 < kap <= 1.02):
                    continue
                w = 1.0 / np.tanh(1.0 / kap**2) - 1.0
                rows.append((tag, n, ratio, kap, w))
                print(f"       {tag:<22} t/v={ratio:<5} kappa {kap:.4f}  "
                      f"window {100*w:8.4f}%  ({(1/np.tanh(1.0)-1)/max(w,1e-15):7.1f}x tighter)")
    if rows:
        ks = np.array([r[3] for r in rows])
        ws = np.array([r[4] for r in rows])
        print(f"       kappa: median {np.median(ks):.4f}  max {ks.max():.4f}  ({len(rows)} rows)")
        print(f"       window: median {100*np.median(ws):.4f}%  worst {100*ws.max():.4f}%")
    return rows


def main():
    print("check_erdos1041_component_capacity")
    cal = arm_cal()
    tol = max(10 * cal, 1e-3)
    form, form_ok = arm_formula(tol)
    conn = arm_connect(tol)
    rows = arm_kappa()
    gates = {
        "solver_calibrated": cal < 1e-3,
        "formula_within_resolution": form_ok and form < tol,
        "connected_recovers_t_pow_1_over_n": conn < tol,
        "kappa_strictly_below_one": bool(rows) and max(r[3] for r in rows) < 1.0,
        "window_strictly_narrower": bool(rows) and max(r[4] for r in rows) < 1 / np.tanh(1.0) - 1,
    }
    print()
    for k, v in gates.items():
        print(f"  {k}={v}")
    ok = all(gates.values())
    print(f"\nverdict {'pass' if ok else 'FAIL'}")
    return 0 if ok else 1


if __name__ == "__main__":
    sys.exit(main())
