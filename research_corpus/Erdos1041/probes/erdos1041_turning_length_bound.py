#!/usr/bin/env python3
"""Erdos 1041, near-Fekete half: the turning bound alone gives the length bound.

NearFeketeCuspLaw.md reduces the near-Fekete half to kappa_n > 0 on the fixed
model g(zeta) = zeta^n + n zeta, and states that a bound on the radius of
curvature R(t) is the entire remaining obstacle.  It is not: an exact identity
for the TRANSVERSE displacement converts the turning bound straight into the
length bound, with no curvature estimate at all.

For a descending branch with asymptotic direction alpha and gamma = arg(zeta_c) - alpha:

  (A)  int sin(tau - alpha) dl = -sin(gamma)          [exact; proved, see the note]
  (B)  1 - cos t = |sin t| * tan(|t|/2)               [exact]
  (C)  |t| <= T with t of constant sign               [the one remaining hypothesis]

  ==>  D = int (1 - cos t) dl <= tan(T/2) * |sin gamma|.

This script measures D, checks (A), checks (C), and compares
  B_n := sum_i tan(T_i/2)|sin gamma_i|   against   C_n := sum_i cos gamma_i.
kappa_n >= C_n - B_n > 0 is the near-Fekete half.

Usage:  ./repo-python formal_math/probes/erdos1041_turning_length_bound.py [--max-n 14]
"""
from __future__ import annotations
import argparse, cmath, math
import numpy as np


def trace_branch(n: int, sign: int, alpha: float, smax: float, npts: int):
    """Track one descending branch by polynomial root continuation in sigma = s^2."""
    zc = cmath.exp(1j * math.pi / (n - 1))
    v = (n - 1) * zc
    gpp = n * (n - 1) * zc ** (n - 2)
    gppp = n * (n - 1) * (n - 2) * zc ** (n - 3)
    a = cmath.sqrt(2.0 / gpp) * sign          # dzeta/ds at the hub
    b = -gppp / (3.0 * gpp ** 2)
    coef = np.zeros(n + 1, dtype=complex); coef[0] = 1.0; coef[n - 1] = n
    ss = np.concatenate(([0.0], np.geomspace(1e-12, smax, npts)))
    zs = np.empty(len(ss), dtype=complex); zs[0] = zc
    for k in range(1, len(ss)):
        s = ss[k]
        if s < 1e-6:
            zs[k] = zc + a * s + b * s * s     # Puiseux series at the simple hub
        else:
            c = coef.copy(); c[n] = -(v + s * s)
            roots = np.roots(c)
            pred = zs[k - 1] + (zs[k - 1] - zs[k - 2]) if k > 1 else zs[0]
            zs[k] = roots[np.argmin(np.abs(roots - pred))]
    gp = n * (zs ** (n - 1) + 1.0)
    dlds = np.empty(len(ss)); dlds[0] = abs(a)
    dlds[1:] = 2 * ss[1:] / np.abs(gp[1:])
    tau = np.empty(len(ss)); tau[0] = cmath.phase(a)
    tau[1:] = np.angle(1.0 / gp[1:])
    t = np.unwrap(tau) - alpha
    trap = np.trapezoid if hasattr(np, "trapezoid") else np.trapz
    Lam = trap(dlds, ss)
    chord = cmath.exp(-1j * alpha) * (zs[-1] - zc)
    # D and the transverse integral, both via the exact chord relations
    return dict(D=Lam - chord.real, Isin=chord.imag, t=t, zs=zs,
                tsup=float(np.max(np.abs(t))))


def main() -> int:
    ap = argparse.ArgumentParser()
    ap.add_argument("--max-n", type=int, default=14)
    args = ap.parse_args()

    print(f"{'n':>3} {'br':>2} {'D':>13} {'tan(T/2)|sin g|':>16} {'(A) resid':>11} "
          f"{'sup|t|-T':>10} {'sector':>7}")
    rows = {}
    for n in range(3, args.max_n + 1):
        T = [(n - 2) * math.pi / (2 * (n - 1)), (n - 2) ** 2 * math.pi / (2 * n * (n - 1))]
        gam = [math.pi / (n - 1), math.pi / (n - 1) - 2 * math.pi / n]
        Ds = []
        for i, (sign, alpha) in enumerate(((+1, 0.0), (-1, 2 * math.pi / n))):
            r = trace_branch(n, sign, alpha, 10 ** (0.5 * n + 2), 20000)
            bnd = math.tan(T[i] / 2) * abs(math.sin(gam[i]))
            resid = abs(r["Isin"] - (-math.sin(gam[i])))
            ang = np.angle(r["zs"][1:])
            insec = bool(np.all(ang >= -1e-9) and np.all(ang <= math.pi / (n - 1) + 1e-9))
            Ds.append(r["D"])
            assert r["D"] <= bnd, f"length bound violated at n={n} branch {i+1}"
            print(f"{n:>3} {i+1:>2} {r['D']:>13.9f} {bnd:>16.9f} {resid:>11.2e} "
                  f"{r['tsup']-T[i]:>10.2e} {str(insec) if i==0 else '-':>7}")
        B = sum(math.tan(T[i] / 2) * abs(math.sin(gam[i])) for i in (0, 1))
        C = sum(math.cos(g) for g in gam)
        rows[n] = (sum(Ds), B, C)

    print(f"\n{'n':>3} {'kappa_n(meas)':>14} {'B_n':>12} {'C_n':>12} {'C_n-B_n>0':>10}")
    ok = True
    for n, (d, B, C) in rows.items():
        kap = C - d
        ok &= (C - B) > 0
        print(f"{n:>3} {kap:>14.9f} {B:>12.8f} {C:>12.8f} {C-B:>10.6f}")
    print("\nall branches satisfy D <= tan(T/2)|sin gamma|, and C_n - B_n > 0:", ok)
    return 0 if ok else 1


if __name__ == "__main__":
    raise SystemExit(main())
