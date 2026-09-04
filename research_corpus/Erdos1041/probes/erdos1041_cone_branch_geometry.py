#!/usr/bin/env python3
"""Erdos 1041: checks for ConeBoundBranchGeometry.md.

Lemma S  branch 1 stays in the open sector 0 < arg zeta < pi/(n-1)
Lemma B  dy/dsigma = -Im(g')/|g'|^2 < 0, hence Im zeta < Im zeta_c, Im G > 0
(star)   Phi = c_n r^{n-2} - (n-2) r^{n-1} sin(phi) - sin((n-2)phi) >= 0
n=3      3 r y (2r - sin(phi)(r^2+1)) = -4 (y-1)^3 (y+1)   [symbolic, exact]
plus the three refutations of section 6.

Usage: ./repo-python formal_math/probes/erdos1041_cone_branch_geometry.py
"""
from __future__ import annotations
import cmath, math
import numpy as np


def branch_one(n: int, smax: float, npts: int) -> np.ndarray:
    zc = cmath.exp(1j * math.pi / (n - 1)); v = (n - 1) * zc
    gpp = n * (n - 1) * zc ** (n - 2); gppp = n * (n - 1) * (n - 2) * zc ** (n - 3)
    a = cmath.sqrt(2 / gpp); b = -gppp / (3 * gpp ** 2)
    coef = np.zeros(n + 1, dtype=complex); coef[0] = 1; coef[n - 1] = n
    ss = np.concatenate(([0.0], np.geomspace(1e-10, smax, npts)))
    zs = np.empty(len(ss), dtype=complex); zs[0] = zc
    for k in range(1, len(ss)):
        s = ss[k]
        if s < 1e-6:
            zs[k] = zc + a * s + b * s * s
        else:
            c = coef.copy(); c[n] = -(v + s * s); rt = np.roots(c)
            pred = zs[k - 1] + (zs[k - 1] - zs[k - 2]) if k > 1 else zs[0]
            zs[k] = rt[np.argmin(np.abs(rt - pred))]
    return zs[1:]


def main() -> int:
    ok = True
    print("Lemma S: the ray arg zeta = phi_c meets Im g = c_n only at r = 1")
    for n in (3, 5, 8, 12, 20):
        rr = np.geomspace(1e-3, 5.0, 400000)
        # Im g on that ray is sin(phi_c)(n r - r^n); max of n r - r^n is n-1 at r=1
        peak = float(np.max(n * rr - rr ** n))
        ok &= peak <= (n - 1) + 1e-8
        print(f"   n={n:>3}  max(n r - r^n) = {peak:.10f}   n-1 = {n-1}")

    print("\nLemma B / (star) / refutations, on branch 1")
    print(f"{'n':>3} {'min Phi':>11} {'min Im g\'':>12} {'max y':>12} {'sin(phi_c)':>11} "
          f"{'min ReG':>10} {'min r':>8} {'frac r<1':>9} {'max (c)-viol':>13} {'resolved':>9}")
    for n in range(3, 13):
        pc = math.pi / (n - 1); spc = math.sin(pc); cn = (n - 1) * spc
        # Keep |zeta|^n inside float64 fidelity: past ~1e12 the level-set residual
        # swamps the quantities being tested (at n=12, r~1e3 gives |z|^n ~ 1e36 and
        # Im(z^n + n z) - c_n reaches 30 -- those points are not on the curve at all).
        smax = min(10 ** (0.5 * n + 2), 1e6)
        z = branch_one(n, smax, 20000)
        r = np.abs(z); phi = np.angle(z); y = z.imag
        gp = n * (z ** (n - 1) + 1.0)
        # Lemma B's sign comes from Im g' = n r^{n-1} sin((n-1)phi), which is well
        # conditioned.  Testing Im(1/g') instead underflows: |g'|^2 reaches 1e56 at
        # n=12, so the sign of a 1e-28 quotient is float64 noise, not mathematics.
        img = n * r ** (n - 1) * np.sin((n - 1) * phi)
        Phi = cn * r ** (n - 2) - (n - 2) * r ** (n - 1) * np.sin(phi) - np.sin((n - 2) * phi)
        cviol = float(np.max(np.sin((n - 2) * phi) - r ** (n - 2) * spc))
        resid = np.abs(np.imag(z ** n + n * z) - cn)
        on = resid < 1e-6                      # points the tracer actually resolved
        assert on.sum() > 0.5 * len(z), f"tracer resolved too little of the branch at n={n}" 
        ok &= bool(np.all(phi[on] > 0) and np.all(phi[on] < pc + 1e-12))   # Lemma S
        ok &= bool(np.all(img[on] > 0))                             # Lemma B
        ok &= bool(y[on].max() <= spc + 1e-9)
        ok &= bool(Phi[on].min() > -1e-9)                           # (star)
        print(f"{n:>3} {Phi[on].min():>11.2e} {img[on].min():>12.2e} {y[on].max():>12.9f} {spc:>11.8f} "
              f"{np.real(z[on]**n+z[on]).min():>10.3e} {r[on].min():>8.5f} {float((r[on]<1).mean()):>9.4f} "
              f"{cviol:>13.3e} {on.mean():>9.4f}")

    print("\nRefuted (section 6): (c) violated above, Re G < 0, and r >= 1 is a minority.")
    try:
        import sympy as sp
        xx, yy = sp.symbols('x y', positive=True)
        rr_ = sp.sqrt(xx ** 2 + yy ** 2)
        star = 2 * rr_ - (yy / rr_) * (rr_ ** 2 + 1)
        expr = sp.expand(sp.simplify(3 * rr_ * yy * star).subs(
            xx ** 2, sp.Rational(1, 3) * (2 / yy + yy ** 2 - 3)))
        diff = sp.simplify(sp.expand(expr - (-4 * (yy - 1) ** 3 * (yy + 1))))
        ok &= (diff == 0)
        print(f"n=3 symbolic identity  3 r y star + 4(y-1)^3(y+1) = {diff}   (must be 0)")
    except ImportError:
        print("n=3 symbolic identity: sympy unavailable, skipped")

    print("\nall checks pass:", ok)
    return 0 if ok else 1


if __name__ == "__main__":
    raise SystemExit(main())
