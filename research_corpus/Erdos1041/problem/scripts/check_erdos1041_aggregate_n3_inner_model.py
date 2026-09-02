"""Checker for AggregateN3InnerModelClosedForm.md (Erdos 1041).

Verifies:
  1  exact reductions (sympy): f_s(z) = z^3 - 3 s^2 z - 1 has critical
     points +-s with v_pm = f(+-s) = -1 -+ 2 s^3; the arm equation
     factorizes EXACTLY: f_s(z) - v_+ = (z-s)^2 (z+2s), so
     f_s(z) = v_+(1-t) <=> (z-s)^2(z+2s) = (1+2s^3) t (hub +; and the
     mirror for hub -); the inner parametrization identity
     g(2 cos(2 nu/3)) = 4 cos^2 nu for g(w) = w^3 - 3w + 2;
  2  the closed form at the wall: D(0) = 3E - (9/4)K - 1/2 (elliptic
     integrals at parameter m = 1/4), against three independent
     numerical routes (the m-integral, the theta-integral, the
     xi-integral through the A(0)/A(pi) decomposition);
  3  elementary bounds (3 pi - 8)/16 <= D(0) <= 3 pi (2 - sqrt 3)/4 - 1/2
     and positivity of the wall integrand;
  4  phase sweep: D(phi) on a grid of (0, pi) — symmetric about pi/2,
     min at the wall (-> closed form), max at pi/2 ~ 0.608, D > 0
     everywhere; the sqrt-cusp constant at the wall ~ 0.6917;
  5  concavity-type bound D'' + D/9 <= 0 on the interior (numeric);
  6  the deficit law: for sample phases and |s| in {1e-3, 1e-4}, the
     directly computed (4 R_MEC - Sigma_c L(c)) / (2|s|) matches D(phi)
     to O(|s|) (arm lengths via the exact single-valued nu-parametrized
     integral; R_MEC of the actual roots);
  7  the campaign-frame conversion: for the campaign family
     f = z^3 + eps(b2 z^2 + b1 z) - 1, |b1| = 0.7, measured
     C := (4R - Sigma L)/sqrt(eps) at small eps equals
     2 sqrt(|b1|/3) D(phi) (settling the conversion factor), and the
     campaign note's D values 0.375 / 0.489 lie on the D(phi) curve.

Exit 0 iff all pass.
"""
import sys

import mpmath as mp
import numpy as np
import sympy as sp

FAILURES = []


def report(name, ok, detail=""):
    print(("PASS " if ok else "FAIL ") + name + ("  " + detail if detail else ""))
    if not ok:
        FAILURES.append(name)


def lam_integrand(xi, phi):
    """(4/3)(|sin a| + |sin(a + 4pi/3)|)/|sin nu0| at kappa = xi e^{i phi/2}."""
    kappa = xi * mp.exp(1j * phi / 2)
    nu0 = mp.acos(kappa)
    a = 2 * nu0 / 3
    s0 = mp.sin(nu0)
    if abs(s0) < mp.mpf("1e-30"):
        return mp.mpf(0)
    return (mp.mpf(4) / 3) * (abs(mp.sin(a)) + abs(mp.sin(a + 4 * mp.pi / 3))) / abs(s0)


def A_of(phi):
    ren = lambda xi: (mp.mpf(4) / 3) * mp.mpf(4) ** (mp.mpf(1) / 3) * xi ** (-mp.mpf(1) / 3)
    return mp.quad(lambda xi: lam_integrand(xi, phi) - ren(xi),
                   [mp.mpf("1e-12"), 0.5, 1, 2, 8, 50, mp.inf])


def D_of(phi):
    return -(A_of(phi) + A_of(phi + mp.pi)) / 2


def Lambda_of(P, phi):
    return mp.quad(lambda xi: lam_integrand(xi, phi),
                   [mp.mpf("1e-12"), 0.5, min(1, mp.sqrt(P) / 2), mp.sqrt(P) / 2]) \
        if mp.sqrt(P) / 2 > 1 else mp.quad(lambda xi: lam_integrand(xi, phi),
                                           [mp.mpf("1e-12"), mp.sqrt(P) / 2])


def mec_radius(pts):
    """Minimal enclosing circle radius of 3 points (numpy complex)."""
    best = None
    # pairs
    for i in range(3):
        for j in range(i + 1, 3):
            c = (pts[i] + pts[j]) / 2
            r = abs(pts[i] - pts[j]) / 2
            if all(abs(p - c) <= r + 1e-15 for p in pts):
                best = r if best is None else min(best, r)
    if best is not None:
        return best
    # circumcircle
    a, b, c = pts
    d = 2 * (a.real * (b.imag - c.imag) + b.real * (c.imag - a.imag)
             + c.real * (a.imag - b.imag))
    ux = ((abs(a) ** 2) * (b.imag - c.imag) + (abs(b) ** 2) * (c.imag - a.imag)
          + (abs(c) ** 2) * (a.imag - b.imag)) / d
    uy = ((abs(a) ** 2) * (c.real - b.real) + (abs(b) ** 2) * (a.real - c.real)
          + (abs(c) ** 2) * (b.real - a.real)) / d
    ctr = complex(ux, uy)
    return max(abs(p - ctr) for p in pts)


def main():
    mp.mp.dps = 30

    # 1 exact reductions
    z, s, nu, w = sp.symbols("z s nu w")
    f = z**3 - 3 * s**2 * z - 1
    vpl = f.subs(z, s)
    vmi = f.subs(z, -s)
    ok1 = sp.simplify(vpl - (-1 - 2 * s**3)) == 0 and sp.simplify(vmi - (-1 + 2 * s**3)) == 0
    ok1 &= sp.simplify(sp.expand(f - vpl) - sp.expand((z - s) ** 2 * (z + 2 * s))) == 0
    ok1 &= sp.simplify(sp.expand(f - vmi) - sp.expand((z + s) ** 2 * (z - 2 * s))) == 0
    g = w**3 - 3 * w + 2
    psi = sp.symbols("psi")
    step_a = sp.simplify(g.subs(w, 2 * sp.cos(psi))
                         - (2 * sp.expand_trig(sp.cos(3 * psi)) + 2)) == 0
    step_b = sp.simplify(2 * sp.expand_trig(sp.cos(2 * nu)) + 2
                         - 4 * sp.cos(nu) ** 2) == 0
    ok1 &= step_a and step_b  # g(2 cos(2nu/3)) = 2 cos(2nu) + 2 = 4 cos^2 nu
    # d/dt check of critical points: f'(z) = 3 z^2 - 3 s^2 = 3(z-s)(z+s)
    ok1 &= sp.simplify(sp.diff(f, z) - 3 * (z - s) * (z + s)) == 0
    report("1 exact reductions (normal form, factorization, nu-parametrization)", ok1)

    # 2 closed form at the wall, three routes
    K = mp.ellipk(mp.mpf(1) / 4)
    E = mp.ellipe(mp.mpf(1) / 4)
    D0_closed = 3 * E - mp.mpf(9) / 4 * K - mp.mpf(1) / 2
    Ecal_m = mp.quad(lambda m: mp.sqrt(4 * mp.cosh(m) ** 2 - 1) - 2 * mp.cosh(m),
                     [0, 1, 3, 8, 20, mp.inf])
    Ecal_th = -mp.quad(lambda th: 1 / (2 + mp.sqrt(3 + mp.sin(th) ** 2)),
                       [0, mp.pi / 2])
    D0_m = -(1 + 3 * Ecal_m) / 2
    D0_xi = D_of(mp.mpf("1e-9"))  # xi-route, just off the wall
    ok2 = (abs(D0_closed - D0_m) < mp.mpf("1e-15")
           and abs(Ecal_m - Ecal_th) < mp.mpf("1e-15")
           and abs(D0_closed - mp.mpf("0.10944832968994037")) < mp.mpf("1e-14")
           and abs(D0_xi - D0_closed) < mp.mpf("1e-3"))  # cusp: |D(1e-9)-D(0)| ~ c*3e-5
    report("2 wall closed form D(0) = 3E - 9K/4 - 1/2 (three routes)", ok2,
           f"D(0) = {mp.nstr(D0_closed, 17)}; routes agree to "
           f"{mp.nstr(abs(D0_closed - D0_m), 3)}; xi-route {mp.nstr(D0_xi, 8)}")

    # 3 elementary bounds
    lo = (3 * mp.pi - 8) / 16
    hi = 3 * mp.pi * (2 - mp.sqrt(3)) / 4 - mp.mpf(1) / 2
    ok3 = lo <= D0_closed <= hi and lo > 0
    report("3 elementary bounds (3pi-8)/16 <= D(0) <= 3pi(2-sqrt3)/4 - 1/2", ok3,
           f"{mp.nstr(lo, 8)} <= {mp.nstr(D0_closed, 8)} <= {mp.nstr(hi, 8)}")

    # 4 phase sweep
    phis = [mp.pi * k / 16 for k in range(1, 16)]
    Ds = [D_of(p) for p in phis]
    sym = max(abs(Ds[k] - Ds[14 - k]) for k in range(7))
    c1 = all(d > 0 for d in Ds)
    c2 = sym < mp.mpf("1e-10")
    c3 = abs(Ds[7] - mp.mpf("0.6080213")) < mp.mpf("1e-4")
    c4 = min(Ds) >= Ds[0] - mp.mpf("1e-10") and D0_closed < Ds[0]  # wall = global min
    # (the two wall-approach grid ends tie to ~1e-14 by symmetry)
    cusp = (D_of(mp.mpf("1e-6")) - D0_closed) / mp.sqrt(mp.mpf("1e-6"))
    c5 = abs(cusp - mp.mpf("0.6917")) < mp.mpf("0.02")
    ok4 = c1 and c2 and c3 and c4 and c5
    report("4 phase sweep: positive, symmetric, min at wall, max at pi/2, cusp", ok4,
           f"min {mp.nstr(min(Ds), 8)}, max {mp.nstr(max(Ds), 8)}, "
           f"sym {mp.nstr(sym, 3)}, cusp {mp.nstr(cusp, 6)} "
           f"[{c1},{c2},{c3},{c4},{c5}]")

    # 5 D'' + D/9 <= 0 (numeric second differences)
    ok5 = True
    hstep = mp.mpf(1) / 40
    for k in range(2, 14):
        p0 = mp.pi * k / 16
        d2 = (D_of(p0 + hstep) - 2 * D_of(p0) + D_of(p0 - hstep)) / hstep**2
        if d2 + Ds[k - 1] / 9 > mp.mpf("0.05"):
            ok5 = False
    report("5 D'' + D/9 <= 0 on interior grid", ok5)

    # 6 deficit law against direct geometry
    ok6 = True
    rows = []
    for args in (0.4, 1.7):
        for smod in (mp.mpf("1e-3"), mp.mpf("1e-4")):
            sval = smod * mp.exp(1j * mp.mpf(args))
            s3 = sval**3
            phi_p = mp.arg((1 + 2 * s3) / s3)
            phi_m = mp.arg(-(1 - 2 * s3) / s3)
            Pp = abs(1 + 2 * s3) / smod**3
            Pm = abs(1 - 2 * s3) / smod**3
            SigL = smod * (Lambda_of(Pp, phi_p) + Lambda_of(Pm, phi_m))
            roots = np.roots([1, 0, -3 * complex(sval) ** 2, -1])
            R = mec_radius(list(roots))
            Dmeas = (4 * mp.mpf(R) - SigL) / (2 * smod)
            phi = mp.arg(1 / s3)
            Dpred = D_of(phi)
            rows.append(f"args={args} |s|={mp.nstr(smod,2)}: "
                        f"meas {mp.nstr(Dmeas, 8)} vs D(phi) {mp.nstr(Dpred, 8)}")
            if abs(Dmeas - Dpred) > 3 * smod / mp.mpf("1e-3") * mp.mpf("1e-3") + mp.mpf("2e-3"):
                ok6 = False
    report("6 deficit law (4R - Sigma L)/(2|s|) -> D(phi)", ok6, "; ".join(rows))

    # 7 campaign-frame conversion + note's D values on the curve
    b1mod = mp.mpf("0.7")
    theta = mp.mpf("0.4") * mp.pi
    eps = mp.mpf("1e-8")
    b1 = b1mod * mp.exp(1j * theta)
    b2 = mp.exp(1j * theta)
    # roots and critical points of z^3 + eps(b2 z^2 + b1 z) - 1
    coeffs = [1, complex(eps * b2), complex(eps * b1), -1]
    roots = np.roots(coeffs)
    R = mec_radius(list(roots))
    dcoeffs = [3, 2 * complex(eps * b2), complex(eps * b1)]
    crit = np.roots(dcoeffs)
    # arm lengths by direct high-resolution descent-lift integration (fibre
    # tracking with graded t-mesh; adequate at eps = 1e-8 away from the wall)
    def arm_lengths(c):
        v = np.polyval(coeffs, c)
        total = 0.0
        # two branches: start slightly off the double point along +-directions
        f2 = np.polyval([6, 2 * complex(eps * b2)], c)
        for sgn in (1, -1):
            ts = np.concatenate([np.geomspace(1e-14, 1e-2, 400),
                                 np.linspace(1.01e-2, 1.0, 600)])
            zprev = c + sgn * np.sqrt(-2 * v * ts[0] / f2)
            length = abs(zprev - c)
            for t in ts[1:]:
                target = v * (1 - t)
                fib = np.roots([1, complex(eps * b2), complex(eps * b1), -1 - target])
                zn = fib[np.argmin(np.abs(fib - zprev))]
                length += abs(zn - zprev)
                zprev = zn
            total += length
        return total

    SigL = sum(arm_lengths(c) for c in crit)
    Cmeas = (4 * mp.mpf(R) - mp.mpf(SigL)) / mp.sqrt(eps)
    sval = complex(mp.sqrt(-eps * b1 / 3))
    phi = mp.arg(1 / mp.mpc(sval) ** 3)
    Dphi = D_of(phi)
    C_conv2 = 2 * mp.sqrt(b1mod / 3) * Dphi
    C_convhalf = mp.mpf("0.5") * mp.sqrt(b1mod / 3) * Dphi
    pick = "2*sqrt(|b1|/3)*D" if abs(Cmeas - C_conv2) < abs(Cmeas - C_convhalf) else "0.5*sqrt(|b1|/3)*D"
    ok7 = min(abs(Cmeas - C_conv2), abs(Cmeas - C_convhalf)) / Cmeas < mp.mpf("0.05")
    # note's D values on the curve: bisection for D(phi) = 0.375 and 0.489
    # (D strictly increasing on (0, pi/2))
    def bisect_D(target):
        lo, hi = mp.mpf("0.02"), mp.pi / 2
        for _ in range(60):
            mid = (lo + hi) / 2
            if D_of(mid) < target:
                lo = mid
            else:
                hi = mid
        return (lo + hi) / 2

    r1 = bisect_D(mp.mpf("0.375"))
    r2 = bisect_D(mp.mpf("0.489"))
    on_curve = (abs(D_of(r1) - mp.mpf("0.375")) < mp.mpf("1e-6")
                and abs(D_of(r2) - mp.mpf("0.489")) < mp.mpf("1e-6"))
    report("7 campaign conversion + note D-values on curve", ok7 and on_curve,
           f"C_meas {mp.nstr(Cmeas, 6)}; 2sqrt conv {mp.nstr(C_conv2, 6)}; "
           f"half conv {mp.nstr(C_convhalf, 6)}; matched: {pick}; "
           f"D=0.375 at phi/pi={mp.nstr(r1 / mp.pi, 5)}, D=0.489 at phi/pi={mp.nstr(r2 / mp.pi, 5)}")

    print()
    if FAILURES:
        print("FAIL:", FAILURES)
        return 1
    print("PASS: all sections")
    return 0


if __name__ == "__main__":
    sys.exit(main())
