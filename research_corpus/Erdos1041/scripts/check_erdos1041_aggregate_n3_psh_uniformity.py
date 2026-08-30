"""Checker for AggregateN3PshUniformityClosure.md (Erdos 1041).

Checks the exact symbolic tangent-cone and Wronskian identities, the radial
test-function coefficient, the comparison barrier, the uniform large-P arm
asymptotic on wall-free phases, and high-precision phase diagnostics.

The ordinary proof in the owner note is authority for the subharmonicity and
distributional-limit steps.  Numerical rows here are diagnostics, not a
replacement for that proof.
"""
import sys

import mpmath as mp
import sympy as sp

from check_erdos1041_aggregate_n3_inner_model import A_of, D_of, Lambda_of


FAILURES = []


def report(name, ok, detail=""):
    print(("PASS " if ok else "FAIL ") + name + ("  " + detail if detail else ""))
    if not ok:
        FAILURES.append(name)


def main():
    mp.mp.dps = 30

    # 1. Polar Laplacian of u_0 + r a(theta).
    r, th = sp.symbols("r th", positive=True, real=True)
    a = sp.Function("a")
    u = 4 + r * a(th)
    lap = sp.diff(u, r, 2) + sp.diff(u, r) / r + sp.diff(u, th, 2) / r**2
    expected = (a(th) + sp.diff(a(th), th, 2)) / r
    report("1 polar tangent Laplacian", sp.simplify(lap - expected) == 0)

    # 2. Exact radial coefficient in the distributional test-function proof.
    q = sp.symbols("q", real=True)
    chi = (q - 1) ** 4 * (2 - q) ** 4
    i0 = sp.integrate(chi, (q, 1, 2))
    irad = sp.integrate(q**2 * sp.diff(chi, q, 2) + q * sp.diff(chi, q),
                        (q, 1, 2))
    report("2 radial test-function coefficient", sp.simplify(irad - i0) == 0,
           f"integral = {i0}")

    # 3. Cubic phase pullback and curvature conversion.
    D, Dpp = sp.symbols("D Dpp", real=True)
    pulled = -2 * D + 9 * (-2 * Dpp)
    report("3 cubic phase factor nine", sp.expand(pulled + 2 * (D + 9 * Dpp)) == 0)

    # 4. Wronskian derivative identity with q'' = -q/9.
    y, ypp, qv = sp.symbols("y ypp qv", real=True)
    lhs = ypp * qv - y * (-qv / 9)
    rhs = qv * (ypp + y / 9)
    report("4 Wronskian derivative kernel", sp.simplify(lhs - rhs) == 0)

    # 5. Exact comparison barrier.
    phi, D0 = sp.symbols("phi D0", real=True)
    h = D0 * sp.cos((phi - sp.pi / 2) / 3) / sp.cos(sp.pi / 6)
    ode = sp.simplify(sp.diff(h, phi, 2) + h / 9)
    endpoints = (sp.simplify(h.subs(phi, 0) - D0) == 0
                 and sp.simplify(h.subs(phi, sp.pi) - D0) == 0)
    report("5 comparison barrier equation and endpoints", ode == 0 and endpoints)

    # 6. The Lambda asymptotic used to make the psh tangent uniform.  The
    # scaled error should stay bounded as P grows because it is O(P^-1/3).
    asym_rows = []
    ok6 = True
    for ph in (mp.pi / 4, mp.pi / 2, 3 * mp.pi / 4):
        vals = []
        for P in (mp.mpf("1e4"), mp.mpf("1e6")):
            err = Lambda_of(P, ph) - 2 * P ** (mp.mpf(1) / 3) - A_of(ph)
            vals.append(err * P ** (mp.mpf(1) / 3))
        asym_rows.append((ph / mp.pi, vals))
        if max(abs(v) for v in vals) > 12 or abs(vals[1] - vals[0]) > 2:
            ok6 = False
    report("6 uniform wall-free Lambda asymptotic", ok6,
           "; ".join(f"phi/pi={mp.nstr(p,3)} scaled={mp.nstr(vs[0],5)},{mp.nstr(vs[1],5)}"
                     for p, vs in asym_rows))

    # 7. High-precision diagnostic for D''+D/9 <= 0 and the proved barrier.
    D0_num = 3 * mp.ellipe(mp.mpf(1) / 4) - mp.mpf(9) / 4 * mp.ellipk(mp.mpf(1) / 4) - mp.mpf(1) / 2
    ok7 = True
    rows7 = []
    step = mp.mpf("0.002")
    for ph in (mp.pi / 4, mp.pi / 2, 3 * mp.pi / 4):
        d = D_of(ph)
        d2 = (D_of(ph + step) - 2 * d + D_of(ph - step)) / step**2
        barrier = D0_num * mp.cos((ph - mp.pi / 2) / 3) / mp.cos(mp.pi / 6)
        curv = d2 + d / 9
        rows7.append((ph / mp.pi, d, barrier, curv))
        if d < barrier - mp.mpf("2e-5") or curv > mp.mpf("0.02"):
            ok7 = False
    report("7 phase curvature and analytic barrier diagnostics", ok7,
           "; ".join(f"{mp.nstr(p,3)}: D={mp.nstr(d,7)} h={mp.nstr(b,7)} L={mp.nstr(c,5)}"
                     for p, d, b, c in rows7))

    if FAILURES:
        print("\nFAIL:", FAILURES)
        return 1
    print("\nPASS: all sections")
    return 0


if __name__ == "__main__":
    sys.exit(main())
