"""Certificate replay for MinimalHubArmBudgetRefutation.md.

Claim A (refutation of the universal row `L(c*) < 2`): there is a monic
degree-4 polynomial with all roots in the CLOSED unit disk (open disk after an
arbitrarily small shrink) whose strict-argmin first-merge hub has two-arm
inverse-ray length strictly greater than 2.

Claim B (refutation of conjecture NF and of every critical-value-slack
envelope): at the same configuration all three critical values tie to within
7.1e-7 relative (slack S = 8.93e-7), so
2*D^{1/(n(n-1))} = 2.00000015 < L(c*); the critical-value moduli vector cannot
separate this configuration from the radial equality family.

Claim C (redirect): the two runner-up hubs of the same configuration have
two-arm lengths 1.9562 and 1.9467 < 2, so the min-over-admissible-hubs
statement survives here.

Witness: the stored `ComponentDepthRefutation.md` degree-4 moduli
(`HubModuliReduction.md` chart, f(rho zeta)/f(c*) = 1 - G(zeta)):

    beta_2 = 0x1.8c5640e53fa34p-9  + 0x1.69a016b3f0c4ap-9  i
    beta_3 = -0x1.6fa15252d066ep-5 - 0x1.3895293ffc3ebp-6  i

Model polynomial ftil(z) = z^4 - beta_3 z^3 - beta_2 z^2 - 1 (monic; hub at 0
with value exactly -1; roots of ftil = the configuration in mu^{1/n}-units).

Method: 50-dps mpmath reconstruction (roots, critical points, values, MEC by
its diameter pair), float64 DOP853 arm integration cross-checked by a 50-dps
Newton-refined inscribed polyline, which is a certified LOWER bound for the
arm length (all vertices lie on the arm to ~1e-40).  The decisive inequality
polyline > 2 * R_MEC is checked with printed margins.

Evidence class: high-precision computation with two independent instruments;
no exact rational certificate is claimed (same class as ClaimLRefutation.md).

Usage: check_erdos1041_minimal_hub_arm_budget_refutation.py [--check]
Exit 0 iff every claim replays.
"""
import argparse
import itertools
import sys

import numpy as np
from scipy.integrate import solve_ivp
from mpmath import mp, mpc, mpf, fabs, polyroots

mp.dps = 50

B2 = mpc(float.fromhex("0x1.8c5640e53fa34p-9"), float.fromhex("0x1.69a016b3f0c4ap-9"))
B3 = mpc(-float.fromhex("0x1.6fa15252d066ep-5"), -float.fromhex("0x1.3895293ffc3ebp-6"))


def mp_poly():
    # ftil = z^4 - B3 z^3 - B2 z^2 - 1
    return [mpf(1), -B3, -B2, mpf(0), mpf(-1)]


def mp_eval(z):
    return (((z - B3) * z - B2) * z) * z - 1


def mp_deval(z):
    return ((4 * z - 3 * B3) * z - 2 * B2) * z


def reconstruct():
    roots = polyroots(mp_poly(), maxsteps=300, extraprec=300)
    cps = polyroots([mpf(4), -3 * B3, -2 * B2], maxsteps=300, extraprec=300)
    cps = [mpf(0)] + list(cps)          # hub exactly at 0
    cvs = [mp_eval(c) for c in cps]
    return roots, cps, cvs


def mec(points):
    """Minimum enclosing circle of <=4 points at mp precision (diameter or
    circumcircle candidates).  Returns (center, radius, margins)."""
    best = None
    pts = points
    for i, j in itertools.combinations(range(len(pts)), 2):
        ctr = (pts[i] + pts[j]) / 2
        rad = fabs(pts[i] - pts[j]) / 2
        if all(fabs(p - ctr) <= rad * (1 + mpf(10) ** (-30)) for p in pts):
            if best is None or rad < best[1]:
                best = (ctr, rad)
    for i, j, k in itertools.combinations(range(len(pts)), 3):
        ax, ay = pts[i].real, pts[i].imag
        bx, by = pts[j].real, pts[j].imag
        cx, cy = pts[k].real, pts[k].imag
        d = 2 * (ax * (by - cy) + bx * (cy - ay) + cx * (ay - by))
        if d == 0:
            continue
        ux = ((ax ** 2 + ay ** 2) * (by - cy) + (bx ** 2 + by ** 2) * (cy - ay)
              + (cx ** 2 + cy ** 2) * (ay - by)) / d
        uy = ((ax ** 2 + ay ** 2) * (cx - bx) + (bx ** 2 + by ** 2) * (ax - cx)
              + (cx ** 2 + cy ** 2) * (bx - ax)) / d
        ctr = mpc(ux, uy)
        rad = fabs(pts[i] - ctr)
        if all(fabs(p - ctr) <= rad * (1 + mpf(10) ** (-30)) for p in pts):
            if best is None or rad < best[1]:
                best = (ctr, rad)
    ctr, rad = best
    margins = sorted(float(rad - fabs(p - ctr)) for p in pts)
    return ctr, rad, margins


def dop853_arm(c_np, dc_np, ddc_np, cstar, v, sign, d_pt, dense=False):
    A = 0.5 * np.polyval(ddc_np, cstar)
    rd = np.sqrt(-v / A)
    ms = min(1e-3, d_pt / 20.0)
    eps = 1e-8
    z0 = cstar + sign * eps * rd

    def rhs(u, y):
        z = y[0] + 1j * y[1]
        dp = np.polyval(dc_np, z)
        d = -2.0 * u * v / dp
        return [d.real, d.imag, abs(d)]

    sol = solve_ivp(rhs, (eps, 1.0), [z0.real, z0.imag, eps * abs(rd)],
                    method="DOP853", rtol=1e-12, atol=1e-14, max_step=ms,
                    dense_output=dense)
    zf = sol.y[0, -1] + 1j * sol.y[1, -1]
    return float(sol.y[2, -1]), zf, sol


def polyline_lower(sol, v_mp, roots, n_nodes=800):
    """Inscribed polyline through 50-dps Newton-refined fiber points along the
    arm (float path used only as Newton seeds).  Lower-bounds the arm length
    between the first refined vertex and the exact terminal root."""
    us = np.linspace(1e-6, 1.0 - 1e-10, n_nodes)
    seeds = sol.sol(us)
    zs = seeds[0] + 1j * seeds[1]
    verts = []
    worst_res = mpf(0)
    for u, z in zip(us, zs):
        target = v_mp * (1 - mpf(float(u)) ** 2)
        w = mpc(z.real, z.imag)
        for _ in range(60):
            f = mp_eval(w) - target
            df = mp_deval(w)
            step = f / df
            w = w - step
            if fabs(step) < mpf(10) ** (-45):
                break
        worst_res = max(worst_res, fabs(mp_eval(w) - target))
        verts.append(w)
    # terminal exact root: nearest reconstruction root to the last float point
    zf = zs[-1]
    root = min(roots, key=lambda r: abs(complex(r) - zf))
    verts.append(root)
    L = mpf(0)
    for a, b in zip(verts[:-1], verts[1:]):
        L += fabs(b - a)
    return L, worst_res, root


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--check", action="store_true")
    ap.parse_args()
    ok = True

    roots, cps, cvs = reconstruct()
    mods = [fabs(w) for w in cvs]
    print("critical value moduli:", [mp.nstr(m, 22) for m in mods])
    # strict argmin at the hub (value exactly 1 in modulus)
    ok &= mods[0] == 1 and all(m > mods[0] for m in mods[1:])
    tie = float(max(m / mods[0] - 1 for m in mods))
    S = float(sum(mp.log(m / mods[0]) for m in mods))
    D = float(mods[0] * mods[1] * mods[2])
    nf_env = 2 * D ** (1.0 / 12.0)
    print(f"tie={tie:.3e}  S={S:.6e}  2*D^(1/12)={nf_env:.12f}")

    ctr, rad, margins = mec(list(roots))
    R = float(rad)
    print(f"MEC radius R = {mp.nstr(rad, 20)}  interior margins: {margins}")
    ok &= margins[0] >= 0

    c_np = np.array([1, complex(-B3), complex(-B2), 0, -1], dtype=complex)
    dc_np = np.polyder(c_np)
    ddc_np = np.polyder(dc_np)
    cps_np = [complex(c) for c in cps]
    L_by_hub = []
    for h in range(3):
        cstar, v = cps_np[h], complex(cvs[h])
        d_pt = min(abs(c - cstar) for c in cps_np if abs(c - cstar) > 1e-13)
        La, za, sa = dop853_arm(c_np, dc_np, ddc_np, cstar, v, +1, d_pt, dense=(h == 0))
        Lb, zb, sb = dop853_arm(c_np, dc_np, ddc_np, cstar, v, -1, d_pt, dense=(h == 0))
        ia = int(np.argmin([abs(complex(r) - za) for r in roots]))
        ib = int(np.argmin([abs(complex(r) - zb) for r in roots]))
        e = max(abs(complex(roots[ia]) - za), abs(complex(roots[ib]) - zb))
        print(f"hub{h}: |w|={mp.nstr(mods[h], 16)} L={La + Lb:.9f} pair=({ia},{ib}) enderr={e:.1e}")
        ok &= e < 1e-9 and ia != ib
        L_by_hub.append((La + Lb, sa, sb))

    # Claim C: runner-up hubs below budget
    ok &= L_by_hub[1][0] < 2.0 and L_by_hub[2][0] < 2.0

    # Claim A/B: certified polyline lower bound at the argmin hub
    L0, sa, sb = L_by_hub[0]
    v_mp = cvs[0]
    Pa, resa, ra = polyline_lower(sa, v_mp, roots)
    Pb, resb, rb = polyline_lower(sb, v_mp, roots)
    P = Pa + Pb
    print(f"argmin hub: DOP853 L = {L0:.9f}; polyline lower = {mp.nstr(P, 18)} "
          f"(worst fiber residual {mp.nstr(max(resa, resb), 3)})")
    ok &= ra != rb
    ok &= float(max(resa, resb)) < 1e-38
    ok &= abs(float(P) - L0) < 5e-4          # cross-instrument agreement

    two_R = 2 * rad
    print(f"2*R_MEC          = {mp.nstr(two_R, 18)}")
    print(f"closed-disk arm length after MEC normalisation >= "
          f"{mp.nstr(P / rad, 18)}  (must be > 2)")
    ok &= P > two_R                           # Claim A
    print(f"margin over 2R_MEC: {mp.nstr(P - two_R, 6)}")
    ok &= float(P) > nf_env                   # Claim B
    print(f"margin over NF envelope: {float(P) - nf_env:.6e}")

    # Lemma 1 spot check on the witness at one interior w
    w = mpc("0.3", "0.1")
    cc = mp_poly()
    cc[-1] = cc[-1] - w
    fiber = polyroots(cc, maxsteps=300, extraprec=300)
    lhs = mpf(1)
    for z in fiber:
        lhs *= fabs(mp_deval(z))
    rhs = mpf(4) ** 4
    for wv in cvs:
        rhs *= fabs(wv - w)
    print(f"lemma1 residual at witness: {float(fabs(lhs / rhs - 1)):.3e}")
    ok &= fabs(lhs / rhs - 1) < mpf(10) ** (-30)

    print("PASS" if ok else "FAIL")
    return 0 if ok else 1


if __name__ == "__main__":
    sys.exit(main())
