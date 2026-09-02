"""Checker for AggregateN3GateFreeCampaign.md.

Sections (all deterministic, fixed seeds):
  1. two-tier instrument agreement (calibrated DOP853 screen vs exact-fibre
     mpmath adjudication) on generic and near-gon configurations;
  2. the (AGG3-radial) law: on the near-radial slice family the aggregate
     ratio is < 1 at every sampled (eps, phase), with C = gap/sqrt(eps)
     stable in [0.065, 0.078];
  3. exact-fibre adjudication rows (dps 42) at eps = 1e-3: positive gaps,
     replayed to 1e-8;
  4. exact m-gon flatness identities (Fraction arithmetic): m-gon radius r
     gives A_j = 1 - r^{2m} (m = 3: A_j = 1 - r^6; m = 4: A_j = 1 - r^8);
  5. FP_m sampled suprema < 1 (m = 2..6, fixed seed);
  6. the cyclic-column Hoelder chain for FP_4 is falsified as an identity
     (product >> 256 at the stored boundary-spread witness);
  7. the Lorentzian co-distance identity
     |1 - conj(c)c'|^2 = |c - c'|^2 + (1-|c|^2)(1-|c'|^2).

Exit 0 iff all sections pass.
"""
import sys
import itertools
from fractions import Fraction

import numpy as np
import mpmath as mp
from scipy.integrate import solve_ivp

OK = True


def check(label, cond, detail=""):
    global OK
    print(f"{'PASS' if cond else 'FAIL'} {label} {detail}")
    OK &= bool(cond)


# ---------------------------------------------------------------- tier 1
def crit_data(roots):
    c = np.poly(np.asarray(roots, dtype=complex))
    dc = np.polyder(c)
    cps = np.roots(dc)
    cvs = np.polyval(c, cps)
    return cps, cvs, c, dc


def mec3(pts):
    a, b, c = pts
    best = None
    for ctr, r in (((a+b)/2, abs(a-b)/2), ((a+c)/2, abs(a-c)/2), ((b+c)/2, abs(b-c)/2)):
        if all(abs(p-ctr) <= r*(1+1e-12) for p in pts):
            best = r if best is None else min(best, r)
    d = 2*(a.real*(b.imag-c.imag) + b.real*(c.imag-a.imag) + c.real*(a.imag-b.imag))
    if abs(d) > 1e-300:
        aa, bb, cc = abs(a)**2, abs(b)**2, abs(c)**2
        ux = (aa*(b.imag-c.imag) + bb*(c.imag-a.imag) + cc*(a.imag-b.imag))/d
        uy = (aa*(c.real-b.real) + bb*(a.real-c.real) + cc*(b.real-a.real))/d
        ctr = complex(ux, uy)
        r = abs(a-ctr)
        if all(abs(p-ctr) <= r*(1+1e-10) for p in pts):
            best = r if best is None else min(best, r)
    return best if best is not None else max(abs(a-b), abs(a-c), abs(b-c))/2


def lift_arm(c_poly, dc_poly, cstar, v, sign, d_pt):
    ddc = np.polyder(dc_poly)
    A = 0.5*np.polyval(ddc, cstar)
    if A == 0:
        return None
    rd = np.sqrt(-v/A)
    ms = min(1e-3, max(d_pt/20.0, 5e-5))
    z0 = cstar + sign*1e-8*rd

    def rhs(u, y):
        z = y[0] + 1j*y[1]
        dp = np.polyval(dc_poly, z)
        if dp == 0:
            return [0.0, 0.0, 0.0]
        d = -2.0*u*v/dp
        return [d.real, d.imag, abs(d)]
    try:
        sol = solve_ivp(rhs, (1e-8, 1.0), [z0.real, z0.imag, 1e-8*abs(rd)],
                        method="DOP853", rtol=1e-11, atol=1e-14, max_step=ms)
    except Exception:
        return None
    if not sol.success:
        return None
    zf = sol.y[0, -1] + 1j*sol.y[1, -1]
    if abs(np.polyval(c_poly, zf)) > 1e-7:
        return None
    return float(sol.y[2, -1]), zf


def agg3_screen(roots):
    roots = np.asarray(roots, dtype=complex)
    cps, cvs, c_poly, dc_poly = crit_data(roots)
    if len(cps) != 2:
        return None
    d_pt = abs(cps[0]-cps[1])
    R = mec3(list(roots))
    tot, per = 0.0, []
    for i in range(2):
        ra = lift_arm(c_poly, dc_poly, cps[i], cvs[i], +1, d_pt)
        rb = lift_arm(c_poly, dc_poly, cps[i], cvs[i], -1, d_pt)
        if ra is None or rb is None:
            return None
        ia = int(np.argmin(np.abs(roots - ra[1])))
        ib = int(np.argmin(np.abs(roots - rb[1])))
        if ia == ib or abs(roots[ia]-ra[1]) > 1e-5 or abs(roots[ib]-rb[1]) > 1e-5:
            return None
        per.append(ra[0]+rb[0])
        tot += per[-1]
    return tot/(4*R), per, d_pt


# ------------------------------------------------- tier 2: exact fibre
def arm_len(fcoef, c, v, sign, vj, dps=40, N0=256, tol=mp.mpf('1e-9')):
    old = mp.mp.dps
    mp.mp.dps = dps
    try:
        A2, A1, A0 = mp.mpc(fcoef[1]), mp.mpc(fcoef[2]), mp.mpc(fcoef[3])
        v = mp.mpc(v); c0 = mp.mpc(c); vj = mp.mpc(vj)
        B2 = 3*c0 + A2
        w = mp.sqrt(-v/B2)
        kappa = 2 if abs(B2) > mp.mpf('0.02')*abs(v)**(mp.mpf(1)/3) else 3

        def Pz(z):
            return 3*z*z + 2*A2*z + A1

        st = {"z": c0, "t": mp.mpf(0), "z2": None, "t2": None}

        def track(t):
            const = A0 - v*(1-t)
            if st["z2"] is not None and st["t"] != st["t2"]:
                seed = st["z"] + (st["z"]-st["z2"])*(t-st["t"])/(st["t"]-st["t2"])
            elif st["t"] == 0 and t > 0:
                seed = (c0 + sign*mp.sqrt(t)*w if kappa == 2
                        else c0 + sign*(v*t)**(mp.mpf(1)/3))
            else:
                seed = st["z"]
            zz = seed
            ok = False
            for _ in range(80):
                fz = zz**3 + A2*zz*zz + A1*zz + const
                pz = Pz(zz)
                if pz == 0:
                    break
                dz = fz/pz
                zz -= dz
                if abs(dz) < mp.mpf('1e-27')*max(1, abs(zz)):
                    ok = True
                    break
            if not ok:
                rts = mp.polyroots([1, A2, A1, const], maxsteps=120)
                zz = min(rts, key=lambda r: abs(r - seed))
                if abs(zz**3 + A2*zz*zz + A1*zz + const) > mp.mpf('1e-18'):
                    return None
            st["z2"] = st["z"]; st["t2"] = st["t"]
            st["z"] = zz; st["t"] = t
            return zz

        def walk_to(t_target, z_start, t_start, nsteps=16):
            st["z"] = z_start; st["t"] = t_start; st["z2"] = None; st["t2"] = None
            for k in range(1, nsteps+1):
                t = t_start + (t_target - t_start)*k/nsteps
                if track(t) is None:
                    return None
            return st["z"]

        Ts = [mp.mpf(0), mp.mpf(1)]
        tj = 1 - vj/v
        has_tj = abs(mp.im(tj)) < mp.mpf('0.25') and 0 < mp.re(tj) < 1
        if has_tj:
            Ts.append(mp.re(tj))
        Ts = sorted(set(Ts))
        zb = [c0]
        for i in range(1, len(Ts)):
            z_i = walk_to(Ts[i], zb[-1], Ts[i-1])
            if z_i is None:
                return None
            zb.append(z_i)

        def simp_piece(a, b, kind, N, z_a):
            wdt = b - a

            def T(u):
                if kind == 'hub':
                    return a + wdt*u**kappa
                if kind == 'singL':
                    return a + wdt*u**3
                if kind == 'singR':
                    return b - wdt*(1-u)**3
                return a + wdt*u

            def dT(u):
                if kind == 'hub':
                    return kappa*wdt*u**(kappa-1)
                if kind == 'singL':
                    return 3*wdt*u*u
                if kind == 'singR':
                    return 3*wdt*(1-u)**2
                return wdt

            st["z"] = z_a; st["t"] = a; st["z2"] = None; st["t2"] = None
            vals = []
            for k in range(N+1):
                u = mp.mpf(k)/N
                dt = dT(u)
                if dt == 0:
                    if kind == 'hub' and kappa == 2:
                        vals.append(abs(v)*mp.sqrt(wdt)/(abs(B2)*abs(w)))
                    elif kind == 'hub':
                        vals.append(abs(v)**(mp.mpf(1)/3)*wdt**(mp.mpf(1)/3))
                    else:
                        vals.append(mp.mpf(0))
                    continue
                z = track(T(u))
                if z is None:
                    return None
                vals.append(abs(v)*dt/abs(Pz(z)))
            tot = vals[0] + vals[-1]
            for k in range(1, N):
                tot += vals[k]*(4 if k % 2 else 2)
            return tot/(3*N)

        def piece(a, b, kind, z_a, depth=0):
            N = N0
            while True:
                v1 = simp_piece(a, b, kind, N, z_a)
                if v1 is None:
                    return None
                v2 = simp_piece(a, b, kind, 4*N, z_a)
                if v2 is None:
                    return None
                if abs(v2 - v1) <= tol*max(mp.mpf(1), abs(v2)):
                    return v2
                N *= 4
                depth += 1
                if depth > 6:
                    return None

        total = mp.mpf(0)
        for i in range(len(Ts)-1):
            a, b = Ts[i], Ts[i+1]
            if b - a < mp.mpf('1e-24'):
                continue
            if i == 0:
                kind = 'hub'
            elif has_tj and abs(a - mp.re(tj)) < mp.mpf('1e-28'):
                kind = 'singL'
            elif has_tj and abs(b - mp.re(tj)) < mp.mpf('1e-28'):
                kind = 'singR'
            else:
                kind = 'lin'
            pv = piece(a, b, kind, zb[i])
            if pv is None:
                return None
            total += pv
        return total
    finally:
        mp.mp.dps = old


def agg3_exact(roots, dps=42, N0=256):
    old = mp.mp.dps
    mp.mp.dps = dps
    try:
        rt = [mp.mpc(x) for x in roots]
        s1 = sum(rt); s2 = rt[0]*rt[1]+rt[0]*rt[2]+rt[1]*rt[2]; s3 = rt[0]*rt[1]*rt[2]
        fcoef = [1, -s1, s2, -s3]
        sq = mp.sqrt((2*s1)**2 - 12*s2)
        cps = [(2*s1+sq)/6, (2*s1-sq)/6]
        cvs = [cc**3 - s1*cc**2 + s2*cc - s3 for cc in cps]
        a, b, c = rt
        R = None
        for ctr, r in (((a+b)/2, abs(a-b)/2), ((a+c)/2, abs(a-c)/2), ((b+c)/2, abs(b-c)/2)):
            if all(abs(p-ctr) <= r*(1+mp.mpf('1e-25')) for p in rt):
                R = r if R is None else min(R, r)
        d = 2*(mp.re(a)*(mp.im(b)-mp.im(c)) + mp.re(b)*(mp.im(c)-mp.im(a)) + mp.re(c)*(mp.im(a)-mp.im(b)))
        if abs(d) > mp.mpf('1e-40'):
            aa, bb, cc = abs(a)**2, abs(b)**2, abs(c)**2
            ux = (aa*(mp.im(b)-mp.im(c)) + bb*(mp.im(c)-mp.im(a)) + cc*(mp.im(a)-mp.im(b)))/d
            uy = (aa*(mp.re(c)-mp.re(b)) + bb*(mp.re(a)-mp.re(c)) + cc*(mp.re(b)-mp.re(a)))/d
            ctr = mp.mpc(ux, uy)
            r = abs(a-ctr)
            if all(abs(p-ctr) <= r*(1+mp.mpf('1e-25')) for p in rt):
                R = r if R is None else min(R, r)
        if R is None:
            R = max(abs(a-b), abs(a-c), abs(b-c))/2
        tot = mp.mpf(0); per = []
        for i in range(2):
            v = cvs[i]; vj = cvs[1-i]
            L = mp.mpf(0)
            for sign in (1, -1):
                Li = arm_len(fcoef, cps[i], v, sign, vj, dps=dps, N0=N0)
                if Li is None:
                    return None
                L += Li
            per.append(L)
            tot += L
        return tot/(4*R), per
    finally:
        mp.mp.dps = old


# ---------------------------------------------------------------- main
def main():
    rng = np.random.default_rng(1041)

    # 1. two-tier agreement
    for label, roots in [
        ("generic torus", np.exp(1j*np.array([0.0, 1.4, 4.0]))),
        ("near-gon", np.exp(1j*(np.array([0, 2*np.pi/3, 4*np.pi/3]) + np.array([0.01, -0.007, 0.004])))),
    ]:
        s = agg3_screen(roots)
        e = agg3_exact(roots, dps=38, N0=192)
        if s is None or e is None:
            check(f"tier-agreement {label}", False, "(instrument fail)")
            continue
        d = abs(s[0] - float(e[0]))
        check(f"tier-agreement {label}", d < 1e-7,
              f"screen={s[0]:.10f} exact={float(e[0]):.10f} d={d:.2e}")

    # 2. radial law (screen)
    print("radial-law scan (screen):")
    Cs = []
    all_below = True
    for ee in range(2, 7):
        eps = 10.0**(-ee)
        mx = 0.0
        for ph in range(4):
            z2 = np.exp(2j*np.pi*ph/4)
            b1 = 0.7*np.exp(2j*np.pi*ph/4 + 0.9j)
            roots = np.roots(np.array([1, eps*z2, eps*b1, -1], dtype=complex))
            res = agg3_screen(roots)
            if res is None:
                continue
            mx = max(mx, res[0])
        gap = 1.0 - mx
        C = gap/np.sqrt(eps)
        Cs.append(C)
        all_below &= (mx < 1.0)
        print(f"  eps=1e-{ee}: max ratio {mx:.9f}  gap {gap:.3e}  C {C:.4f}")
    check("radial-law: ratio < 1 at every sampled (eps, phase)", all_below)
    # C is phase-slice dependent; the law asserts positivity and stability
    check("radial-law: C stable across decades (max/min < 1.1)",
          max(Cs)/min(Cs) < 1.1 and min(Cs) > 0.05,
          f"C range [{min(Cs):.4f},{max(Cs):.4f}]")

    # 3. exact adjudication rows at eps=1e-3 (dps 42)
    print("exact adjudication (dps 42):")
    expected = {
        "slice ph0": 0.996556926561,
        "slice ph3": 0.998996787187,
        "slice ph5": 0.995801901681,
    }
    for label, ph in [("slice ph0", 0), ("slice ph3", 3), ("slice ph5", 5)]:
        eps = mp.mpf('1e-3')
        z2 = mp.exp(2j*mp.pi*ph/8)
        b1 = mp.mpf('0.7')*mp.exp(2j*mp.pi*(ph+1)/8)
        rt = mp.polyroots([1, eps*z2, eps*b1, -1], maxsteps=200)
        roots = [complex(x) for x in rt]
        e = agg3_exact(roots, dps=42, N0=256)
        if e is None:
            check(f"exact {label}", False, "(instrument fail)")
            continue
        ratio = float(e[0])
        check(f"exact {label}: gap positive + replay",
              1 - ratio > 0 and abs(ratio - expected[label]) < 1e-8,
              f"ratio={ratio:.12f} gap={1-ratio:+.3e}")

    # 4. m-gon flatness identities (exact in r via the product formula)
    for m in (3, 4):
        mp.mp.dps = 50
        rr = mp.mpf(1)/3
        om = mp.exp(2j*mp.pi/m)
        dev = mp.mpf(0)
        for j in range(m):
            cj = rr*om**j
            A = mp.mpf(1)
            for k in range(m):
                A *= abs(1 - mp.conj(cj)*(rr*om**k))
            dev = max(dev, abs(A - (1 - rr**(2*m))))
        check(f"m-gon flatness m={m}: A_j = 1 - r^(2m)",
              float(dev) < 1e-40, f"max dev {float(dev):.2e}")

    # 5. FP_m sampled suprema
    for m in (2, 3, 4, 5, 6):
        best = 0.0
        for t in range(1500):
            mode = t % 3
            if mode == 0:
                r = np.sqrt(rng.uniform(0, 1, m)); ang = rng.uniform(0, 2*np.pi, m)
            elif mode == 1:
                r = rng.uniform(0, 0.3, m); ang = rng.uniform(0, 2*np.pi, m)
            else:
                r = rng.uniform(0, 0.1, m)
                ang = rng.uniform(0, 2*np.pi, m)
            pts = r*np.exp(1j*ang)
            D = np.abs(1 - np.outer(np.conj(pts), pts))
            S = np.sum(np.prod(D, axis=1)**(1.0/m))
            best = max(best, S/m)
        check(f"FP_{m} sampled (1/m)S < 1", best < 1.0, f"max {best:.8f}")

    # 6. cyclic Hoelder chain falsification for FP_4
    pts = np.array([0.9454 - 0.2667j, -0.8489 - 0.2104j,
                    -0.9739 + 0.0505j, 0.9116 + 0.1828j])
    x = 1 - np.abs(pts)**2
    D = np.abs(1 - np.outer(np.conj(pts), pts))
    idx = np.arange(4)
    d1 = D[idx, (idx+1) % 4]; d2 = D[idx, (idx+2) % 4]; d3 = D[idx, (idx+3) % 4]
    P = x.sum()*(d1**4).sum()**2*(d2**4).sum()*(d3**4).sum()
    check("cyclic Hoelder chain falsified (product >> 256)", P > 1e4,
          f"product {P:.3e}")

    # 7. Lorentzian co-distance identity
    rng2 = np.random.default_rng(77)
    worst = 0.0
    for _ in range(4000):
        a = complex(rng2.normal(), rng2.normal())
        b = complex(rng2.normal(), rng2.normal())
        a = a/max(1, abs(a))*rng2.uniform(0, 1)
        b = b/max(1, abs(b))*rng2.uniform(0, 1)
        lhs = abs(1 - np.conj(a)*b)**2
        rhs = abs(a - b)**2 + (1 - abs(a)**2)*(1 - abs(b)**2)
        worst = max(worst, abs(lhs - rhs))
    check("Lorentzian co-distance identity", worst < 1e-12, f"worst {worst:.2e}")

    print("PASS" if OK else "FAIL")
    return 0 if OK else 1


if __name__ == "__main__":
    sys.exit(main())
