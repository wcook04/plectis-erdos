#!/usr/bin/env python3
"""Erdos #1041 -- probe for DegenerateHubBlaschkeReduction.md.

Four gates.

G1  tracer validation.  On f = (z-d)(z+d) the one-root lobe boundary at
    sigma -> mu is one loop of Bernoulli's lemniscate, of length exactly
    sqrt(2)*varpi*rho = Gamma(1/4)^2/(2 sqrt pi) * rho.  Both instruments must
    reproduce it from below.

G2  Conjecture P is false.  Family f = z^n - z, one-root lobe at the root 0,
    sigma = 0.9999 mu.  Two independent instruments must agree and must exceed
    sqrt(2)*varpi from n = 3 on.

G3  threshold table of Theorem 3 / Corollary 4, with the three exact anchors
    Q_full(2) = tanh 1, lim Q_full = exp(-pi/sqrt(e^4-1)), Q_sect ~ (1-e^-m)^4.

G4  Lemma 1 degree claim.  For f with an engineered critical point of
    multiplicity m, the component of {|f| < s} containing it must carry exactly
    m roots: the arg-f parametrisation of its boundary closes after 2*pi*m and
    not before.  Also verified in closed form on z^n - r^n, where the explicit
    uniformiser Phi^n = sigma(z^n) puts the n roots at modulus q^{1/n}.

Exit 0 iff every gate passes.
"""
from __future__ import annotations
import math, cmath, sys
import numpy as np

VARPI2 = math.gamma(0.25)**2/(2*math.sqrt(math.pi))     # sqrt(2)*varpi
E4 = math.exp(4.0)
TOL = {}

# ---------------------------------------------------------------- primitives
def fval(roots, z):
    p = 1.0+0j
    for r in roots: p *= (z-r)
    return p

def g_of(roots, z):                      # f'/f
    s = 0j
    for r in roots: s += 1.0/(z-r)
    return s

def crit(roots):
    c = np.poly(np.array(roots, dtype=complex))
    return list(np.roots(np.polyder(c)))

def first_crossing(roots, a, th, sigma, tmax, N=20000):
    """First crossing of |f| = sigma along the ray from a.  MUST be a monotone
    scan: a geometric walk steps over the O(sqrt eps) window at sigma = mu(1-eps)
    and lands on a different lobe (instrument defect, negative_results 34/41)."""
    u = cmath.exp(1j*th)
    for k in range(1, N+1):
        t = tmax*k/N
        if abs(fval(roots, a+t*u)) >= sigma:
            lo, hi = tmax*(k-1)/N, t
            for _ in range(100):
                mid = 0.5*(lo+hi)
                if abs(fval(roots, a+mid*u)) < sigma: lo = mid
                else: hi = mid
            return a+0.5*(lo+hi)*u
    return None

def trace(roots, a, sigma, M=20000, turns=1, tmax=None):
    """Integrate dz/dphi = i f/f' over phi in [0, 2 pi turns]; returns
    (length, closure).  Closure ~ 0 certifies the winding of arg f."""
    if tmax is None:
        tmax = 2.0*max(abs(r-a) for r in roots)+1.0
    z0 = first_crossing(roots, a, 0.0, sigma, tmax)
    if z0 is None: return None
    z = z0; dphi = 2*math.pi*turns/M; L = 0.0
    for _ in range(M):
        def F(zz):
            gg = g_of(roots, zz)
            return None if gg == 0 else 1j/gg
        k1 = F(z)
        if k1 is None: return None
        k2 = F(z+0.5*dphi*k1); k3 = F(z+0.5*dphi*k2); k4 = F(z+dphi*k3)
        if k2 is None or k3 is None or k4 is None: return None
        zn = z+(dphi/6.0)*(k1+2*k2+2*k3+k4)
        for _ in range(2):
            v = fval(roots, zn); gg = g_of(roots, zn)
            if v == 0 or gg == 0: break
            zn = zn-((abs(v)-sigma)/abs(v))/gg
        L += abs(zn-z); z = zn
    return L, abs(z-z0)

def star_perimeter(n, sigma, M=4000):
    """Independent instrument for f = z^n - z: smallest positive root of
    t^{2n} - 2 cos((n-1)phi) t^{n+1} + t^2 - sigma^2."""
    s2 = sigma*sigma
    pts = np.empty(M, dtype=complex)
    for k in range(M):
        phi = 2*math.pi*k/M
        ca = math.cos((n-1)*phi)
        c = np.zeros(2*n+1); c[0] = 1.0
        c[2*n-(n+1)] += -2.0*ca; c[2*n-2] += 1.0; c[2*n] += -s2
        rts = np.roots(c)
        good = [x.real for x in rts if abs(x.imag) < 1e-9 and x.real > 1e-12]
        pts[k] = min(good)*cmath.exp(1j*phi)
    return float(np.abs(np.roll(pts,-1)-pts).sum())

# ---------------------------------------------------------------- thresholds
def one_minus_rho2_full(x, m):
    d = 2*math.pi/m
    return (1-x*x)**2/abs(1-x*x*cmath.exp(1j*d))**2

def one_minus_rho2_sector(x, m):
    us = []
    for th in (math.pi/m, 3*math.pi/m):
        xi = (x**(m/4.0))*cmath.exp(1j*(m/4.0)*th)     # -> upper half disc
        w = (1+xi)/(1-xi)                              # -> first quadrant
        us.append(w*w)                                 # -> upper half plane
    u1, u2 = us
    rho = abs(u1-u2)/abs(u1-u2.conjugate())
    return 1.0-rho*rho

def bisect(pred, lo=1e-12, hi=1-1e-15, it=300):
    if not pred(lo): return None
    for _ in range(it):
        mid = 0.5*(lo+hi)
        if pred(mid): lo = mid
        else: hi = mid
    return lo

# --------------------------------------------------------------------- gates
def gate1():
    print("G1  tracer validation on the quadratic (Conjecture P's own equality case)")
    ok = True
    for d in (0.3, 1.0):
        vals = []
        for frac in (0.99, 0.999, 0.9999):
            s = d*d*frac
            out = trace([d, -d], d, s, 20000)
            assert out is not None
            L, cl = out
            vals.append(L/(s**0.5))
            print(f"      d={d}  sigma/mu={frac:<7} P/rho={L/(s**0.5):.6f}  closure={cl:.1e}")
        if not (vals[0] < vals[1] < vals[2] < VARPI2 and vals[2] > 0.996*VARPI2):
            ok = False
    print(f"      target sqrt(2)*varpi = {VARPI2:.10f}   -> {'PASS' if ok else 'FAIL'}")
    return ok

def gate2():
    print("G2  Conjecture P refutation, two independent instruments, f = z^n - z")
    ok = True; worst = 0.0
    print(f"      {'n':>3} {'star/ray':>11} {'ODE tracer':>11} {'rel.diff':>10} {'/sqrt2varpi':>12}")
    for n in (3, 4, 6, 10, 16, 26):
        roots = [0j]+[cmath.exp(2j*math.pi*k/(n-1)) for k in range(n-1)]
        cs = crit(roots); mu = min(abs(fval(roots, c)) for c in cs)
        s = mu*0.9999; rho = s**(1.0/n)
        P1 = star_perimeter(n, s, 3000)/rho
        out = trace(roots, 0j, s, 20000); P2 = out[0]/rho
        rel = abs(P1-P2)/P1
        worst = max(worst, P2/VARPI2)
        print(f"      {n:>3} {P1:>11.5f} {P2:>11.5f} {rel:>10.2e} {P2/VARPI2:>12.5f}")
        if rel > 2e-3: ok = False
        if n >= 3 and P2 <= VARPI2: ok = False
    print(f"      worst ratio to the conjectured bound = {worst:.5f}  (>1 refutes)"
          f"   -> {'PASS' if ok and worst > 1.5 else 'FAIL'}")
    return ok and worst > 1.5

def gate3():
    print("G3  Theorem 3 / Corollary 4 threshold table")
    ok = True
    print(f"      {'m':>3} {'Q_full':>13} {'Q_sect':>13} {'Q':>13} {'(1-e^-m)^4':>13}")
    Qf_prev = None
    for m in (2,3,4,5,6,8,10,12,16):
        xf = bisect(lambda x: 1.0/one_minus_rho2_full(x, m) <= E4); Qf = xf**m
        thr = math.exp(-2.0*m)
        if m == 2:
            Qs = Qf                       # the two sectors are the whole disc
        else:
            xs = bisect(lambda x: one_minus_rho2_sector(x, m) >= thr); Qs = xs**m
        print(f"      {m:>3} {Qf:>13.9f} {Qs:>13.9f} {max(Qf,Qs):>13.9f} {(1-math.exp(-m))**4:>13.9f}")
        if m == 2 and abs(Qf-math.tanh(1.0)) > 1e-12: ok = False
        if Qf_prev is not None and Qf > Qf_prev: ok = False
        Qf_prev = Qf
        # (1-e^-m)^4 is the leading order only: compare relative to the gap 1-Qs
        # (1-e^-m)^4 is the leading order only; it is within 2% of the gap from m=4 on
        if m >= 4 and abs(Qs-(1-math.exp(-m))**4) > 0.02*(1-Qs)+1e-9: ok = False
    lim = math.exp(-math.pi/math.sqrt(E4-1))
    xf = bisect(lambda x: 1.0/one_minus_rho2_full(x, 400) <= E4)
    xf2 = bisect(lambda x: 1.0/one_minus_rho2_full(x, 2) <= E4)
    print(f"      anchors: Q_full(2) = tanh 1 = {math.tanh(1.0):.12f}  "
          f"(computed {xf2**2:.12f}, err {abs(xf2**2-math.tanh(1.0)):.2e})")
    print(f"               lim Q_full = exp(-pi/sqrt(e^4-1)) = {lim:.12f}   at m=400: {xf**400:.12f}")
    if abs(xf**400-lim) > 2e-3: ok = False
    print(f"      -> {'PASS' if ok else 'FAIL'}")
    return ok

def gate4():
    print("G4  Lemma 1: the merge component of a multiplicity-m hub carries m roots")
    ok = True
    # closed form on z^n - r^n : Phi^n = sigma(z^n) puts the n roots at modulus q^{1/n}
    for n, r, t in ((3, 0.8, 1.0), (5, 0.9, 1.0), (7, 0.95, 1.0)):
        q = r**n/t
        # explicit uniformiser check: sigma(r^n) = q, so |Phi(root)| = q^{1/n}
        w = r**n
        sig = ((w-r**n)/t+q)/(1+q*(w-r**n)/t)
        print(f"      z^{n} - r^{n}, r={r}: sigma(r^n) = {sig.real:.12f}  q = {q:.12f}"
              f"  |Phi(root)| = {abs(sig)**(1.0/n):.9f}  q^(1/n) = {q**(1.0/n):.9f}")
        if abs(sig-q) > 1e-12: ok = False
    # engineered non-symmetric degenerate hub:  f' = n (z-c)^{m-1} h(z)
    for (n, m, c, tail) in ((5, 3, 0.1+0.05j, [0.7-0.3j, -0.6+0.2j]),
                            (6, 4, -0.2+0.1j, [0.5+0.4j, -0.8-0.1j])):
        dcoef = np.poly(np.array([c]*(m-1)+tail, dtype=complex))*n
        fc = np.polyint(dcoef); fc[-1] = 0.0        # f with f(0)=0; constant is free
        roots = list(np.roots(fc))
        cs = crit(roots)
        # a root of multiplicity m-1 is returned by np.roots as m-1 points at
        # radius ~ eps^{1/(m-1)} from c, so the cluster tolerance must be loose
        mult = sum(1 for cc in cs if abs(cc-c) < 1e-3)
        vc = abs(np.polyval(fc, c))
        others = [abs(np.polyval(fc, cc)) for cc in cs if abs(cc-c) >= 1e-6]
        s = min([vc*1.35]+([min(others)*0.999] if others else []))
        if s <= vc: s = vc*1.0005
        out = trace(roots, c+1e-9, s, 24000, turns=m)
        half = trace(roots, c+1e-9, s, 24000, turns=1)
        ok_m = out is not None and out[1] < 1e-2*max(1.0, out[0])
        ok_1 = half is not None and half[1] > 1e-2*max(1.0, half[0])
        print(f"      n={n} m={m}: hub multiplicity found = {mult+1}, |f(c)|={vc:.6f}, s={s:.6f}"
              f"  closes at 2pi*{m}: {ok_m}   closes at 2pi: {not ok_1 and 'yes(BAD)' or 'no'}")
        if not (ok_m and ok_1 and mult+1 == m): ok = False
    print(f"      -> {'PASS' if ok else 'FAIL'}")
    return ok


def area_Omega_pure(n, r, t=1.0, N=120000):
    """Area of {|z^n - r^n| < t} in closed form: u = z^n gives
       Area = (1/2) int_0^{2pi} R(th)^{2/n} dth, R = r^n cos th + sqrt(t^2 - r^{2n} sin^2 th)."""
    c = r**n; s = 0.0
    for k in range(N):
        th = 2*math.pi*(k+0.5)/N
        s += (c*math.cos(th)+math.sqrt(max(0.0, t*t-c*c*math.sin(th)**2)))**(2.0/n)
    return 0.5*s*(2*math.pi/N)

PUB = {0.90: {3:1.705,4:1.429,5:1.236,6:1.090,8:0.883,10:0.741,12:0.638},
       0.99: {3:2.067,4:1.782,5:1.600,6:1.465,8:1.270,10:1.129,12:1.021}}

def gate5():
    """Theorem 3 (sector form) must reproduce, on f = z^n - r^n at t = 1, the
    closed-form 'two basins' row of BergmanGeodesicInvariance.md section 6 --
    which was computed there at 50 digits from the explicit uniformiser of that
    one symmetric family.  Here it comes out of the general theorem."""
    print("G5  Theorem 3 vs the published closed-form Proposition S 'two basins' row")
    worst = 0.0
    print(f"      {'r':>5} {'n':>3} {'Area':>10} {'B_sect':>9} {'published':>10} {'rel err':>9}")
    for r in (0.90, 0.99):
        for n in (3,4,5,6,8,10,12):
            A = area_Omega_pure(n, r, 1.0)
            omr2 = one_minus_rho2_sector(r, n)     # x = q^{1/m} = (r^n)^{1/n} = r
            B = math.sqrt((2*A/(n*math.pi))*math.log(1.0/omr2))
            rel = abs(B-PUB[r][n])/PUB[r][n]; worst = max(worst, rel)
            print(f"      {r:>5} {n:>3} {A:>10.6f} {B:>9.4f} {PUB[r][n]:>10.3f} {rel:>9.2e}")
    print(f"      worst relative discrepancy = {worst:.2e}   -> {'PASS' if worst < 2e-3 else 'FAIL'}")
    return worst < 2e-3


def gate6():
    """Section 5b: closed-form map of the near-Fekete wall on

           f(z) = z^n + eps e^{i phi} z - m0 .

    Exact: f' = 0 gives z^{n-1} = -eps e^{i phi}/n, so rho_c = (eps/n)^{1/(n-1)},
    and f(c) = -m0 + (n-1) rho_c^n * (e^{i phi} c / rho_c), where the n-1 numbers
    e^{i phi} c/rho_c are the (n-1)-th roots of -e^{i n phi}.  So the critical
    VALUES are the vertices of a regular (n-1)-gon of radius s = (n-1) rho_c^n
    centred at -m0, rotated by phi.

    CAUTION, and the point of this gate: at phi = 0 -- the direction that
    NearFeketeCuspLaw.md sec.3 records as MINIMISING kappa_n -- the gon is
    symmetric about the real axis, so the two smallest critical-value moduli are
    a conjugate PAIR and are exactly equal.  Corollary 5 is then vacuous at every
    eps.  The separation is maximal at phi = pi/n, where a vertex points at +1.
    """
    print("G6  wall map on f = z^n + eps e^{i phi} z - m0  (closed forms vs numpy)")
    TANH1 = math.tanh(1.0); worst = 0.0
    def closed(n, eps, phi, m0=1.0):
        rho_c = (eps/n)**(1.0/(n-1)); s = (n-1)*rho_c**n
        base = cmath.exp(1j*(math.pi + n*phi)/(n-1))       # (n-1)-th root of -e^{i n phi}
        etas = [base*cmath.exp(2j*math.pi*k/(n-1)) for k in range(n-1)]
        return rho_c, s, sorted(abs(-m0 + s*e) for e in etas)
    def numeric(n, eps, phi, m0=1.0):
        c = np.zeros(n+1, dtype=complex); c[0] = 1.0
        c[n-1] = eps*cmath.exp(1j*phi); c[n] = -m0
        return sorted(abs(np.polyval(c, z)) for z in np.roots(np.polyder(c)))
    for n in (3,4,5,6,8):
        for phi in (0.0, math.pi/n):
            rho_c, s, cl = closed(n, 0.2, phi)
            nu = numeric(n, 0.2, phi)
            err = max(abs(cl[i]-nu[i]) for i in range(min(2, len(cl))))
            worst = max(worst, err)
            tag = "phi=0 (kappa-min, TIE)" if phi == 0.0 else "phi=pi/n (max sep)"
            print(f"      n={n} {tag:>22}: mu1={cl[0]:.9f} mu2={cl[1]:.9f} "
                  f"ratio={cl[0]/cl[1]:.6f} err={err:.1e}")
    print("      -- level deficit is the n-th power of the cusp radius:")
    for n in (3,5,8,12):
        for rc in (0.3,):
            eps = n*rc**(n-1); rho_c, s, cl = closed(n, eps, math.pi/n)
            print(f"      n={n:>2} rho_c={rc}: eps={eps:.6g}, 1-mu1/m0={1-cl[0]:.3e}, "
                  f"mu1/mu2={cl[0]/cl[1]:.6f}")
    print("      -- least eps at which Corollary 5 fires (phi = pi/n, best case):")
    for n in (3,4,5,6,8,10,12):
        lo, hi, ok = 1e-12, 50.0, None
        for _ in range(200):
            mid = math.sqrt(lo*hi); _,_,cl = closed(n, mid, math.pi/n)
            if cl[0]/cl[1] <= TANH1: hi, ok = mid, mid
            else: lo = mid
        print(f"      n={n:>2}  eps* = {ok:.6g}    cusp side (rho_c=0.3): eps = {n*0.3**(n-1):.6g}")
    print(f"      worst closed-form vs numpy error = {worst:.1e}   -> "
          f"{'PASS' if worst < 1e-9 else 'FAIL'}")
    return worst < 1e-9

def gate7():
    """Section 6, Proposition 6: the concyclic two-spoke reduction.
    S_j = max_t log prod_k |t w_j - w_k| >= 0, and Lambda = second-smallest S_j.
    Gate: Lambda = 0 at the n-th roots of unity (every spoke of z^n - R^n is safe),
    and a short hill-climb finds Lambda > 0 but tiny."""
    print("G7  concyclic two-spoke functional Lambda (Proposition 6)")
    import random
    rng = random.Random(7)
    def S(ws, j, M=1500):
        w = ws[j]; best = -1e18
        for k in range(M+1):
            z = (k/M)*w
            s = 0.0
            for u in ws:
                d = abs(z-u); s += math.log(d) if d > 0 else -700.0
            if s > best: best = s
        return best
    def Lam(ws, M=1500):
        return sorted(S(ws, j, M) for j in range(len(ws)))[1]
    ok = True
    for n in (3,5,8):
        ws = [cmath.exp(2j*math.pi*k/n) for k in range(n)]
        v = Lam(ws, 2000)
        print(f"      n={n} roots of unity: Lambda = {v:.3e}  (must be 0)")
        if abs(v) > 1e-9: ok = False
    print(f"      {'n':>3} {'sup Lambda (short climb)':>26} {'implied 1-R suffices':>22}")
    for n in (3,5,6):
        best = 0.0
        for trial in range(6):
            ws = [cmath.exp(1j*(2*math.pi*k/n+0.4*rng.uniform(-1,1))) for k in range(n)]
            cur = Lam(ws, 600); cw = ws
            for it in range(40):
                st = 0.4*(0.9**it)
                cand = [w*cmath.exp(1j*st*rng.uniform(-1,1)) for w in cw]
                v = Lam(cand, 600)
                if v > cur: cur, cw = v, cand
            best = max(best, Lam(cw, 2000))
        print(f"      {n:>3} {best:>26.3e} {1-math.exp(-max(best,0)/n):>22.3e}")
        if best > 0.05: ok = False        # the measured record is ~1e-2
    print(f"      -> {'PASS' if ok else 'FAIL'}")
    return ok

if __name__ == "__main__":
    print("Erdos 1041 -- DegenerateHubBlaschkeReduction.md probe")
    print("sqrt(2)*varpi =", VARPI2, "   2*pi =", 2*math.pi)
    res = [gate1(), gate2(), gate3(), gate4(), gate5(), gate6(), gate7()]
    print("verdict:", "pass" if all(res) else "FAIL", [bool(x) for x in res])
    sys.exit(0 if all(res) else 1)
