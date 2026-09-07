#!/usr/bin/env python3
"""Erdos #1041: deterministic verifier for NearFeketeCuspLaw.md.

Four parts, each of which FAILS (non-zero exit) if the recorded claim stops
holding.

  calib      the branch integrator returns 2r on the equality family
             z^n - r^n, and reproduces the two stored hard witnesses.
  stability  Theorem A (quantitative Fekete stability) holds on a fixed
             deterministic configuration sweep.
  cusp       (2R - min_c L(c)) / rho converges to the recorded kappa_n on
             f = z^n + eps z - R^n, and is independent of R.
  phase      min_phi kappa_n(phi) > 0 on a full sweep of the split direction,
             and the minimum is attained at phi = 0.

Arithmetic is mpmath at 50 digits, but the Gauss-Legendre rule is generated in
float64, so the honest error bar on any length here is 3.9e-16 absolute (the
measured deviation from 2r on the equality family).  No random number generator
is used anywhere, so a failure is reproducible.

Why the integrator is written out here rather than imported: the two defects
described in NearFeketeCuspLaw.md section 5 (scale truncation of the inner
decades, and loss of sigma to rounding) both UNDER-report branch length, i.e.
both flatter the surviving conjecture.  The corrected integrator is the object
under test, so it lives with its test.
"""

from __future__ import annotations

import argparse
import json
import sys

from mpmath import mp

mp.dps = 50

# recorded limits, min over the split direction (attained at phi = 0)
KAPPA = {
    3: mp.mpf("0.60802134"),
    4: mp.mpf("1.0301197"),
    5: mp.mpf("1.2585783"),
    6: mp.mpf("1.3989124"),
}

# StraightSpokeHubCriterionLab.md section 3, stored as exact IEEE-754 literals
DEG6 = [("0x1.fffffaead1dfdp-1", "-0x1.c7f97b12bedcep-15"),
        ("0x1.004ed623acd87p-1", "0x1.bb3a1b3208ad6p-1"),
        ("-0x1.ffded10fb5c87p-2", "0x1.bb713c92edfe4p-1"),
        ("-0x1.fffff9e87dd68p-1", "-0x1.0766ef919e3d1p-12"),
        ("-0x1.00485f6af598cp-1", "-0x1.bb3dd8051992dp-1"),
        ("0x1.00198d2225a68p-1", "-0x1.bb58e733c06dcp-1")]
DEG9 = [("0x1.fffffadb279edp-1", "-0x1.54cbe5f38764ep-14"),
        ("0x1.882fdda9ba317p-1", "0x1.4922d6b3868dfp-1"),
        ("0x1.63e8c845cba7bp-3", "0x1.f83590b0811ebp-1"),
        ("-0x1.fffb9be200080p-2", "0x1.bb68ed350eca4p-1"),
        ("-0x1.e121a80180737p-1", "0x1.5e2df749c719cp-2"),
        ("-0x1.e11b7beb2b6bep-1", "-0x1.5e4fe150117d8p-2"),
        ("-0x1.0005816d133a1p-1", "-0x1.bb647aee76a86p-1"),
        ("0x1.637127244f7d2p-3", "-0x1.f83ad6df31cf7p-1"),
        ("0x1.8833eebb49d0cp-1", "-0x1.491f0e2e50785p-1")]


def _hex(tab):
    return [mp.mpc(mp.mpf(float.fromhex(a)), mp.mpf(float.fromhex(b))) for a, b in tab]


# ------------------------------------------------------------------ machinery

_GL = {}


def gl(nq):
    """Gauss-Legendre nodes on [0,1].

    NOTE ON PRECISION.  The rule itself is generated in float64 and promoted,
    so despite mpmath arithmetic everywhere else the quadrature is accurate to
    about 1e-16 relative, not to mp.dps.  Measured: the equality family
    z^n - r^n returns 2r with absolute error 3.9e-16 at every degree tested.
    That is the honest error bar on every length in this file; it is ample for
    the eight digits of kappa_n recorded, and it is why the calibration
    tolerance below is 1e-14 rather than something dps-shaped."""
    if nq not in _GL:
        import numpy as np
        x, w = np.polynomial.legendre.leggauss(nq)
        _GL[nq] = ([mp.mpf(float(t)) / 2 + mp.mpf("0.5") for t in x],
                   [mp.mpf(float(t)) / 2 for t in w])
    return _GL[nq]


def poly_from_roots(rs):
    c = [mp.mpc(1)]
    for r in rs:
        new = [mp.mpc(0)] * (len(c) + 1)
        for i, ci in enumerate(c):
            new[i] += ci
            new[i + 1] -= ci * r
        c = new
    return c


def taylor(co, a):
    """Taylor coefficients f^{(k)}(a)/k!, ascending."""
    work, out = list(co), []
    while work:
        rem = mp.mpc(0)
        nxt = []
        for x in work:
            rem = rem * a + x
            nxt.append(rem)
        out.append(rem)
        work = nxt[:-1]
    return out


def mec(pts):
    """Exact smallest enclosing circle (pairs + triples).  An APPROXIMATE
    centre inflates R, and R is the denominator of the obligation."""
    n = len(pts)
    tol = mp.mpf(10) ** (-(mp.dps - 10))
    cands = []
    for i in range(n):
        for j in range(i + 1, n):
            cands.append(((pts[i] + pts[j]) / 2, abs(pts[i] - pts[j]) / 2))
    for i in range(n):
        for j in range(i + 1, n):
            for k in range(j + 1, n):
                A, B, C = pts[i], pts[j], pts[k]
                d = 2 * (A.real * (B.imag - C.imag) + B.real * (C.imag - A.imag)
                         + C.real * (A.imag - B.imag))
                if abs(d) < mp.mpf(10) ** (-40):
                    continue
                na, nb, nc = abs(A) ** 2, abs(B) ** 2, abs(C) ** 2
                ux = (na * (B.imag - C.imag) + nb * (C.imag - A.imag)
                      + nc * (A.imag - B.imag)) / d
                uy = (na * (C.real - B.real) + nb * (A.real - C.real)
                      + nc * (B.real - A.real)) / d
                ctr = mp.mpc(ux, uy)
                cands.append((ctr, abs(A - ctr)))
    best = None
    for ctr, R in cands:
        if all(abs(p - ctr) <= R + tol for p in pts) and (best is None or R < best[1]):
            best = (ctr, R)
    return best


def branches(co, c, v, m, nq=20, levels=52):
    """The m descending branches at c.  Shifted coordinates w = z - c and a
    graded dyadic mesh in the parameter s (sigma = s^m); see section 5."""
    tay = taylor(co, c)
    if m >= len(tay) or tay[m] == 0:
        return None
    qc = [mp.mpc(0)] + [(mp.mpc(0) if k < m else tay[k]) for k in range(1, len(tay))]
    qd = [qc[k] * k for k in range(1, len(qc))]

    def Q(w):
        a = mp.mpc(0)
        for ci in reversed(qc):
            a = a * w + ci
        return a

    def dQ(w):
        a = mp.mpc(0)
        for ci in reversed(qd):
            a = a * w + ci
        return a

    def newt(rhs, w):
        for _ in range(80):
            d = dQ(w)
            if d == 0:
                return w
            st = (Q(w) - rhs) / d
            w -= st
            if abs(st) <= mp.mpf(10) ** (-(mp.dps - 8)) * max(mp.mpf(10) ** (-300), abs(w)):
                break
        return w

    xs, ws = gl(nq)
    edges = [mp.mpf(0)] + [mp.mpf(2) ** (-k) for k in range(levels, 0, -1)] + [mp.mpf(1)]
    base = mp.root(-v / tay[m], m)
    out = []
    for k in range(m):
        d0 = base * mp.e ** (2j * mp.pi * k / m)
        tot, w, sp, dp = mp.mpf(0), None, mp.mpf(0), None
        for i in range(len(edges) - 1):
            lo, hi = edges[i], edges[i + 1]
            for u, wt in zip(xs, ws):
                s = lo + (hi - lo) * u
                guess = d0 * s if w is None else w + (-v * m * sp ** (m - 1) / dp) * (s - sp)
                w = newt(-v * s**m, guess)
                dp = dQ(w)
                if dp == 0:
                    return None
                tot += wt * (hi - lo) * abs(-v * m * s ** (m - 1) / dp)
                sp = s
        out.append((tot, c + w))
    return out


def min_pair_length(co, roots, crits, mults=None):
    """min over admissible hubs of the two-branch length reaching two roots."""
    best = None
    for idx, c in enumerate(crits):
        v = mp.polyval(co, c)
        if abs(v) >= 1:
            continue
        m = 2 if mults is None else mults[idx]
        br = branches(co, c, v, m)
        if br is None or len(br) < 2:
            continue
        for i in range(len(br)):
            for j in range(i + 1, len(br)):
                a = min(range(len(roots)), key=lambda t: abs(roots[t] - br[i][1]))
                b = min(range(len(roots)), key=lambda t: abs(roots[t] - br[j][1]))
                if a == b:
                    continue
                L = br[i][0] + br[j][0]
                if best is None or L < best:
                    best = L
    return best


# ------------------------------------------------------------------ parts


def part_calib(rep):
    ok = True
    r = mp.mpf("0.999")
    for n in (3, 4, 5, 6, 7):
        roots = [r * mp.e ** (2j * mp.pi * k / n) for k in range(n)]
        co = poly_from_roots(roots)
        got = min_pair_length(co, roots, [mp.mpc(0)], mults=[n])
        err = abs(got - 2 * r)
        rep.setdefault("calib_equality_family", []).append(
            {"n": n, "min_pair": mp.nstr(got, 20), "target_2r": mp.nstr(2 * r, 20),
             "abs_err": mp.nstr(err, 6)})
        if err > mp.mpf("1e-14"):
            ok = False
    for name, tab, want in (("deg6", DEG6, mp.mpf("1.763942")),
                            ("deg9", DEG9, mp.mpf("1.545995"))):
        roots = _hex(tab)
        co = poly_from_roots(roots)
        crits = mp.polyroots([co[i] * (len(roots) - i) for i in range(len(roots))],
                             maxsteps=400, extraprec=600)
        got = min_pair_length(co, roots, list(crits))
        rep.setdefault("calib_stored_witnesses", []).append(
            {"witness": name, "min_pair": mp.nstr(got, 12), "recorded": mp.nstr(want, 7)})
        if abs(got - want) > mp.mpf("1e-6"):
            ok = False
    return ok


def part_stability(rep):
    """Theorem A on a deterministic configuration sweep."""
    worst = mp.mpf(1)
    worst_at = None
    for n in range(2, 11):
        cfgs = []
        cfgs.append([mp.e ** (2j * mp.pi * k / n) for k in range(n)])          # gon
        for e in ("1e-1", "1e-3", "1e-6"):                                     # perturbed
            ee = mp.mpf(e)
            cfgs.append([mp.e ** (2j * mp.pi * (mp.mpf(k) / n + ee * mp.cos(mp.mpf(7) * k + 1)))
                         for k in range(n)])
        cfgs.append([mp.mpf(k + 1) / (n + 1) for k in range(n)])               # real
        cfgs.append([mp.mpf("0.9") * mp.e ** (2j * mp.pi * k / n) for k in range(n)])
        cfgs.append([mp.mpf("0.5") + mp.mpf("0.1") * mp.e ** (2j * mp.pi * k / n)
                     for k in range(n)])                                       # clustered
        for a in cfgs:
            a = [mp.mpc(x) for x in a]
            G = [[sum(a[t] ** i * mp.conj(a[t]) ** j for t in range(n))
                  for j in range(n)] for i in range(n)]
            g = [mp.re(G[i][i]) for i in range(n)]
            if min(g) <= 0:
                continue
            fro = sum(abs(G[i][j]) ** 2 / (g[i] * g[j])
                      for i in range(n) for j in range(n) if i != j)
            vdm = mp.mpf(1)
            for i in range(n):
                for j in range(i + 1, n):
                    vdm *= abs(a[i] - a[j]) ** 2
            pg = mp.mpf(1)
            for x in g:
                pg *= x
            rhs = pg * mp.e ** (-fro / (2 * n))
            ratio = vdm / rhs                       # must be <= 1
            if ratio > worst:
                worst, worst_at = ratio, n
    rep["stability_worst_vdm_over_bound"] = mp.nstr(worst, 20)
    rep["stability_worst_degree"] = worst_at
    return worst <= 1 + mp.mpf("1e-30")


def part_cusp(rep):
    ok = True
    for R0s in ("0.5", "0.9"):
        R0 = mp.mpf(R0s)
        for n in (3, 4, 5, 6):
            eps = mp.mpf(10) ** (-12)
            rho = mp.root(eps / n, n - 1)
            m = R0**n
            co = [mp.mpc(1)] + [mp.mpc(0)] * (n - 2) + [mp.mpc(eps), mp.mpc(-m)]
            roots = mp.polyroots(co, maxsteps=400, extraprec=600)
            _, R = mec(list(roots))
            crits = [rho * mp.e ** (1j * mp.pi * (2 * k + 1) / (n - 1)) for k in range(n - 1)]
            L = min_pair_length(co, list(roots), crits)
            k = (2 * R - L) / rho
            rel = abs(k - KAPPA[n]) / KAPPA[n]
            rep.setdefault("cusp", []).append(
                {"R": R0s, "n": n, "kappa_measured": mp.nstr(k, 12),
                 "kappa_recorded": mp.nstr(KAPPA[n], 9), "rel_dev": mp.nstr(rel, 4)})
            if k <= 0 or rel > mp.mpf("1e-6"):
                ok = False
    return ok


def part_phase(rep, samples=12):
    ok = True
    R0 = mp.mpf("0.9")
    for n in (3, 4):
        eps = mp.mpf(10) ** (-12)
        rho = mp.root(eps / n, n - 1)
        m = R0**n
        vals = []
        for j in range(samples):
            phi = 2 * mp.pi * j / samples
            co = [mp.mpc(1)] + [mp.mpc(0)] * (n - 2) + [eps * mp.e ** (1j * phi), mp.mpc(-m)]
            roots = mp.polyroots(co, maxsteps=400, extraprec=600)
            _, R = mec(list(roots))
            crits = [rho * mp.e ** (1j * (mp.pi + phi + 2 * mp.pi * t) / (n - 1))
                     for t in range(n - 1)]
            L = min_pair_length(co, list(roots), crits)
            if L is None:
                continue
            vals.append((phi, (2 * R - L) / rho))
        lo = min(v for _, v in vals)
        hi = max(v for _, v in vals)
        at0 = [v for p, v in vals if p == 0][0]
        rep.setdefault("phase", []).append(
            {"n": n, "min_kappa": mp.nstr(lo, 12), "max_kappa": mp.nstr(hi, 12),
             "kappa_at_phi_0": mp.nstr(at0, 12),
             "min_attained_at_phi_0": bool(abs(at0 - lo) <= mp.mpf("1e-20"))})
        if lo <= 0:
            ok = False                       # a non-positive direction refutes the claim
        if abs(at0 - lo) > mp.mpf("1e-20"):
            ok = False                       # recorded: the minimum sits at phi = 0
    return ok


PARTS = {"calib": part_calib, "stability": part_stability,
         "cusp": part_cusp, "phase": part_phase}


def main() -> int:
    ap = argparse.ArgumentParser()
    ap.add_argument("--part", choices=sorted(PARTS) + ["all"], default="all")
    ap.add_argument("--json", action="store_true")
    args = ap.parse_args()
    todo = sorted(PARTS) if args.part == "all" else [args.part]
    rep: dict = {"analysis": "ErdosProblems/Erdos1041/NearFeketeCuspLaw.md",
                 "dps": mp.dps, "parts": {}}
    ok = True
    for name in todo:
        good = PARTS[name](rep)
        rep["parts"][name] = "PASS" if good else "FAIL"
        ok = ok and good
        if not args.json:
            print(f"{name:<10} {'PASS' if good else 'FAIL'}", flush=True)
    rep["status"] = "PASS" if ok else "FAIL"
    if args.json:
        print(json.dumps(rep, indent=1, default=str))
    else:
        for k in ("calib_equality_family", "calib_stored_witnesses", "cusp", "phase"):
            for row in rep.get(k, []):
                print("   ", k, row)
        for k in ("stability_worst_vdm_over_bound", "stability_worst_degree"):
            if k in rep:
                print("   ", k, "=", rep[k])
    return 0 if ok else 1


if __name__ == "__main__":
    sys.exit(main())
