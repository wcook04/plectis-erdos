#!/usr/bin/env python3
r"""The minimal hub has exactly n-2 complex moduli, and admissibility is the
whole content at degree three.

REDUCTION.  Translate the minimal hub c* to 0, scale by rho = mu^{1/n} with
mu = |f(c*)|, and rotate so that arg f(c*) = pi.  Then

        f(rho*zeta) / f(c*)  =  1 - G(zeta),
        G(zeta) = zeta^n - sum_{k=2}^{n-1} beta_k zeta^k        (monic, G(0)=G'(0)=0),

so EVERYTHING about the hub is the n-2 complex parameters beta = (beta_2,...,beta_{n-1}):

  * the two descending branches solve  G(zeta) = s,  s : 0 -> 1, from zeta = 0;
  * the hub is MINIMAL exactly when every other critical value v of G satisfies
    |1 - v| >= 1, i.e. the critical values of G avoid the OPEN DISK D(1,1);
  * the roots of f are the roots of G(zeta) = 1, of circumradius Rt = R/rho;
  * L(c*) <= 2 mu^{1/n}  <=>  L(beta) <= 2         (the strong form, entry 29)
  * L(c*) <= 2R          <=>  L(beta) <= 2 Rt(beta)   (the standing obligation)
  * Fekete is exactly Rt >= 1, so the strong form implies the obligation.

Three things this buys that root coordinates do not.

1. n = 2 HAS AN EMPTY MODULI SPACE.  There are no beta at all, G = zeta^2, the
   branches are +/- sqrt(s), and L = 2 identically.  That is the structural
   reason every monic quadratic is an equality case -- not a coincidence of the
   normalisation, but the absence of any parameter to vary.

2. n = 3 IS ONE COMPLEX PARAMETER.  G = zeta^3 - beta zeta^2 and, because
   zeta -> omega zeta sends beta -> omega^2 beta with omega^3 = 1, every
   quantity depends only on gamma = 4 beta^3/27, the other critical value of G.
   Admissibility is exactly  |1 + gamma| >= 1:  gamma OUTSIDE the open disk
   D(-1,1).  The extremal family z^3 - r^3 is gamma = 0 -- a single point, and it
   lies ON the boundary circle of that disk.

3. ADMISSIBILITY IS LOAD BEARING, AND HERE IS THE MARGIN.  Over the admissible
   region the strong form holds with supremum 1 at gamma = 0; a short distance
   INSIDE the excluded disk it fails, reaching L/2 = 1.0163.  So at the minimal
   degree the entire content of the strong form is the minimality of the hub.
   Along the boundary circle |1 + gamma| = 1, L/2 decreases monotonically away
   from gamma = 0.

Searching beta-space also quotients out translation, rotation and scale:
2(n-2) real parameters against 2n for a root configuration, with admissibility
an explicit constraint rather than something a search has to stumble into.

Exit 0 iff beta -> 0 reproduces L = 2 and Rt = 1, AND the inadmissible side of
degree three still breaks the strong form.  Fails closed: if the second check
stops firing, the constraint has stopped being load bearing and the numbers
below mean nothing.
"""
from __future__ import annotations

import argparse
import itertools
import json
import sys

import numpy as np
from numpy.polynomial.legendre import leggauss


def mec_exact(z):
    z = np.asarray(z, complex); best = (None, np.inf); tol = 1e-11
    for i, j in itertools.combinations(range(len(z)), 2):
        c = (z[i] + z[j]) / 2; R = abs(z[i] - z[j]) / 2
        if np.max(np.abs(z - c)) <= R * (1 + tol) + tol and R < best[1]: best = (c, R)
    for i, j, k in itertools.combinations(range(len(z)), 3):
        a, b, d = z[i], z[j], z[k]
        A = np.array([[2 * (b.real - a.real), 2 * (b.imag - a.imag)],
                      [2 * (d.real - a.real), 2 * (d.imag - a.imag)]])
        if abs(np.linalg.det(A)) < 1e-14: continue
        s = np.linalg.solve(A, np.array([abs(b) ** 2 - abs(a) ** 2,
                                         abs(d) ** 2 - abs(a) ** 2]))
        c = s[0] + 1j * s[1]; R = abs(z[i] - c)
        if np.max(np.abs(z - c)) <= R * (1 + tol) + tol and R < best[1]: best = (c, R)
    return best


def _mesh(per=10, K=44):
    """Geometric mesh in v (s = v^2): the hub may be nearly degenerate, and then
    the branch crosses many decades of |zeta| inside a vanishing range of s."""
    x, w = leggauss(per)
    edges = [0.0] + [2.0 ** -j for j in range(K, 0, -1)] + [1.0]
    v, ww = [], []
    for lo, hi in zip(edges[:-1], edges[1:]):
        v.append((x + 1) / 2 * (hi - lo) + lo); ww.append(w / 2 * (hi - lo))
    v = np.concatenate(v); ww = np.concatenate(ww)
    o = np.argsort(v)
    return v[o], ww[o]


_V, _W = _mesh()


def analyse(beta, n, need_R=True):
    beta = np.asarray(beta, complex)
    if beta.size and abs(beta[0]) < 1e-13: return None
    G = np.zeros(n + 1, complex); G[0] = 1.0
    for k in range(2, n): G[n - k] = -beta[k - 2]
    dG = np.polyder(G)
    cz = np.roots(dG); cz = cz[np.abs(cz) > 1e-9]
    cv = np.polyval(G, cz) if cz.size else np.array([], complex)
    slack = float(np.min(np.abs(1 - cv)) - 1) if cv.size else float("inf")
    amp = 1.0 / np.sqrt(-beta[0])
    cur = np.array([amp, -amp]) * _V[0]
    acc = np.zeros(2)
    for v, w in zip(_V, _W):
        tgt = v * v
        for _ in range(14):
            d = np.polyval(dG, cur)
            if np.any(d == 0): return None
            st = (np.polyval(G, cur) - tgt) / d
            cur = cur - st
            if np.max(np.abs(st)) < 1e-14 * (1e-300 + np.max(np.abs(cur))): break
        if np.max(np.abs(np.polyval(G, cur) - tgt)) > 1e-9 * max(1.0, tgt): return None
        if abs(cur[0] - cur[1]) < 1e-13 * max(1e-300, abs(cur[0])): return None
        ad = np.abs(np.polyval(dG, cur))
        if np.any(ad == 0): return None
        acc += w * 2 * v / ad
    L = float(acc.sum())
    out = dict(L=L, slack=slack, admissible=bool(slack >= -1e-12), strong=L / 2.0)
    if need_R:
        Gm = G.copy(); Gm[-1] -= 1.0
        _, Rt = mec_exact(np.roots(Gm))
        out.update(Rt=Rt, obligation=L / (2 * Rt))
    return out


BOUNDARY_P = -3.0 / 2 ** (2 / 3.0)


def boundary_family(a):
    """f_a(z) = z^3 + BOUNDARY_P z + i a.

    Derivation: for f = z^3 + p z + q the critical values are q +/- w with
    w = (2p/3) sqrt(-p/3), so the two are EQUAL IN MODULUS iff Re(conj(q) w) = 0.
    Putting p = -3 u^2 gives w = -2 u^3; choosing u = -2^{-1/3} makes w = 1, and
    then the tie condition is exactly q purely imaginary.  Scaling fixes |w| = 1
    and rotation fixes arg w, so up to the symmetries this ONE REAL PARAMETER
    family is the whole admissibility boundary at degree three -- the locus the
    plurisubharmonic maximum principle sends the extremal problem to.
    Both critical values have modulus sqrt(a^2+1)."""
    coef = np.array([1.0, 0.0, BOUNDARY_P, 1j * a], complex)
    cp = np.roots(np.polyder(coef))
    cv = np.polyval(coef, cp)
    return coef, cv, float(np.abs(cv).min())


def cubic(gamma):
    return analyse(np.array([(27 * gamma / 4) ** (1 / 3.0)]), 3)


def main() -> int:
    ap = argparse.ArgumentParser()
    ap.add_argument("--angles", type=int, default=36)
    ap.add_argument("--json", action="store_true")
    args = ap.parse_args()

    # 1a. calibration: beta -> 0 is the equality family z^n - r^n.  Only n = 3, 4
    #     can be calibrated this way.  For n >= 5 the all-equal direction is NOT
    #     admissible near 0 -- see the boundary note below -- and the simple-hub
    #     model over-reports there by about |beta|^{1/(n-2)}, so those rows are
    #     reported as a measured instrument boundary and are NOT a pass criterion.
    cal, boundary = [], []
    for n in (3, 4):
        r = analyse(np.full(n - 2, 1e-10 + 0j), n)
        cal.append(dict(n=n, L=r["L"], Rt=r["Rt"], slack=r["slack"]))
    for n in (5, 6, 8):
        r = analyse(np.full(n - 2, 1e-10 + 0j), n)
        boundary.append(dict(n=n, L=r["L"], slack=r["slack"],
                             note="all-equal direction sits on the admissibility boundary"))
    cal_ok = all(abs(c["L"] - 2) < 1e-8 and abs(c["Rt"] - 1) < 1e-8 for c in cal)

    # 1b. mesh self-consistency at admissible beta: the honest accuracy check.
    conv = []
    global _V, _W
    keep = (_V, _W)
    for n, b in ((3, [0.6 + 0.2j]), (4, [0.5 - 0.3j, 0.2 + 0.1j]),
                 (5, [0.7 + 0.1j, -0.2 + 0.3j, 0.15 - 0.05j])):
        _V, _W = _mesh(10, 44); a = analyse(np.array(b, complex), n, need_R=False)
        _V, _W = _mesh(14, 52); c2 = analyse(np.array(b, complex), n, need_R=False)
        _V, _W = keep
        if a is None or c2 is None: conv.append(dict(n=n, delta=None)); continue
        conv.append(dict(n=n, L=a["L"], delta=abs(a["L"] - c2["L"]), admissible=a["admissible"]))
    conv_ok = all(c["delta"] is not None and c["delta"] < 1e-8 for c in conv)
    cal_ok = cal_ok and conv_ok

    # 2. degree three: the strong form on both sides of the constraint.
    adm, inadm = (-9.0, None), (-9.0, None)
    for mod in (1e-3, 3e-3, 1e-2, 3e-2, 0.1, 0.25, 0.5):
        for k in range(args.angles):
            g = mod * np.exp(2j * np.pi * k / args.angles)
            r = cubic(g)
            if r is None: continue
            ok = abs(1 + g) >= 1 - 1e-14
            tgt = adm if ok else inadm
            if r["strong"] > tgt[0]:
                if ok: adm = (r["strong"], complex(g))
                else: inadm = (r["strong"], complex(g))

    # 3. the admissibility boundary |1+gamma| = 1, where the extremum sits.
    prof, mono = [], True
    prev = None
    for psi in (0.005, 0.01, 0.02, 0.04, 0.08, 0.15, 0.3, 0.5, 0.8, 1.2, 1.6, 2.0, 2.5, 3.0):
        r = cubic(-1 + np.exp(1j * psi))
        if r is None: continue
        prof.append(dict(psi=psi, strong=r["strong"]))
        if prev is not None and r["strong"] > prev + 1e-9: mono = False
        prev = r["strong"]

    # 3b. the boundary family, as an INDEPENDENT route to the same profile:
    #     the tie is exact by construction, and psi = arg(f(c2)/f(c1)) is the
    #     same angle that parametrises the gamma-circle above.
    fam, tie_ok = [], True
    for a in (0.0, 0.3, 1.0, 3.0, 10.0, 50.0):
        coef, cv, mu = boundary_family(a)
        if abs(abs(cv[0]) - abs(cv[1])) > 1e-12 * max(1.0, abs(cv[0])): tie_ok = False
        psi = float(abs(np.angle(cv[1] / cv[0])))
        g = -1 + np.exp(1j * psi)
        r = cubic(g)
        fam.append(dict(a=a, mod=float(abs(cv[0])), psi=psi,
                        strong_from_gamma=None if r is None else r["strong"]))
    fam_monotone = all(fam[i]["strong_from_gamma"] <= fam[i+1]["strong_from_gamma"] + 1e-9
                       for i in range(len(fam)-1))

    constraint_is_load_bearing = bool(inadm[0] > 1 + 1e-4 and adm[0] <= 1 + 1e-6)
    ok = bool(cal_ok and constraint_is_load_bearing and tie_ok)
    _ = boundary

    payload = dict(
        reduction="hub -> 0, scale mu^{1/n}, rotate: G(z)=z^n - sum beta_k z^k, n-2 complex moduli",
        moduli_dimension={n: n - 2 for n in (2, 3, 4, 5, 6)},
        n2_note="n=2 has an EMPTY moduli space, so L = 2 identically -- why every quadratic is an equality case",
        calibration=cal, mesh_convergence=conv, degenerate_limit_boundary=boundary,
        calibration_ok=cal_ok,
        degree3_sup_strong_admissible=adm[0], degree3_argmax_admissible=str(adm[1]),
        degree3_sup_strong_inadmissible=inadm[0], degree3_argmax_inadmissible=str(inadm[1]),
        constraint_is_load_bearing=constraint_is_load_bearing,
        boundary_profile=prof, boundary_monotone_decreasing=mono,
        boundary_family="f_a(z) = z^3 - 3*2^{-2/3} z + i a, a real -- the whole degree-three tie locus",
        boundary_family_rows=fam, boundary_family_tie_exact=tie_ok,
        boundary_family_monotone_in_a=fam_monotone,
        verdict="pass" if ok else "FAIL")
    if args.json:
        print(json.dumps(payload, indent=2))
    else:
        print("calibration -- beta -> 0 must give L = 2 and Rt = 1 (the family z^n - r^n):")
        for c in cal:
            print(f"    n={c['n']}   L = {c['L']:.9f}   Rt = {c['Rt']:.9f}")
        print("  mesh self-consistency at admissible beta (K=44/per=10 vs K=52/per=14):")
        for c in conv:
            print(f"    n={c['n']}   |dL| = {c['delta']:.2e}")
        print("  instrument boundary -- the all-equal direction is NOT admissible for n >= 5,")
        print("  and the simple-hub model over-reports there; reported, not used as a gate:")
        for c in boundary:
            print(f"    n={c['n']}   L = {c['L']:.9f}   slack = {c['slack']:+.2e}")
        print(f"  calibration_ok = {cal_ok}")
        print("\ndegree three, one complex parameter gamma = 4 beta^3/27:")
        print(f"    sup L/2 over ADMISSIBLE   gamma (outside D(-1,1)) = {adm[0]:.9f}  at {adm[1]}")
        print(f"    sup L/2 over INADMISSIBLE gamma (inside  D(-1,1)) = {inadm[0]:.9f}  at {inadm[1]}")
        print(f"    -> minimality of the hub is the WHOLE content: {constraint_is_load_bearing}")
        print("\nalong the admissibility boundary |1+gamma| = 1  (gamma = -1 + e^{i psi}):")
        for p in prof:
            print(f"    psi = {p['psi']:<6} L/2 = {p['strong']:.9f}")
        print(f"    monotone decreasing away from gamma = 0: {mono}")
        print("\nthe same boundary as ONE REAL PARAMETER:  f_a(z) = z^3 - 3*2^(-2/3) z + i a")
        print("  (both critical values have modulus sqrt(a^2+1) -- the tie is exact by construction)")
        for r in fam:
            print(f"    a = {r['a']:<6} |f(c)| = {r['mod']:.8f}   psi = {r['psi']:.6f}"
                  f"   L/2 = {r['strong_from_gamma']:.9f}")
        print(f"    tie exact at every a: {tie_ok};  L/2 increasing in a: {fam_monotone}")
        print(f"\nverdict={payload['verdict']}")
    return 0 if ok else 1


if __name__ == "__main__":
    sys.exit(main())
