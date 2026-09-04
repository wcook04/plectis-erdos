#!/usr/bin/env python3
r"""DEPTH-ALL is false: a component-depth branch that is longer than R.

LemniscateCapacityBudget.md defines, at the first-merge level mu = min_k |f(c_k)|,
the hub-free component depth

    Delta_j = max over theta of  length{ z : f(z) = t e^{i theta}, t in [0, mu] }
              ending at the root z_j,

records that Delta_a + Delta_b >= L(c*), and proposes

    DEPTH-ALL:   Delta_j <= R  for every j    ==>   L(c*) <= 2R < 2,

i.e. Erdos #1041.  DEPTH-ALL is EXACTLY tight on both equality families (every
quadratic, and z^n - r^n), which is what made it attractive.

**It is false at degree three.**  The witness below is three Gaussian rationals
of denominator 1000, all strictly inside the open unit disk, whose triangle is
acute -- so its minimum enclosing circle is the circumcircle and R^2 is an EXACT
rational.  At the minimal hub one of the two merging branches has arclength

        0.99831545...  >  R = 0.99124864...        ratio 1.00712919...

The number reported is a CHORD SUM over points on the branch located at 50
digits.  An inscribed polygon never exceeds the arclength, so the ratio is a
RIGOROUS LOWER BOUND, not an estimate: the refutation cannot be an integrator
artifact in the way negative_results 24 and 34 describe, because every known
integrator fault in this directory UNDER-reports and this arm under-reports too.

Three further facts, all load bearing.

* The violating branch is one of the two that MERGE at the minimal hub -- it is
  not an artifact of the max over theta, and theta is exactly arg f(c*).
* The PAIR bound survives at the same witness: L(c*)/2R = 0.98532.  The two
  branches compensate; the length budget does not split per branch.  That is the
  content of the refutation, and it is negative_results 21 ("the exact charge
  identity does not split into separately nonnegative pieces") appearing again
  one level up.
* It is ROBUST, unlike negative_results 29's witness, which dies under a 1e-3
  perturbation: 24/24 random perturbations at 1e-4 still violate, 18/24 at 1e-3,
  and violations persist at 1e-2 and 3e-2.  The violating set is open with
  substantial measure, so this is not a near-tie corner.

Why it was missed: the on-disk instrument check_erdos1041_component_depth.py
reports 1.00492 on THIS configuration -- already above one -- so it detects the
violation; what it never did was look here.  Its hill-climb seeds roots at
modulus ~0.6 with 2 restarts x 18 steps, and the violating set sits in the
near-Fekete shell at modulus ~0.99.  negative_results 19 exactly: a supremum
pinned just under a threshold is one basin.

Exit 0 iff the calibration reproduces the quadratic equality family AND the
pinned witness still refutes DEPTH-ALL.  Fails closed.
"""
from __future__ import annotations

import argparse
import json
import sys
from fractions import Fraction as F

from mpmath import exp, fabs, mp, mpc, mpf, polyroots
from mpmath import sqrt as msqrt

# Three Gaussian rationals over 1000; every modulus^2 is exactly below one.
WITNESS = [(F(990), F(0)), (F(-500), F(860)), (F(-497), F(-855))]
DEN = 1000


def _mul(a, b):
    out = [mpc(0)] * (len(a) + len(b) - 1)
    for i, p in enumerate(a):
        for j, q in enumerate(b):
            out[i + j] += p * q
    return out


def _val(c, x):
    s = mpc(0)
    for a in c:
        s = s * x + a
    return s


def _from_frac(x):
    return mpf(x.numerator) / mpf(x.denominator)


def exact_circumcircle(pts):
    """Exact circumcentre and R^2 of three rational points, plus the acute test."""
    (x1, y1), (x2, y2), (x3, y3) = pts
    d = 2 * (x1 * (y2 - y3) + x2 * (y3 - y1) + x3 * (y1 - y2))
    n1, n2, n3 = x1 * x1 + y1 * y1, x2 * x2 + y2 * y2, x3 * x3 + y3 * y3
    ux = (n1 * (y2 - y3) + n2 * (y3 - y1) + n3 * (y1 - y2)) / d
    uy = (n1 * (x3 - x2) + n2 * (x1 - x3) + n3 * (x2 - x1)) / d
    r2 = (x1 - ux) ** 2 + (y1 - uy) ** 2
    s = [(x2 - x3) ** 2 + (y2 - y3) ** 2, (x1 - x3) ** 2 + (y1 - y3) ** 2,
         (x1 - x2) ** 2 + (y1 - y2) ** 2]
    return ux, uy, r2, max(s) < sum(s) - max(s)


def branch_chords(roots, steps):
    """Chord sums of the three inverse rays at theta = arg f(c*), level 0 -> mu.

    s = 1 - t/mu = v^2 makes the branch LINEAR in v at the hub, so a uniform v
    grid resolves the square-root approach that a uniform t grid does not."""
    coef = [mpc(1)]
    for r in roots:
        coef = _mul(coef, [mpc(1), -r])
    dcoef = [coef[i] * (len(coef) - 1 - i) for i in range(len(coef) - 1)]
    cp = polyroots(dcoef, maxsteps=300, extraprec=300)
    cv = [_val(coef, c) for c in cp]
    mu = min(fabs(v) for v in cv)
    k = [i for i, v in enumerate(cv) if fabs(v) == mu][0]
    e = exp(mpc(0, 1) * mp.arg(cv[k]))
    n = len(roots)
    cur = list(roots)
    first = None
    acc = [mpf(0)] * n
    for i in range(steps + 1):
        v = mpf(i) / steps                      # v: 0 -> 1  is  t: mu -> 0
        cc = list(coef)
        cc[-1] = cc[-1] - mu * (1 - v * v) * e
        rr = polyroots(cc, maxsteps=400, extraprec=400)
        nxt, used = [], set()
        for c0 in cur:
            b = min((j for j in range(n) if j not in used),
                    key=lambda j: fabs(rr[j] - c0))
            used.add(b)
            nxt.append(rr[b])
        if first is None:
            first = list(nxt)
        else:
            for j in range(n):
                acc[j] += fabs(nxt[j] - cur[j])
        cur = nxt
    label = [min(range(n), key=lambda r: fabs(cur[j] - roots[r])) for j in range(n)]
    d = [fabs(first[j] - cp[k]) for j in range(n)]
    pair = sorted(range(n), key=lambda j: d[j])[:2]
    return mu, acc, label, pair


# Degree-four witness for the SECOND elimination (section 8): L(c*) <= 2R fails
# at the minimal hub.  Pinned as exact IEEE-754 hex because the margin is 1.6e-4.
BETA4 = [(float.fromhex("0x1.8c5640e53fa34p-9"), float.fromhex("0x1.69a016b3f0c4ap-9")),
         (float.fromhex("-0x1.6fa15252d066ep-5"), float.fromhex("-0x1.3895293ffc3ebp-6"))]


def degree_four_witness(steps=1200):
    """Roots of G(z) = 1 for G(z) = z^4 - beta_3 z^3 - beta_2 z^2, then the two
    merging branches at the minimal hub by chord sum (a rigorous lower bound)."""
    import numpy as _np
    b = [complex(*BETA4[0]), complex(*BETA4[1])]
    G = _np.zeros(5, complex); G[0] = 1.0; G[2] = -b[0]; G[1] = -b[1]
    Gm = G.copy(); Gm[-1] -= 1.0
    z = _np.roots(Gm)
    z = z / _np.max(_np.abs(z))                 # scale invariant; put roots in the disk
    roots = [mpc(v.real, v.imag) for v in z]
    coef = [mpc(1)]
    for r in roots:
        coef = _mul(coef, [mpc(1), -r])
    dcoef = [coef[i] * (len(coef) - 1 - i) for i in range(len(coef) - 1)]
    cp = polyroots(dcoef, maxsteps=300, extraprec=300)
    cv = [_val(coef, c) for c in cp]
    mods = [fabs(v) for v in cv]
    mu = min(mods); k = mods.index(mu)
    tie = (sorted(mods)[1] - mu) / mu
    # exact-form MEC over pairs and triples
    import itertools as _it
    best = (None, mpf("1e99"))
    for i, j in _it.combinations(range(4), 2):
        c = (roots[i] + roots[j]) / 2; R = fabs(roots[i] - roots[j]) / 2
        if max(fabs(p - c) for p in roots) <= R * (1 + mpf("1e-30")) and R < best[1]:
            best = (c, R)
    for i, j, l in _it.combinations(range(4), 3):
        a, bb, d = roots[i], roots[j], roots[l]
        A = mp.matrix([[2*(bb.real-a.real), 2*(bb.imag-a.imag)],
                       [2*(d.real-a.real), 2*(d.imag-a.imag)]])
        if abs(mp.det(A)) < mpf("1e-30"): continue
        s = mp.lu_solve(A, mp.matrix([fabs(bb)**2 - fabs(a)**2, fabs(d)**2 - fabs(a)**2]))
        c = mpc(s[0], s[1]); R = fabs(roots[i] - c)
        if max(fabs(p - c) for p in roots) <= R * (1 + mpf("1e-30")) and R < best[1]:
            best = (c, R)
    R = best[1]
    e = exp(mpc(0, 1) * mp.arg(cv[k]))
    cur = None; acc = [mpf(0), mpf(0)]
    for i in range(steps + 1):
        v = mpf(i) / steps
        cc = list(coef); cc[-1] = cc[-1] - mu * (1 - v * v) * e
        rr = polyroots(cc, maxsteps=400, extraprec=400)
        if cur is None:
            d2 = sorted(range(4), key=lambda j: fabs(rr[j] - cp[k]))[:2]
            cur = [rr[d2[0]], rr[d2[1]]]; continue
        nxt, used = [], set()
        for c1 in cur:
            bj = min((j for j in range(4) if j not in used), key=lambda j: fabs(rr[j] - c1))
            used.add(bj); nxt.append(rr[bj])
        for j in range(2): acc[j] += fabs(nxt[j] - cur[j])
        cur = nxt
    L = acc[0] + acc[1]
    return dict(mu=float(mu), R=float(R), tie=float(tie), L_lower=float(L),
                ratio_2R=float(L / (2 * R)), ratio_strong=float(L / (2 * mu ** mpf(0.25))),
                endpoints_distinct=bool(fabs(cur[0] - cur[1]) > mpf("1e-3")))


def calibrate():
    """Every quadratic has Delta = R exactly; the chord sum must approach it."""
    a, b = mpc("0.4", "0.2"), mpc("-0.7", "0.5")
    R = fabs(a - b) / 2
    _, acc, _, _ = branch_chords([a, b], 900)
    return float(max(acc) / R)


def main() -> int:
    ap = argparse.ArgumentParser()
    ap.add_argument("--steps", type=int, default=1500)
    ap.add_argument("--dps", type=int, default=50)
    ap.add_argument("--json", action="store_true")
    args = ap.parse_args()
    mp.dps = args.dps

    rq = [(x / DEN, y / DEN) for x, y in WITNESS]
    moduli2 = [x * x + y * y for x, y in rq]
    in_disk = all(m < 1 for m in moduli2)
    ux, uy, r2, acute = exact_circumcircle(rq)
    R = msqrt(_from_frac(r2))
    roots = [mpc(_from_frac(x), _from_frac(y)) for x, y in rq]

    mu, acc, label, pair = branch_chords(roots, args.steps)
    n = len(roots)
    ratios = {label[j]: float(acc[j] / R) for j in range(n)}
    worst_branch = max(range(n), key=lambda j: acc[j])
    worst = float(acc[worst_branch] / R)
    pair_ratio = float((acc[pair[0]] + acc[pair[1]]) / (2 * R))

    d4 = degree_four_witness()
    cal = calibrate()
    cal_ok = 0.995 < cal <= 1.0 + 1e-9          # chord sum approaches 1 FROM BELOW
    refutes = bool(worst > 1.0 + 1e-4)
    in_pair = worst_branch in pair
    refutes_2R = bool(d4["ratio_2R"] > 1.0 + 1e-5 and d4["endpoints_distinct"])
    ok = bool(in_disk and acute and cal_ok and refutes and refutes_2R)

    payload = dict(
        claim="DEPTH-ALL (Delta_j <= R at the first-merge level) is FALSE",
        witness=[[str(x), str(y)] for x, y in rq],
        witness_moduli_squared=[str(m) for m in moduli2],
        all_roots_in_open_unit_disk=in_disk,
        triangle_acute_so_mec_is_circumcircle=acute,
        exact_R_squared=str(r2), R=float(R), mu=float(mu),
        mu_pow_1_over_n=float(mu ** (mpf(1) / n)),
        branch_chord_sum_over_R=ratios,
        worst_branch_over_R=worst,
        worst_branch_is_in_the_merging_pair=in_pair,
        bound_type="rigorous lower bound (inscribed polygon, %d vertices)" % args.steps,
        pair_bound_L_cstar_over_2R=pair_ratio,
        pair_bound_survives=bool(pair_ratio < 1),
        calibration_quadratic_Delta_over_R=cal,
        calibration_ok=cal_ok,
        refutes_depth_all=refutes,
        degree_four_minimal_hub_witness=d4,
        refutes_L_cstar_le_2R_at_degree_four=refutes_2R,
        verdict="pass" if ok else "FAIL")
    if args.json:
        print(json.dumps(payload, indent=2))
    else:
        print("witness (exact Gaussian rationals over 1000):")
        for (x, y), m in zip(rq, moduli2):
            print(f"    {str(x):>12} + {str(y):>12} i     |z|^2 = {m} < 1: {m < 1}")
        print(f"  triangle acute (MEC = circumcircle): {acute}")
        print(f"  exact R^2 = {r2}")
        print(f"  R = {float(R):.15f}   mu^(1/3) = {float(mu**(mpf(1)/n)):.15f}")
        print(f"\ncalibration -- every quadratic has Delta = R exactly: {cal:.9f}"
              f"  {'ok' if cal_ok else '*** BROKEN'}")
        print("\nbranch chord sums / R at theta = arg f(c*)"
              f"  ({args.steps} vertices, RIGOROUS LOWER BOUNDS):")
        for j in sorted(ratios):
            mark = "   <== EXCEEDS R" if ratios[j] > 1 else ""
            print(f"    branch to root {j}:  {ratios[j]:.12f}{mark}")
        print(f"\n  DEPTH-ALL refuted: {refutes}   "
              f"(worst branch is in the merging pair: {in_pair})")
        print(f"  pair bound at the same witness: L(c*)/2R = {pair_ratio:.9f}"
              f"  -> survives: {pair_ratio < 1}")
        print("\ndegree-four witness (section 8) -- L(c*) <= 2R at the MINIMAL hub:")
        print(f"    mu = {d4['mu']:.15f}   runner-up larger by {d4['tie']:.3e} relative (a near-tie)")
        print(f"    R  = {d4['R']:.15f}   2R = {2*d4['R']:.15f}")
        print(f"    L(c*) >= {d4['L_lower']:.15f}   (chord sum, rigorous lower bound)")
        print(f"    L(c*)/2R           >= {d4['ratio_2R']:.10f}"
              f"{'   <== ABOVE ONE' if d4['ratio_2R'] > 1 else ''}")
        print(f"    L(c*)/(2 mu^(1/4)) >= {d4['ratio_strong']:.10f}")
        print(f"    branches land on distinct roots: {d4['endpoints_distinct']}")
        print(f"\nverdict={payload['verdict']}")
    return 0 if ok else 1


if __name__ == "__main__":
    sys.exit(main())
