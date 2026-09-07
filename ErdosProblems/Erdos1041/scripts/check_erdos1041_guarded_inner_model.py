#!/usr/bin/env python3
"""Erdos #1041: deterministic verifier for NearFeketeGuardedInnerModel.md.

The near-Fekete inner model of NearFeketeInnerModelWidening.md reduces the
surviving obligation

    (MIN)   min over critical points c with |f(c)| < 1 of L(c) <= 2R

to the inner statement

    (MIN-inner)   min_j A_j <= 0,   A_j = -2|Z_j| + int over both arms (1-cos chi) ds,

for Q' = n prod_j (Z - Z_j), sum_j Z_j = 0, max_j |Z_j| = 1, arms being the
lifts of the horizontal ray Q = Q(Z_j) + s, s real increasing.  The degree-five
"refutation" recorded in that note was WITHDRAWN because its configuration sits
on the saddle-connection wall (two critical values with equal imaginary part to
1.8e-12 and ordered real parts, so one hub's arm runs into another hub).

This script tests what survives once the wall guard is imposed properly.

  wall      the wall specimen's ambiguous hub has TWO continuations, one per
            outgoing arm of the hub its arm runs into; they are computed by
            surgery and by two-sided limits and must agree.  The lower one is
            negative, so (MIN-inner) survives ON the wall in the
            lower-continuation reading.
  guarded   the recorded wall-guarded maximisers reproduce their min_j A_j at
            two tracing radii and two tolerances, and pass the guard: hub
            separation, the value-plane Im gap at the stated width, and the
            GEOMETRIC clearance (distance from every traced arm to every other
            critical point).
  refute    the guarded degree-five maximiser, carried to an actual monic
            quintic f' = 5 prod (z - rho Z_j), f(0) = -c^n, gives
            min_c L(c) > 2R at four values of rho, with (min_c L(c) - 2R)/rho
            converging linearly to the inner prediction.  Chord-sum audited.
  shell     the same configuration at c -> 1 gives an actual quintic with all
            roots strictly inside the open unit disc and min_c L(c) > 2, while
            the origin's two shortest straight spokes are contained and total
            below 2.  The branch-pair mechanism dies; Erdos 1041 does not.
  selectors three candidate hub selectors that would have implied (MIN-inner)
            are refuted on deterministic guarded samples.

Arithmetic.  The inner tracer is an adaptive Cash-Karp RK45 written out here in
scalar complex float64; arc length is carried as an INTEGRATED ODE STATE, never
as a chord sum.  Actual polynomials are built from their OWN exact coefficients
at 80 mpmath digits, never reconstructed from float64 roots.  R is reported as
max_k |a_k - o| for an exhibited centre o, hence an UPPER bound for the true
circumradius, so min_c L(c) > 2R is only weakened by an imprecise centre.  No
random number generator is used, so a failure is reproducible.
"""

from __future__ import annotations

import argparse
import cmath
import itertools
import json
import math
import sys

import numpy as np

# --------------------------------------------------------------------------
# recorded rows under test
# --------------------------------------------------------------------------

# the WITHDRAWN degree-five wall specimen of NearFeketeInnerModelWidening 5.4
WALL_SPECIMEN = [
    [-0.48805079116945244, -0.0003542519331306829],
    [-0.4971815689676606, -0.01556459260195624],
    [0.9999957080391201, 0.002929829916397283],
    [-0.014763347902007076, 0.012989014618689643],
]
# its ambiguous hub (0-indexed) and the hub its arm runs into
WALL_AMBIGUOUS = (1, 0)
WALL_CONTINUATIONS = (0.022910, -0.752866)      # upper, lower; tolerance 2e-4

# wall-guarded maximisers of min_j A_j found by deterministic Nelder-Mead
# climbs (seeded restarts; see NearFeketeGuardedInnerModel.md section 3)
GUARDED = {
    "n5_g1em4": {
        "n": 5, "g": 1e-4,
        "Z": [[-0.484542215051725, 0.05144206683972985],
              [-0.4790225872657048, -0.05048178067995962],
              [0.9999999811212439, -0.00019431292175353673],
              [-0.03643517880381401, -0.0007659732380166911]],
        "minA": 0.0382254105, "tol": 2e-8,
    },
    "n5_g1em3": {
        "n": 5, "g": 1e-3,
        "Z": [[-0.4813448740770264, 0.0560997215787875],
              [-0.48697068697373264, -0.06225801544932408],
              [0.9999995222452515, 0.000977501544196589],
              [-0.0316839611944924, 0.005180792326339986]],
        "minA": 0.0022916068, "tol": 2e-8,
    },
    "n6_g1em4": {
        "n": 6, "g": 1e-4,
        "Z": [[-0.2644444374393768, 0.1297931330695117],
              [-0.4366367339067514, -0.49853009658861575],
              [-0.02806556341344416, 0.11117615450057781],
              [-0.2703231734387016, 0.2250046635750954],
              [0.999469908198274, 0.03255614544343074]],
        "minA": 0.0614192457, "tol": 2e-8,
    },
}

# the actual-polynomial rows, c = 9/10; tolerance 1e-6 on (min_c L - 2R)/rho
REFUTE_CASES = {
    "n5_g1em4": {"rhos": (0.02, 0.01, 0.005, 0.0025),
                 "over_rho": (0.02260395, 0.03046076, 0.03435461, 0.03629290)},
    "n6_g1em4": {"rhos": (0.02, 0.01, 0.005),
                 "over_rho": (0.05158839, 0.05650472, 0.05896210)},
}

# the near-Fekete shell row: same Z, c = 9999/10000, rho = 1/50
SHELL = {"c": 0.9999, "rho": 0.02, "minL": 2.000405278363, "max_abs_root": 0.999998424336917,
         "origin_two_spokes": 1.999641}


# --------------------------------------------------------------------------
# scalar-complex Cash-Karp RK45
# --------------------------------------------------------------------------

_A = [(), (0.2,), (3 / 40, 9 / 40), (0.3, -0.9, 1.2),
      (-11 / 54, 2.5, -70 / 27, 35 / 27),
      (1631 / 55296, 175 / 512, 575 / 13824, 44275 / 110592, 253 / 4096)]
_C = (0.0, 0.2, 0.3, 0.6, 1.0, 0.875)
_B5 = (37 / 378, 0.0, 250 / 621, 125 / 594, 0.0, 512 / 1771)
_B4 = (2825 / 27648, 0.0, 18575 / 48384, 13525 / 55296, 277 / 14336, 0.25)


def _steps(rhs, t, Z, L, h):
    kz, kl = [], []
    for i in range(6):
        zz, ll = Z, L
        for j, a in enumerate(_A[i]):
            zz = zz + h * a * kz[j]
            ll = ll + h * a * kl[j]
        dz, dl = rhs(t + _C[i] * h, zz)
        kz.append(dz)
        kl.append(dl)
    z5 = z4 = Z
    l5 = l4 = L
    for b, k in zip(_B5, kz):
        z5 = z5 + h * b * k
    for b, k in zip(_B4, kz):
        z4 = z4 + h * b * k
    for b, k in zip(_B5, kl):
        l5 = l5 + h * b * k
    for b, k in zip(_B4, kl):
        l4 = l4 + h * b * k
    return z5, z4, l5, l4


# --------------------------------------------------------------------------
# the inner model
# --------------------------------------------------------------------------

def normalise(Zc):
    mu = sum(Zc) / len(Zc)
    Z = [z - mu for z in Zc]
    sc = max(abs(z) for z in Z)
    if sc < 1e-12:
        return None
    return [z / sc for z in Z]


def _dQ(Zc, n):
    def f(Z):
        d = float(n)
        for r in Zc:
            d = d * (Z - r)
        return d
    return f


def qpoly(Zc):
    """Q with Q(0) = 0 and Q' = n prod (Z - Z_j)."""
    n = len(Zc) + 1
    co = [1.0 + 0j]
    for r in Zc:
        new = [0j] * (len(co) + 1)
        for i, a in enumerate(co):
            new[i] += a
            new[i + 1] -= a * r
        co = new
    qc = [n * a / (len(co) - i) for i, a in enumerate(co)] + [0j]

    def Q(Z):
        v = 0j
        for a in qc:
            v = v * Z + a
        return v
    return Q


def crit_values(Zc):
    Q = qpoly(Zc)
    return [Q(z) for z in Zc]


def wall_report(Zc):
    """(min hub separation, min ordered Im-value gap / value scale, scale)."""
    V = crit_values(Zc)
    m = len(Zc)
    sep = min(abs(Zc[i] - Zc[j]) for i in range(m) for j in range(i + 1, m))
    scale = max(abs(v) for v in V) or 1.0
    gap = float("inf")
    for i in range(m):
        for j in range(m):
            # the arm of hub j runs rightward in value, so it can only reach
            # hub i when Re V_i > Re V_j
            if i != j and V[i].real > V[j].real:
                gap = min(gap, abs(V[i].imag - V[j].imag))
    return sep, gap / scale, scale


def trace_arm(Zc, n, c, alpha, radii, rtol=1e-12, atol=1e-14, maxsteps=200000):
    """One outgoing arm.  Returns (excess at each radius, escape sector,
    geometric clearance to the other critical points)."""
    dQ = _dQ(Zc, n)

    def rhs(sig, Z):
        d = dQ(Z)
        if abs(d) < 1e-300:
            return 0j, 0.0
        dz = (2.0 * sig) / d
        return dz, abs(dz)

    s0 = 1e-9
    Z = c + alpha * s0
    L, sig = 0.0, s0
    sig_max = 4.0 * radii[-1] ** (n / 2.0)
    h = sig_max / 1000.0
    out, ri, steps = [], 0, 0
    clear = float("inf")
    others = [r for r in Zc if abs(r - c) > 1e-14]
    while ri < len(radii) and sig < sig_max and steps < maxsteps:
        steps += 1
        h = min(h, sig_max - sig)
        z5, z4, l5, l4 = _steps(rhs, sig, Z, L, h)
        err = max(abs(z5 - z4) / (atol + rtol * max(abs(z5), abs(Z))),
                  abs(l5 - l4) / (atol + rtol * max(abs(l5), abs(L), 1e-3)))
        if not math.isfinite(err):
            return None
        if err > 1.0:
            h *= max(0.2, 0.9 * err ** -0.25)
            if h < 1e-15 * max(1.0, sig):
                return None
            continue
        while ri < len(radii) and abs(z5) >= radii[ri]:
            lo, hi = 0.0, h
            for _ in range(70):
                mid = 0.5 * (lo + hi)
                zm, _, lm, _ = _steps(rhs, sig, Z, L, mid)
                if abs(zm) >= radii[ri]:
                    hi = mid
                else:
                    lo = mid
            zm, _, lm, _ = _steps(rhs, sig, Z, L, hi)
            out.append(lm + abs(alpha) * s0 - abs(zm))
            ri += 1
            if ri == len(radii):
                sector = int(round(math.atan2(zm.imag, zm.real) * n / (2 * math.pi))) % n
                return out, sector, clear
        for r in others:
            clear = min(clear, abs(Z - r), abs(z5 - r))
        Z, L = z5, l5
        sig += h
        h *= min(5.0, max(0.2, 0.9 * err ** -0.2)) if err > 0 else 5.0
    return None


def hub_alpha(Zc, n, j):
    A2 = float(n) / 2.0
    for k, z in enumerate(Zc):
        if k != j:
            A2 *= (Zc[j] - z)
    if abs(A2) < 1e-11:
        return None
    return cmath.sqrt(1.0 / A2)


def inner_A(Zc_in, M=60.0, rtol=1e-12, atol=1e-14):
    """A_j for every hub, plus escape sectors and geometric clearances."""
    Zc = normalise(list(Zc_in))
    if Zc is None:
        return None
    n = len(Zc) + 1
    radii = (0.5 * M, M)
    A, secs, clears = [], [], []
    for j in range(len(Zc)):
        alpha = hub_alpha(Zc, n, j)
        if alpha is None:
            return None
        arms = []
        for sg in (1.0, -1.0):
            got = trace_arm(Zc, n, Zc[j], sg * alpha, radii, rtol, atol)
            if got is None:
                return None
            arms.append(got)
        if arms[0][1] == arms[1][1]:
            return None                      # both arms reach the same root
        A.append(sum(e[1] + (e[1] - e[0]) / 7.0 for e, _, _ in arms))
        secs.append((arms[0][1], arms[1][1]))
        clears.append(min(arms[0][2], arms[1][2]))
    return A, secs, clears


# --------------------------------------------------------------------------
# the actual polynomial
# --------------------------------------------------------------------------

def _circle3(a, b, c):
    ax, ay, bx, by, cx, cy = a.real, a.imag, b.real, b.imag, c.real, c.imag
    d = 2 * (ax * (by - cy) + bx * (cy - ay) + cx * (ay - by))
    if abs(d) < 1e-300:
        return None
    ux = ((ax * ax + ay * ay) * (by - cy) + (bx * bx + by * by) * (cy - ay)
          + (cx * cx + cy * cy) * (ay - by)) / d
    uy = ((ax * ax + ay * ay) * (cx - bx) + (bx * bx + by * by) * (ax - cx)
          + (cx * cx + cy * cy) * (bx - ax)) / d
    o = complex(ux, uy)
    return o, abs(o - a)


def min_enclosing_circle(points):
    pts = [complex(p) for p in points]
    best = None
    for a, b in itertools.combinations(pts, 2):
        o, r = (a + b) / 2, abs(a - b) / 2
        if all(abs(p - o) <= r + 1e-12 for p in pts) and (best is None or r < best[1]):
            best = (o, r)
    for a, b, c in itertools.combinations(pts, 3):
        got = _circle3(a, b, c)
        if got is None:
            continue
        o, r = got
        if all(abs(p - o) <= r + 1e-12 for p in pts) and (best is None or r < best[1]):
            best = (o, r)
    return best


def build_poly(Z, n, cval, rho, dps=80):
    """f' = n prod (z - rho Z_j), f(0) = -c^n, at `dps` digits."""
    import mpmath as mp
    with mp.workdps(dps):
        cq, rq = mp.mpf(cval), mp.mpf(rho)
        dc = [mp.mpc(1)]
        for z in Z:
            zj = mp.mpc(z.real, z.imag)
            nc = [mp.mpc(0)] * (len(dc) + 1)
            for i, ci in enumerate(dc):
                nc[i] += ci
                nc[i + 1] -= ci * (rq * zj)
            dc = nc
        dc = [n * x for x in dc]
        co = [dc[i] / (n - i) for i in range(n)] + [-cq ** n]
        roots = mp.polyroots(co, maxsteps=600, extraprec=2000)
        crit = mp.polyroots(dc, maxsteps=600, extraprec=2000)
    return ([complex(x) for x in co], [complex(x) for x in crit],
            [complex(x) for x in roots])


def outer_arm(co, c, v, alpha, u0=1e-13, rtol=1e-13, atol=1e-17, hmax=2e-2,
              nsamp=6000):
    """One descending branch f = v(1-u^2), u from u0 to 1.  Returns (length,
    endpoint, chord sum of a sampled path).  A chord sum ABOVE the reported
    length proves the continuation hopped sheets."""
    d_np = np.polyder(np.array(co, dtype=complex))

    def rhs(u, Z):
        d = complex(np.polyval(d_np, Z))
        if abs(d) < 1e-300:
            return 0j, 0.0
        dz = (-2.0 * v * u) / d
        return dz, abs(dz)

    Z = c + alpha * u0
    L, u = 0.0, u0
    h = 1e-14
    pts = [c, Z]
    steps = 0
    while u < 1.0 and steps < 4000000:
        steps += 1
        h = min(h, 1.0 - u, max(1e-14, hmax * u))
        z5, z4, l5, l4 = _steps(rhs, u, Z, L, h)
        err = max(abs(z5 - z4) / (atol + rtol * max(abs(z5), abs(Z))),
                  abs(l5 - l4) / (atol + rtol * max(abs(l5), abs(L), 1e-3)))
        if not math.isfinite(err):
            return None
        if err > 1.0:
            h *= max(0.2, 0.9 * err ** -0.25)
            if h < 1e-18:
                return None
            continue
        Z, L = z5, l5
        u += h
        if len(pts) < nsamp:
            pts.append(Z)
        h *= min(5.0, max(0.2, 0.9 * err ** -0.2)) if err > 0 else 5.0
    if u < 1.0 - 1e-12:
        return None
    chord = sum(abs(pts[i + 1] - pts[i]) for i in range(len(pts) - 1))
    return L + abs(alpha) * u0, Z, chord


def outer_row(Z, n, cval, rho, dps=80):
    co, crit, roots = build_poly(Z, n, cval, rho, dps)
    dd = np.polyder(np.polyder(np.array(co, dtype=complex)))
    rows = []
    for c in crit:
        v = complex(np.polyval(np.array(co, dtype=complex), c))
        if abs(v) >= 1.0:
            rows.append({"admissible": False, "absv": abs(v)})
            continue
        A2 = complex(np.polyval(dd, c)) / 2.0
        alpha = cmath.sqrt(-v / A2)
        arms = []
        for sg in (1.0, -1.0):
            got = outer_arm(co, c, v, sg * alpha)
            if got is None:
                return None
            L, end, chord = got
            k = int(np.argmin([abs(end - z) for z in roots]))
            arms.append((L, chord, k, abs(end - roots[k])))
        if arms[0][2] == arms[1][2]:
            return None
        rows.append({"admissible": True, "absv": abs(v),
                     "L": arms[0][0] + arms[1][0],
                     "chord": arms[0][1] + arms[1][1],
                     "pair": (arms[0][2], arms[1][2]),
                     "dist": max(arms[0][3], arms[1][3])})
    good = [r for r in rows if r["admissible"]]
    if len(good) < n - 1:
        return None
    o, _ = min_enclosing_circle(roots)
    Rup = max(abs(z - o) for z in roots)
    return {"rho": rho, "c": cval, "max_abs_root": max(abs(z) for z in roots),
            "R_upper": Rup, "minL": min(r["L"] for r in good),
            "minL_minus_2R": min(r["L"] for r in good) - 2 * Rup,
            "over_rho": (min(r["L"] for r in good) - 2 * Rup) / rho,
            "max_abs_f_at_hub": max(r["absv"] for r in good),
            "max_endpoint_dist": max(r["dist"] for r in good),
            "chord_sum_ok": all(r["chord"] <= r["L"] + 1e-10 for r in good),
            "distinct_pairs": all(len(set(r["pair"])) == 2 for r in good),
            "roots": roots, "co": co, "crit": crit}


# --------------------------------------------------------------------------
# parts
# --------------------------------------------------------------------------

def part_wall(rep):
    """On the wall the ambiguous hub's arm ends at a critical point, so L(c) is
    not a branch pair.  Its two continuations, one per outgoing arm of the hub
    it runs into, are computed by surgery and by two-sided limits."""
    Z = normalise([complex(a, b) for a, b in WALL_SPECIMEN])
    n = 5
    j, i = WALL_AMBIGUOUS
    Q = qpoly(Z)
    V = crit_values(Z)
    sstar = (V[i] - V[j]).real
    sep, gap, scale = wall_report(Z)
    got = inner_A(Z, M=300.0)
    A_onwall = got[0] if got else None
    dQ = _dQ(Z, n)

    # --- surgery: Newton continuation along Q = V_j + tau to the saddle
    alpha_j = hub_alpha(Z, n, j)
    arcs = {}
    for sg in (1.0, -1.0):
        m = 40000
        u = np.linspace(0.0, 1.0, m + 1)
        tau = sstar * (0.5 - 0.5 * np.cos(math.pi * u))
        Zp = Z[j] + sg * alpha_j * math.sqrt(max(float(tau[1]), 0.0))
        pts = [Z[j]]
        ok = True
        for t in tau[1:]:
            target = V[j] + float(t)
            for _ in range(60):
                d = dQ(Zp)
                if abs(d) < 1e-300:
                    ok = False
                    break
                step = (Q(Zp) - target) / d
                Zp = Zp - step
                if abs(step) < 1e-15 * max(1.0, abs(Zp)):
                    break
            if not ok:
                break
            pts.append(Zp)
        if ok:
            arcs[sg] = (sum(abs(pts[k + 1] - pts[k]) for k in range(len(pts) - 1)),
                        abs(pts[-1] - Z[i]))
    if len(arcs) != 2:
        rep["wall"] = {"error": "surgery failed"}
        return False
    sg_in = min(arcs, key=lambda s: arcs[s][1])
    Lin = arcs[sg_in][0]
    got_free = trace_arm(Z, n, Z[j], -sg_in * alpha_j, (150.0, 300.0), 1e-13, 1e-15)
    exc_free = got_free[0][1] + (got_free[0][1] - got_free[0][0]) / 7.0
    alpha_i = hub_alpha(Z, n, i)
    conts = []
    for sg in (1.0, -1.0):
        g2 = trace_arm(Z, n, Z[i], sg * alpha_i, (150.0, 300.0), 1e-13, 1e-15)
        e = g2[0][1] + (g2[0][1] - g2[0][0]) / 7.0
        conts.append(exc_free + Lin + e)
    conts.sort()

    ok = (gap < 1e-10 and arcs[sg_in][1] < 1e-4
          and abs(conts[0] - min(WALL_CONTINUATIONS)) < 2e-4
          and abs(conts[1] - max(WALL_CONTINUATIONS)) < 2e-4
          and conts[0] < 0.0 < conts[1])
    rep["wall"] = {
        "rel_im_gap": gap, "hub_separation": sep, "s_star": sstar,
        "arrival_distance": arcs[sg_in][1],
        "A_on_wall_as_traced": A_onwall,
        "continuations": conts, "recorded": sorted(WALL_CONTINUATIONS),
        "lower_continuation_negative": conts[0] < 0.0,
        "reading_that_survives_on_the_wall": "lower continuation",
        "ok": bool(ok),
    }
    return bool(ok)


def part_guarded(rep):
    """Recorded wall-guarded maximisers reproduce, and pass the guard."""
    rows = {}
    ok = True
    for key, rec in GUARDED.items():
        Z = normalise([complex(a, b) for a, b in rec["Z"]])
        n = rec["n"]
        sep, gap, scale = wall_report(Z)
        vals = {}
        for M in (60.0, 300.0):
            for rtol in (1e-11, 1e-13):
                got = inner_A(Z, M=M, rtol=rtol, atol=1e-15)
                if got is None:
                    vals["M%g_r%g" % (M, rtol)] = None
                    ok = False
                    continue
                vals["M%g_r%g" % (M, rtol)] = min(got[0])
        got = inner_A(Z, M=300.0, rtol=1e-13, atol=1e-15)
        A, secs, clears = got
        spread = max(vals.values()) - min(vals.values())
        row = {
            "n": n, "guard_g": rec["g"], "A": A, "minA": min(A),
            "recorded_minA": rec["minA"], "reproduces": abs(min(A) - rec["minA"]) < rec["tol"],
            "instrument_spread_over_M_and_rtol": spread,
            "hub_separation": sep, "rel_im_gap": gap,
            "value_plane_guard_passes": gap >= rec["g"],
            "collision_guard_passes": sep >= 1e-3,
            "geometric_arm_clearance": min(clears), "clearances": clears,
            "sectors": secs,
            "sectors_distinct_at_every_hub": all(a != b for a, b in secs),
            "min_A_is_positive": min(A) > 0.0,
        }
        ok = ok and row["reproduces"] and row["value_plane_guard_passes"] \
            and row["collision_guard_passes"] and row["sectors_distinct_at_every_hub"] \
            and row["min_A_is_positive"] and spread < 1e-7
        rows[key] = row
    rep["guarded"] = rows
    return ok


def part_refute(rep):
    """The guarded maximisers carried to actual polynomials, degrees five and
    six."""
    ok = True
    by_case = {}
    for key, case in REFUTE_CASES.items():
        rec = GUARDED[key]
        Z = normalise([complex(a, b) for a, b in rec["Z"]])
        n = rec["n"]
        rows = []
        for rho, expect in zip(case["rhos"], case["over_rho"]):
            r = outer_row(Z, n, 0.9, rho)
            if r is None:
                rows.append({"rho": rho, "error": "trace failed"})
                ok = False
                continue
            row = {k: r[k] for k in ("rho", "max_abs_root", "R_upper", "minL",
                                     "minL_minus_2R", "over_rho", "max_abs_f_at_hub",
                                     "max_endpoint_dist", "chord_sum_ok",
                                     "distinct_pairs")}
            row["expected_over_rho"] = expect
            row["refutes_MIN"] = r["minL"] > 2 * r["R_upper"]
            row["roots_strictly_inside"] = r["max_abs_root"] < 1.0
            ok = ok and row["refutes_MIN"] and row["roots_strictly_inside"] \
                and row["chord_sum_ok"] and row["distinct_pairs"] \
                and abs(row["over_rho"] - expect) < 1e-6
            rows.append(row)
        o = [r["over_rho"] for r in rows if "over_rho" in r]
        rich = 2 * o[-1] - o[-2] if len(o) >= 2 else None
        matches = rich is not None and abs(rich - rec["minA"]) < 5e-5
        ok = ok and matches
        by_case[key] = {"n": n, "inner_prediction": rec["minA"], "cases": rows,
                        "richardson_over_rho": rich,
                        "richardson_matches_inner": matches}
    rec = GUARDED["n5_g1em4"]
    Z = normalise([complex(a, b) for a, b in rec["Z"]])
    n = rec["n"]
    rows = by_case["n5_g1em4"]["cases"]
    rich = by_case["n5_g1em4"]["richardson_over_rho"]
    # launch-point stability: |alpha| u0 must be far below the critical-point
    # separation, and the answer must not move when u0 and the step cap do
    co, crit, roots = build_poly(Z, n, 0.9, 0.005)
    dd = np.polyder(np.polyder(np.array(co, dtype=complex)))
    launch = {}
    for u0 in (1e-11, 1e-15):
        for hmax in (2e-2, 5e-3):
            Ls = []
            for c in crit:
                v = complex(np.polyval(np.array(co, dtype=complex), c))
                A2 = complex(np.polyval(dd, c)) / 2.0
                alpha = cmath.sqrt(-v / A2)
                tot = 0.0
                for sg in (1.0, -1.0):
                    got = outer_arm(co, c, v, sg * alpha, u0=u0, hmax=hmax)
                    if got is None:
                        tot = None
                        break
                    tot += got[0]
                if tot is None:
                    break
                Ls.append(tot)
            launch["u0=%g,hmax=%g" % (u0, hmax)] = min(Ls) if Ls else None
    vals = [v for v in launch.values() if v is not None]
    launch_spread = (max(vals) - min(vals)) if len(vals) == 4 else None
    ok = ok and launch_spread is not None and launch_spread < 1e-11
    rep["refute"] = {"by_case": by_case,
                     "launch_point_minL_n5_rho0.005": launch,
                     "launch_point_spread": launch_spread,
                     "ok": bool(ok)}
    return bool(ok)


def _seg_max_abs_f(co, a, b, N=20001):
    ts = np.linspace(0.0, 1.0, N)
    P = a + (b - a) * ts
    return float(np.abs(np.polyval(np.array(co, dtype=complex), P)).max())


def part_shell(rep):
    """c -> 1: an actual quintic whose every branch pair exceeds length 2,
    while the origin's two shortest straight spokes are contained, total < 2."""
    rec = GUARDED["n5_g1em4"]
    Z = normalise([complex(a, b) for a, b in rec["Z"]])
    n = rec["n"]
    r = outer_row(Z, n, SHELL["c"], SHELL["rho"], dps=120)
    if r is None:
        rep["shell"] = {"error": "trace failed"}
        return False
    co, roots = r["co"], r["roots"]
    spokes = sorted((_seg_max_abs_f(co, 0j, z), abs(z)) for z in roots)
    contained = [s for s in spokes if s[0] < 1.0]
    two = sum(s[1] for s in contained[:2]) if len(contained) >= 2 else None
    chords = []
    for i in range(n):
        for j in range(i + 1, n):
            chords.append((_seg_max_abs_f(co, roots[i], roots[j]),
                           abs(roots[i] - roots[j])))
    # exact-shaped certificate for the origin spokes: with f = z^n + sum_{j<n}
    # p_j z^j and f(a) = 0,  f(ta) = p_0 (1 - t^n) + sum_{j>=1} p_j (t^j - t^n) a^j,
    # so |a| <= 1 and sum_{j=0}^{n-1} |p_j| <= 1 force |f| <= 1 on every origin
    # spoke.  This is the coefficient-sum corollary of BernsteinOriginSpokeCertificate
    # Theorem C, and it is a pure inequality on the exhibited coefficients.
    coeff_sum = sum(abs(a) for a in co[1:])
    ok = (r["max_abs_root"] < 1.0 and r["minL"] > 2.0 and r["chord_sum_ok"]
          and r["distinct_pairs"] and two is not None and two < 2.0
          and all(c[0] >= 1.0 for c in chords) and coeff_sum < 1.0)
    rep["shell"] = {
        "c": SHELL["c"], "rho": SHELL["rho"],
        "max_abs_root": r["max_abs_root"], "roots_strictly_inside": r["max_abs_root"] < 1.0,
        "max_abs_f_at_hub": r["max_abs_f_at_hub"],
        "min_branch_pair_length": r["minL"], "exceeds_two": r["minL"] > 2.0,
        "minL_minus_two": r["minL"] - 2.0,
        "chord_sum_ok": r["chord_sum_ok"], "distinct_pairs": r["distinct_pairs"],
        "contained_origin_spokes": len(contained),
        "origin_two_shortest_spokes": two,
        "origin_hub_beats_two": two is not None and two < 2.0,
        "contained_root_chords": sum(1 for c in chords if c[0] < 1.0),
        "min_max_abs_f_over_root_chords": min(c[0] for c in chords),
        "coefficient_sum_certificate": coeff_sum,
        "coefficient_sum_below_one": coeff_sum < 1.0,
        "ok": bool(ok),
    }
    return bool(ok)


def part_selectors(rep):
    """Three hub selectors that would each imply (MIN-inner) are refuted."""
    # deterministic guarded samples: a fixed lattice of configurations
    samples = []
    for a in (-0.9, -0.4, 0.2, 0.7):
        for b in (-0.6, -0.1, 0.35, 0.8):
            for c in (-0.5, 0.25):
                Z = normalise([complex(a, b), complex(c, -0.3), complex(-0.2, 0.55)])
                if Z is None:
                    continue
                sep, gap, sc = wall_report(Z)
                if sep < 1e-3 or gap < 1e-3:
                    continue
                got = inner_A(Z, M=40.0, rtol=1e-11, atol=1e-13)
                if got is None:
                    continue
                A, secs, clears = got
                if min(clears) < 1e-2:
                    continue
                samples.append((Z, A))
    V_sel, out_sel, in_sel = [], [], []
    for Z, A in samples:
        mods = [abs(z) for z in Z]
        V = crit_values(Z)
        out_sel.append(A[int(np.argmax(mods))])
        in_sel.append(A[int(np.argmin(mods))])
        V_sel.append(A[int(np.argmax([v.real for v in V]))])
    rec = GUARDED["n5_g1em4"]
    Zr = normalise([complex(a, b) for a, b in rec["Z"]])
    Ar = inner_A(Zr, M=300.0, rtol=1e-13, atol=1e-15)[0]
    ok = (len(samples) >= 8 and max(out_sel) > 0 and max(in_sel) > 0
          and max(V_sel) > 0 and min(Ar) > 0)
    rep["selectors"] = {
        "guarded_samples": len(samples),
        "outermost_hub_max_A": max(out_sel) if out_sel else None,
        "innermost_hub_max_A": max(in_sel) if in_sel else None,
        "largest_Re_V_hub_max_A": max(V_sel) if V_sel else None,
        "outermost_hub_selector_refuted": max(out_sel) > 0 if out_sel else None,
        "innermost_hub_selector_refuted": max(in_sel) > 0 if in_sel else None,
        "largest_Re_V_selector_refuted": max(V_sel) > 0 if V_sel else None,
        "every_hub_positive_at_the_guarded_maximiser": min(Ar) > 0,
        "ok": bool(ok),
    }
    return bool(ok)


PARTS = {"wall": part_wall, "guarded": part_guarded, "refute": part_refute,
         "shell": part_shell, "selectors": part_selectors}


def main() -> int:
    ap = argparse.ArgumentParser()
    ap.add_argument("--part", choices=sorted(PARTS) + ["all"], default="all")
    ap.add_argument("--verbose", action="store_true")
    args = ap.parse_args()
    rep: dict = {}
    todo = sorted(PARTS) if args.part == "all" else [args.part]
    ok = True
    for name in todo:
        ok = PARTS[name](rep) and ok
    payload = {
        "check": "erdos1041_guarded_inner_model",
        "status": "pass" if ok else "fail",
        "evidence_class": "finite_computational_evidence",
        "claim": ("(MIN-inner) min_j A_j <= 0 is FALSE at degrees five and six "
                  "at wall-guarded configurations; on the saddle-connection "
                  "wall itself it survives in the lower-continuation reading; "
                  "Erdos 1041 is NOT refuted"),
        "parts": todo,
        "report": rep if args.verbose else {
            k: (v if not isinstance(v, dict) else
                {kk: vv for kk, vv in v.items() if kk != "roots"})
            for k, v in rep.items()},
    }
    print(json.dumps(payload, default=lambda o: (
        [o.real, o.imag] if isinstance(o, complex) else str(o))))
    return 0


if __name__ == "__main__":
    sys.exit(main())
