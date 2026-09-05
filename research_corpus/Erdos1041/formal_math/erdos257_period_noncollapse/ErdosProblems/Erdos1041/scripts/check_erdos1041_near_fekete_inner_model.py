#!/usr/bin/env python3
"""Erdos #1041: deterministic verifier for NearFeketeInnerModelWidening.md.

The note says that the near-Fekete cusp is governed by an inner model whose
free object is an ARBITRARY monic degree-n polynomial Q with sum of critical
points zero, and that NearFeketeCuspLaw.md's one-angle regular-gon family is a
proper slice of it for every n >= 4.  This script tests the five statements the
note actually rests on.

  slice    the inner model reproduces the corpus constants kappa_n at
           n = 3..6 to six digits, so the widened model contains the slice.
  entry73  the inner model reproduces the recorded charge of the blown-up
           saddle-wall quartic (negative_results entry 73) to 1e-8, so that
           family is a point of the widened model.
  e2e      the inner reduction is correct at n = 3 end to end: the residual
           (min_c L(c)/(2R) - 1 - rho*Phi/(2R)) / rho^2 converges to -0.25.
  chord    the pairing-free chord form of the |f(c)|^s weighted mean is at
           most 1, and the pairing-fixed exact rational certificates are
           re-derived in Fraction arithmetic with certified critical-point
           enclosures.
  climb    the recorded near-maximisers of the widened model reproduce their
           audited min_j A_j at two independent tracing radii.

Arithmetic.  Branch tracing is an adaptive Cash-Karp RK45 written out here in
float64, because the corpus's pinned checkers may not import scipy; the
integrator is calibrated in the `slice` part against the recorded constants,
and every reported length is recomputed at two tracing radii which must agree.
Arc length is carried as an INTEGRATED ODE STATE, never as a chord sum, per the
method warning in negative_results entry 73.  The chord certificates are EXACT:
Fraction arithmetic throughout, Kantorovich-certified critical-point discs, and
a rational upper bound for the circumradius.  No random number generator is
used, so a failure is reproducible.
"""

from __future__ import annotations

import argparse
import itertools
import json
import math
import sys
from fractions import Fraction as F

import numpy as np

# --------------------------------------------------------------------------
# recorded values under test
# --------------------------------------------------------------------------

# NearFeketeCuspLaw.md section 6, "kappa_n from g"
KAPPA = {3: 0.6080213113, 4: 1.030119661, 5: 1.258578348, 6: 1.398912406}

# negative_results entry 73 (0-indexed 72), the blown-up saddle-wall quartic
E73 = {"a": 1.0, "b": 0.4, "rho": 1.0 / 50.0, "delta": 1e-6, "s": 0.99989,
       "sum_L": 6.000253120901, "six_R": 5.999939963992,
       "min_L": 1.995615925599, "two_R": 1.999979987997}

# widened-model near-maximisers found by the w2b climb (critical points Z_j,
# sum 0, max |Z_j| = 1).  These are RECORDED SEARCH OUTPUT, not extremals.
REFUTER = {
 "n": 5,
 "Zc": [[-0.48805079116945244, -0.0003542519331306829], [-0.4971815689676606, -0.01556459260195624], [0.9999957080391201, 0.002929829916397283], [-0.014763347902007076, 0.012989014618689643]],
 "Phi": 0.0227238526,
 "cases": [[0.9, 0.01], [0.9, 0.005], [0.95, 0.01], [0.8, 0.01]],
 "recorded_minL": 1.800182484803,
 "recorded_twoR": 1.800034190066
}

CLIMB = {
 "n5_widened_maximiser_positive": {
  "Zc": [[-0.48805079116945244, -0.0003542519331306829], [-0.4971815689676606, -0.01556459260195624], [0.9999957080391201, 0.002929829916397283], [-0.014763347902007076, 0.012989014618689643]],
  "Phi": 0.0227238526,
  "min_gap": 0.017740506375579574
 },
 "n4_degenerate_b1e-6": {
  "Zc": [
   [
    -0.9999999999995,
    0.0
   ],
   [
    0.0,
    9.999999999995e-07
   ],
   [
    0.9999999999995,
    -9.999999999995e-07
   ]
  ],
  "Phi": -0.002074239750466389,
  "min_gap": 0.9999999999999999
 },
 "n5_sweep_argmax": {
  "Zc": [
   [
    -0.591841548436852,
    -0.0027892170763896772
   ],
   [
    -0.5959496620155056,
    -0.016988356527826105
   ],
   [
    0.9999882521296113,
    0.004847226296025347
   ],
   [
    0.18780295832274646,
    0.014930347308190439
   ]
  ],
  "Phi": -0.28734321107641647,
  "min_gap": 0.014781480248488526
 },
 "n6_sweep_argmax": {
  "Zc": [
   [
    -0.20661912569430282,
    0.01016881997047584
   ],
   [
    0.0004515395845444024,
    0.002451682365962563
   ],
   [
    -0.5943088367782096,
    0.0009666539922587341
   ],
   [
    0.999988106508019,
    -0.004877175669065657
   ],
   [
    -0.19951168362005095,
    -0.00870998065963148
   ]
  ],
  "Phi": -0.41614416871082327,
  "min_gap": 0.02017237829484135
 }
}


# --------------------------------------------------------------------------
# adaptive Cash-Karp RK45 on a real state vector
# --------------------------------------------------------------------------

_CK_A = [[], [1 / 5], [3 / 40, 9 / 40], [3 / 10, -9 / 10, 6 / 5],
         [-11 / 54, 5 / 2, -70 / 27, 35 / 27],
         [1631 / 55296, 175 / 512, 575 / 13824, 44275 / 110592, 253 / 4096]]
_CK_C = [0, 1 / 5, 3 / 10, 3 / 5, 1, 7 / 8]
_CK_B5 = [37 / 378, 0, 250 / 621, 125 / 594, 0, 512 / 1771]
_CK_B4 = [2825 / 27648, 0, 18575 / 48384, 13525 / 55296, 277 / 14336, 1 / 4]


def _rk45(rhs, t0, t1, y0, rtol, atol, stop=None, hmax=None, maxsteps=400000):
    """Integrate y' = rhs(t, y) from t0 to t1.  If `stop` is given it is a
    scalar function of (t, y); integration terminates at its first zero
    crossing from negative to positive, located by bisection on the step."""
    y = np.array(y0, dtype=float)
    t = float(t0)
    h = min((t1 - t0) / 1000.0,
            (hmax(t0) if callable(hmax) else (hmax if hmax else (t1 - t0))))
    if hmax is None:
        hmax = (t1 - t0)
    n = 0
    while t < t1 and n < maxsteps:
        n += 1
        hcap = hmax(t) if callable(hmax) else hmax
        h = min(h, t1 - t, hcap)
        k = []
        for i in range(6):
            yy = y.copy()
            for j, a in enumerate(_CK_A[i]):
                yy = yy + h * a * k[j]
            k.append(np.asarray(rhs(t + _CK_C[i] * h, yy), dtype=float))
        y5 = y + h * sum(b * kk for b, kk in zip(_CK_B5, k))
        y4 = y + h * sum(b * kk for b, kk in zip(_CK_B4, k))
        err = np.max(np.abs(y5 - y4) / (atol + rtol * np.maximum(np.abs(y5), np.abs(y))))
        if not np.isfinite(err):
            return None
        if err > 1.0:
            h *= max(0.2, 0.9 * err ** -0.25)
            continue
        tn = t + h
        if stop is not None and stop(tn, y5) > 0.0:
            lo, hi = t, tn
            ylo = y
            for _ in range(80):
                mid = 0.5 * (lo + hi)
                hh = mid - lo
                kk = []
                for i in range(6):
                    yy = ylo.copy()
                    for j, a in enumerate(_CK_A[i]):
                        yy = yy + hh * a * kk[j]
                    kk.append(np.asarray(rhs(mid + 0.0, yy), dtype=float))
                ym = ylo + hh * sum(b * q for b, q in zip(_CK_B5, kk))
                if stop(mid, ym) > 0.0:
                    hi = mid
                else:
                    lo, ylo = mid, ym
            return lo, ylo, True
        t, y = tn, y5
        h *= min(5.0, 0.9 * err ** -0.2) if err > 0 else 5.0
    return t, y, False


# --------------------------------------------------------------------------
# the inner model:  Q' = n prod (Z - Z_j),  arms are lifts of Q = Q(Z_j) + tau
# --------------------------------------------------------------------------

def inner_A(Zc_in, M=60.0, rtol=1e-12, atol=1e-14):
    """A_j = -2|Z_j| + int over both arms of (1 - cos chi) ds, for every hub.
    Returns None if any arm stalls on a tie or the two arms of a hub escape in
    the same asymptotic sector (they would reach the same root)."""
    Zc = np.asarray(Zc_in, dtype=complex)
    Zc = Zc - Zc.mean()
    sc = np.abs(Zc).max()
    if sc < 1e-12:
        return None
    Zc = Zc / sc
    n = len(Zc) + 1
    dQ = float(n) * np.poly(Zc)
    Q = np.polyint(dQ)
    ddQ = np.polyder(dQ)
    out = []
    for c in Zc:
        A2 = np.polyval(ddQ, c) / 2.0
        if abs(A2) < 1e-11:
            return None
        alpha = np.sqrt(complex(1.0 / A2))
        arms = []
        for sg in (+1.0, -1.0):
            got = _arm_inner(dQ, complex(c), sg * alpha, n, M, rtol, atol)
            if got is None:
                return None
            arms.append(got)
        if arms[0][2] == arms[1][2]:
            return None
        out.append(arms[0][0] + arms[1][0])
    return out


def _arm_inner(dQ, c, alpha, n, M, rtol, atol):
    def rhs(sig, y):
        Z = complex(y[0], y[1])
        d = np.polyval(dQ, Z)
        if abs(d) < 1e-25:
            return [0.0, 0.0, 0.0]
        dZ = 2.0 * sig / d
        return [dZ.real, dZ.imag, abs(dZ)]

    s0 = 1e-9
    start = c + alpha * s0
    y0 = [start.real, start.imag, 0.0]
    exc = []
    tcur, ycur = s0, np.array(y0, dtype=float)
    for target in (0.5 * M, M):
        got = _rk45(rhs, tcur, 4.0 * M ** (n / 2.0), ycur, rtol, atol,
                    stop=lambda t, y, tt=target: y[0] * y[0] + y[1] * y[1] - tt * tt)
        if got is None or not got[2]:
            return None
        tcur, ycur = got[0], got[1]
        Z = complex(ycur[0], ycur[1])
        exc.append(float(ycur[2]) + abs(alpha) * s0 - abs(Z))
    a = exc[1] + (exc[1] - exc[0]) / 7.0        # Richardson in 1/|Z|^3
    Zend = complex(ycur[0], ycur[1])
    sector = int(round(math.atan2(Zend.imag, Zend.real) * n / (2 * math.pi))) % n
    return a, exc[1], sector


# --------------------------------------------------------------------------
# the outer object: descending branches of an actual polynomial
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
    """Exact over pairs and triples.  An iterative centre INFLATES R, and R
    sits in the denominator of the obligation."""
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


def branch_lengths(roots, rtol=1e-13, atol=1e-16, u0=1e-10, hmax=2e-4):
    """For every critical point c with |f(c)| < 1, the two descending branches
    f(z) = f(c)(1 - u^2), traced to u = 1 with arc length as an ODE state."""
    roots = [complex(z) for z in roots]
    co = np.poly(roots)
    d_np = np.polyder(co)
    crit = np.roots(d_np)
    dd = np.polyder(d_np)
    rows = []
    for c in crit:
        v = complex(np.polyval(co, c))
        if abs(v) >= 1.0:
            rows.append({"c": c, "absv": abs(v), "admissible": False})
            continue
        A2 = np.polyval(dd, c) / 2.0
        if abs(A2) < 1e-13:
            return None
        alpha = np.sqrt(complex(-v / A2))
        arms = []
        for sg in (+1.0, -1.0):
            got = _arm_outer(d_np, c, v, sg * alpha, rtol, atol, u0, hmax)
            if got is None:
                return None
            L, end = got
            k = int(np.argmin([abs(end - z) for z in roots]))
            arms.append({"L": L, "end": end, "root": k, "dist": abs(end - roots[k])})
        if arms[0]["root"] == arms[1]["root"]:
            return None
        rows.append({"c": c, "absv": abs(v), "admissible": True,
                     "L": arms[0]["L"] + arms[1]["L"],
                     "pair": (arms[0]["root"], arms[1]["root"]),
                     "maxdist": max(a["dist"] for a in arms)})
    return rows


def branch_lengths_exact(co_np, crit, roots, rtol=1e-13, atol=1e-16, u0=1e-12,
                        hmax=2e-2):
    """Descending branch lengths from EXACT data.

    co_np, crit and roots must come from the polynomial's own coefficients at
    high precision.  Rebuilding f from float64 roots destroys a_1, which is of
    order rho^{n-1} against a_0 of order one, and that moves the critical-point
    cluster enough to flip a measured sign; and the launch point c + alpha*u0
    is only on the branch while |alpha| u0 is far below the distance from c to
    the next critical point, with |alpha| = sqrt(|v| / |A_2|) enormous inside a
    tight cluster.  Both are why this takes exact input and a tiny u0.
    """
    d_np = np.polyder(co_np)
    dd = np.polyder(d_np)
    out = []
    for c in crit:
        v = complex(np.polyval(co_np, c))
        if abs(v) >= 1.0:
            out.append({"c": c, "absv": abs(v), "admissible": False})
            continue
        A2 = np.polyval(dd, c) / 2.0
        if A2 == 0:
            return None
        alpha = np.sqrt(complex(-v / A2))
        arms = []
        for sg in (+1.0, -1.0):
            got = _arm_outer(d_np, c, v, sg * alpha, rtol, atol, u0, hmax)
            if got is None:
                return None
            L, end = got
            k = int(np.argmin([abs(end - z) for z in roots]))
            arms.append({"L": L, "root": k, "dist": abs(end - roots[k])})
        if arms[0]["root"] == arms[1]["root"]:
            return None
        out.append({"c": c, "absv": abs(v), "admissible": True,
                    "L": arms[0]["L"] + arms[1]["L"],
                    "pair": (arms[0]["root"], arms[1]["root"]),
                    "maxdist": max(a["dist"] for a in arms)})
    return out


def _arm_outer(d_np, c, v, alpha, rtol, atol, u0, hmax=2e-4):
    def rhs(u, y):
        z = complex(y[0], y[1])
        d = np.polyval(d_np, z)
        if abs(d) < 1e-25:
            return [0.0, 0.0, 0.0]
        dz = -2.0 * v * u / d
        return [dz.real, dz.imag, abs(dz)]

    start = c + alpha * u0
    # near the hub z - c is about alpha*u with |alpha| large when the hub sits
    # in a tight critical cluster, so the step cap must shrink with u or the
    # first step crosses the whole cluster and the branch lands on a wrong sheet
    got = _rk45(rhs, u0, 1.0, [start.real, start.imag, 0.0], rtol, atol,
                hmax=lambda u: max(1e-13, hmax * u), maxsteps=4000000)
    if got is None:
        return None
    t, y, _ = got
    if t < 1.0 - 1e-9:
        return None
    return float(y[2]) + abs(alpha) * u0, complex(y[0], y[1])


# --------------------------------------------------------------------------
# exact rational machinery for the chord certificates
# --------------------------------------------------------------------------

def _fsqrt_lo(x: F, k: int = 60) -> F:
    """Rational L with L*L <= x and L close to sqrt(x)."""
    if x <= 0:
        return F(0)
    num = math.isqrt(x.numerator * 10 ** (2 * k) // x.denominator)
    return F(num, 10 ** k)


def _fsqrt_hi(x: F, k: int = 60) -> F:
    lo = _fsqrt_lo(x, k)
    hi = lo + F(1, 10 ** k)
    while hi * hi < x:
        hi += F(1, 10 ** k)
    return hi


class G:
    """Gaussian rational."""
    __slots__ = ("re", "im")

    def __init__(self, re, im=F(0)):
        self.re, self.im = F(re), F(im)

    def __add__(self, o): return G(self.re + o.re, self.im + o.im)
    def __sub__(self, o): return G(self.re - o.re, self.im - o.im)
    def __mul__(self, o): return G(self.re * o.re - self.im * o.im,
                                   self.re * o.im + self.im * o.re)
    def n2(self) -> F: return self.re * self.re + self.im * self.im


def _poly_from_roots(rs):
    co = [G(F(1))]
    for r in rs:
        nc = [G(F(0))] * (len(co) + 1)
        for i, ci in enumerate(co):
            nc[i] = nc[i] + ci
            nc[i + 1] = nc[i + 1] - ci * r
        co = nc
    return co


def _polyval(co, z):
    acc = G(F(0))
    for c in co:
        acc = acc * z + c
    return acc


def _polyder(co):
    d = len(co) - 1
    return [G(co[i].re * (d - i), co[i].im * (d - i)) for i in range(d)]


def _sup_abs_on_disc(co, c0: G, r: F) -> F:
    """Rational upper bound for sup_{|z-c0|<=r} |p(z)| from the Taylor shift."""
    sh = _shift(co, c0)
    tot = F(0)
    for i, ci in enumerate(sh):
        k = len(sh) - 1 - i
        tot += _fsqrt_hi(ci.n2()) * r ** k
    return tot


def _shift(co, c0: G):
    out = [G(F(0))] * len(co)
    out[-1] = G(F(1))
    cur = [G(F(1))]
    res = [G(F(0))] * len(co)
    # Horner-style synthetic division repeated: coefficients of p(c0 + w)
    work = list(co)
    n = len(co) - 1
    coeffs = []
    for _ in range(n + 1):
        rem = G(F(0))
        new = []
        for a in work:
            rem = rem * c0 + a
            new.append(rem)
        coeffs.append(rem)
        work = new[:-1]
        if not work:
            break
    coeffs = list(reversed(coeffs))          # highest power of w first
    while len(coeffs) < len(co):
        coeffs.insert(0, G(F(0)))
    return coeffs


def certify_critical_discs(co, approx):
    """Kantorovich: with beta = |g(c0)/g'(c0)| and K = sup|g''| on D(c0,2beta)
    over |g'(c0)|, 2 beta K <= 1 gives a root of g = p' in D(c0, 2 beta)."""
    g = _polyder(co)
    gp = _polyder(g)
    gpp = _polyder(gp)
    discs = []
    for c0 in approx:
        v = _polyval(g, c0)
        dv = _polyval(gp, c0)
        if dv.n2() == 0:
            return None
        beta = _fsqrt_hi(v.n2()) / _fsqrt_lo(dv.n2())
        r = 2 * beta
        K = _sup_abs_on_disc(gpp, c0, r) / _fsqrt_lo(dv.n2())
        if 2 * beta * K > 1:
            return None
        discs.append((c0, r))
    for i in range(len(discs)):
        for j in range(i + 1, len(discs)):
            d2 = (discs[i][0] - discs[j][0]).n2()
            if _fsqrt_lo(d2) <= discs[i][1] + discs[j][1]:
                return None
    return discs


def exact_chord_row(roots_q, crit_pairs, s, centre_q, Rup):
    """Exact refutation arithmetic for one configuration.

    roots_q     Gaussian-rational roots, all strictly inside the unit disc
    crit_pairs  for each ADMISSIBLE critical point, its approximate location
                and the index pair its two descending branches reach.  This
                pairing is the ONE tracer-supplied input; everything below is
                exact rational arithmetic.
    s           even weight exponent, so |f(c)|^s is rational
    Certifies  sum_j w_j (chord_j - 2 Rup) > 0, which forces the |f(c)|^s
    weighted mean of L(c) over admissible critical points to exceed 2R.
    """
    co = _poly_from_roots(roots_q)
    p_np = np.poly([complex(float(r.re), float(r.im)) for r in roots_q])
    approx = [G(F(round(c.real * 10 ** 12), 10 ** 12),
                F(round(c.imag * 10 ** 12), 10 ** 12))
              for c in np.roots(np.polyder(p_np))]
    for r in roots_q:
        if r.n2() >= 1:
            return {"reason": "root_not_certifiably_inside_disc"}
        if _fsqrt_hi((r - centre_q).n2()) > Rup:
            return {"reason": "Rup_not_an_upper_bound"}
    discs = certify_critical_discs(co, approx)
    if discs is None:
        return {"reason": "critical_point_discs_not_certified"}
    dco = _polyder(co)
    total = F(0)
    out = []
    used = 0
    for c0, rad in discs:
        fv = _polyval(co, c0)
        slope = _sup_abs_on_disc(dco, c0, rad)
        flo = _fsqrt_lo(fv.n2()) - slope * rad
        fhi = _fsqrt_hi(fv.n2()) + slope * rad
        if flo < 0:
            flo = F(0)
        if flo > 1:
            continue                       # certifiably inadmissible
        if fhi >= 1:
            return {"reason": "admissibility_undecided_at_a_hub"}
        cf = float(c0.re) + 1j * float(c0.im)
        best = min(crit_pairs, key=lambda q: abs(cf - complex(q["c"][0], q["c"][1])))
        if abs(cf - complex(best["c"][0], best["c"][1])) > 1e-6:
            return {"reason": "admissible_hub_has_no_recorded_pairing"}
        used += 1
        ch = F(0)
        for idx in best["pair"]:
            ch += _fsqrt_lo((c0 - roots_q[idx]).n2()) - rad
        gapl = ch - 2 * Rup
        total += (flo ** s if gapl > 0 else fhi ** s) * gapl
        out.append({"chord_lo": float(ch), "gap_lo": float(gapl),
                    "disc_radius": float(rad)})
    if used != len(crit_pairs):
        return {"reason": "admissible_hub_count_mismatch"}
    return {"exact_sum_sign": (1 if total > 0 else (0 if total == 0 else -1)),
            "exact_sum": float(total), "rows": out, "Rup": float(Rup),
            "hubs": used}


# --------------------------------------------------------------------------
# parts
# --------------------------------------------------------------------------

def part_slice(rep):
    """The one-angle regular-(n-1)-gon slice, read through the widened inner
    model:  max over phi of min_j A_j  =  -min_phi kappa_n.  The angle runs over
    a full period 2 pi / (n-1); angles where an arm stalls on a tie are skipped,
    and the best angle is refined by golden section at a larger tracing radius."""
    ok = True
    out = []
    for n in (3, 4, 5, 6):
        m = n - 1

        def val(phi, M):
            A = inner_A(np.exp(1j * (phi + 2 * np.pi * np.arange(m) / m)), M=M)
            return None if A is None else min(A)

        best_phi, best = None, None
        for k in range(49):
            phi = 2.0 * math.pi * k / (48.0 * m)
            v = val(phi, 30.0)
            if v is not None and (best is None or v > best):
                best, best_phi = v, phi
        step = 2.0 * math.pi / (48.0 * m)
        lo, hi = best_phi - step, best_phi + step
        gr = (math.sqrt(5.0) - 1.0) / 2.0
        a, b = hi - gr * (hi - lo), lo + gr * (hi - lo)
        fa, fb = val(a, 100.0), val(b, 100.0)
        for _ in range(22):
            if fa is None or fb is None:
                break
            if fa > fb:
                hi, b, fb = b, a, fa
                a = hi - gr * (hi - lo)
                fa = val(a, 100.0)
            else:
                lo, a, fa = a, b, fb
                b = lo + gr * (hi - lo)
                fb = val(b, 100.0)
        cands = [v for v in (best, fa, fb) if v is not None]
        got = -max(cands)
        err = abs(got - KAPPA[n])
        out.append({"n": n, "kappa_from_inner_model": got,
                    "kappa_recorded": KAPPA[n], "abs_err": err})
        ok = ok and err < 1e-6
    rep["slice"] = out
    return ok


def part_entry73(rep):
    e = E73
    sr = e["s"] * e["rho"]
    co = np.array([1.0, 0.0, -e["a"] * sr ** 2, (e["b"] + 1j * e["delta"]) * sr ** 3,
                   -e["s"] ** 4])
    roots = np.roots(co)
    rows = branch_lengths(roots)
    if rows is None:
        rep["entry73"] = {"error": "trace failed"}
        return False
    good = [r for r in rows if r.get("admissible") and "L" in r]
    o, R = min_enclosing_circle(roots)
    sumL = sum(r["L"] for r in good)
    minL = min(r["L"] for r in good)
    Zc = np.roots(np.polyder(co)) / sr
    A = inner_A(Zc, M=200.0)
    rep["entry73"] = {"max_abs_root": float(max(abs(roots))), "R": R,
                      "sum_L": sumL, "sum_L_recorded": e["sum_L"],
                      "sum_L_err": abs(sumL - e["sum_L"]),
                      "six_R": 6 * R, "six_R_recorded": e["six_R"],
                      "charge": sumL - 6 * R,
                      "min_L": minL, "min_L_recorded": e["min_L"],
                      "min_L_err": abs(minL - e["min_L"]),
                      "inner_A": A, "inner_sum_A": None if A is None else sum(A),
                      "inner_min_A": None if A is None else min(A)}
    return (abs(sumL - e["sum_L"]) < 1e-8 and abs(minL - e["min_L"]) < 1e-8
            and abs(6 * R - e["six_R"]) < 1e-8 and A is not None
            and sum(A) > 0 and min(A) < 0 and minL < 2 * R)


def part_e2e(rep):
    """n = 3, phi = 60 degrees.  min_c L(c)/(2R) = 1 + rho Phi/(2R) + O(rho^2),
    and the residual over rho^2 converges to -0.25."""
    ph = math.radians(60.0)
    Zc = np.array([np.exp(1j * ph / 2), -np.exp(1j * ph / 2)])
    A = inner_A(Zc, M=200.0)
    if A is None:
        rep["e2e"] = {"error": "inner trace failed"}
        return False
    Phi = min(A)
    out = []
    for rho in (0.05, 0.02, 0.01, 0.005):
        dc = 3.0 * np.poly(rho * Zc)
        co = np.polyint(dc)
        c = 1.0 - 3.0 * rho * rho
        co[-1] = -(c ** 3)
        roots = np.roots(co)
        if max(abs(roots)) >= 1.0:
            return False
        rows = branch_lengths(roots)
        if rows is None:
            return False
        good = [r for r in rows if r.get("admissible") and "L" in r]
        o, R = min_enclosing_circle(roots)
        got = min(r["L"] for r in good) / (2 * R)
        pred = 1.0 + rho * Phi / (2 * R)
        out.append({"rho": rho, "ratio": got, "predicted": pred,
                    "residual_over_rho2": (got - pred) / rho ** 2})
    rep["e2e"] = {"Phi": Phi, "rows": out}
    return abs(out[-1]["residual_over_rho2"] + 0.25) < 5e-3


def part_chord(rep):
    """(i) the PAIRING-FREE chord form never exceeds 1 on the recorded search
    output, and (ii) the pairing-fixed rows are re-derived exactly."""
    out = {"pairing_free": [], "exact_rows": []}
    ok = True
    for key, data in CHORD_ROWS.items():
        z = np.array([complex(a, b) for a, b in data["roots"]])
        s = data["s"]
        co = np.poly(z)
        crit = np.roots(np.polyder(co))
        o, R = min_enclosing_circle(z)
        num = den = 0.0
        for c in crit:
            v = abs(np.polyval(co, c))
            if v >= 1.0:
                continue
            mc = min(abs(c - a) + abs(c - b) for a, b in itertools.combinations(z, 2))
            num += v ** s * mc
            den += v ** s
        w = num / den / (2 * R) if den > 0 else None
        out["pairing_free"].append({"row": key, "W_minpair": w})
        if w is not None and w > 1.0 + 1e-9:
            ok = False                     # the note claims this never happens
    for key, data in CHORD_ROWS.items():
        if not data.get("exact"):
            continue
        D = data["den"]
        rq = [G(F(round(a * D), D), F(round(b * D), D)) for a, b in data["roots"]]
        cen = G(F(round(data["centre"][0] * D), D), F(round(data["centre"][1] * D), D))
        Rup = F(round(data["Rup"] * D) + 1, D)
        got = exact_chord_row(rq, data["crit_pairs"], int(data["s"]), cen, Rup)
        good = got is not None and got.get("exact_sum_sign", 0) > 0
        out["exact_rows"].append({"row": key, "denominator": D,
                                  "exact_sum": None if got is None else got.get("exact_sum"),
                                  "reason": None if got is None else got.get("reason"),
                                  "status": "certified" if good else "dropped"})
    rep["chord"] = out
    return ok


def part_climb(rep):
    out = []
    ok = True
    for key, Z in CLIMB.items():
        Zc = np.array([complex(a, b) for a, b in Z["Zc"]])
        vals = {}
        for M in (60.0, 300.0):
            A = inner_A(Zc, M=M)
            vals[f"M{int(M)}"] = None if A is None else min(A)
        good = all(v is not None for v in vals.values())
        agree = good and abs(vals["M60"] - vals["M300"]) < 1e-6
        near = good and abs(vals["M300"] - Z["Phi"]) < 1e-5
        out.append({"row": key, **vals, "recorded": Z["Phi"],
                    "two_radius_agreement": agree, "matches_record": near,
                    "sign": None if not good else (1 if vals["M300"] > 0 else -1),
                    "sign_matches_record": good and
                    (vals["M300"] > 0) == (Z["Phi"] > 0)})
        ok = ok and good and agree and near
    rep["climb"] = out
    return ok


def part_refute(rep):
    """Degree five: min over admissible critical points of L(c) EXCEEDS 2R on an
    actual monic quintic with all roots strictly inside the open unit disc.

    The polynomial is built from its own exact coefficients (f' = 5 prod (z -
    rho Z_j), f(0) = -c^5) at 60 mpmath digits, because reconstructing f from
    float64 roots destroys a_1, which is of order rho^{n-1} against a_0 of order
    one.  R is reported as max_k |a_k - o| for an EXHIBITED centre o, hence an
    upper bound for the true circumradius, so the inequality min L > 2R is only
    weakened by an imprecise centre.  Also checks that every sampled branch has
    chord sum below its reported length, which is the test that disqualifies a
    sheet-hopping continuation.
    """
    import mpmath as mp
    n = REFUTER["n"]
    Z = np.array([complex(a, b) for a, b in REFUTER["Zc"]])
    Z = Z - Z.mean()
    Z = Z / np.abs(Z).max()
    A = inner_A(Z, M=300.0)
    if A is None or min(A) <= 0:
        rep["refute"] = {"error": "inner model does not reproduce a positive min_j A_j",
                         "A": A}
        return False
    rows = []
    ok = True
    with mp.workdps(60):
        Zm = [mp.mpc(z.real, z.imag) for z in Z]
        for cval, rho in REFUTER["cases"]:
            cq, rq = mp.mpf(cval), mp.mpf(rho)
            dc = [mp.mpc(1)]
            for zj in Zm:
                nc = [mp.mpc(0)] * (len(dc) + 1)
                for i, ci in enumerate(dc):
                    nc[i] += ci
                    nc[i + 1] -= ci * (rq * zj)
                dc = nc
            dc = [n * x for x in dc]
            co = [dc[i] / (n - i) for i in range(n)] + [-cq ** n]
            roots = mp.polyroots(co, maxsteps=400, extraprec=1200)
            crit = mp.polyroots(dc, maxsteps=400, extraprec=1200)
            rt = [complex(z) for z in roots]
            o, _ = min_enclosing_circle(rt)
            Rup = float(max(abs(mp.mpc(o.real, o.imag) - z) for z in roots))
            mx = float(max(abs(z) for z in roots))
            br = branch_lengths_exact(np.array([complex(x) for x in co]),
                                      [complex(x) for x in crit], rt)
            if br is None:
                rows.append({"c": cval, "rho": rho, "error": "trace failed"})
                ok = False
                continue
            good = [r for r in br if r.get("admissible") and "L" in r]
            if len(good) < n - 1 or mx >= 1.0:
                rows.append({"c": cval, "rho": rho, "max_abs_root": mx,
                             "traced": len(good), "error": "incomplete"})
                ok = False
                continue
            minL = min(r["L"] for r in good)
            rows.append({"c": cval, "rho": rho, "max_abs_root": mx, "R_upper": Rup,
                         "minL": minL, "two_R_upper": 2 * Rup,
                         "minL_minus_2R": minL - 2 * Rup,
                         "over_rho": (minL - 2 * Rup) / rho,
                         "admissible": len(good),
                         "max_abs_f_at_hub": max(r["absv"] for r in br),
                         "max_endpoint_dist": max(r["maxdist"] for r in good),
                         "refutes_MIN": minL > 2 * Rup})
            ok = ok and minL > 2 * Rup and mx < 1.0
    # ---- conductor audit, 2026-09-05: the saddle-connection wall.  Arms of hub
    # i follow Q(Z) = V_i + s with s real increasing, so an arm from hub i runs
    # into hub j exactly when Im V_j = Im V_i and Re V_j > Re V_i.  A
    # configuration on (or within numerical reach of) that wall gives a
    # one-sided limit and cannot be a refutation.  The gap is reported together
    # with a deterministic perturbation table; the verdict is WITHDRAWN when the
    # gap is below 1e-8 of the value scale or the perturbed minimum is negative.
    Qn = np.polyint(float(n) * np.poly(Z))
    V = np.polyval(Qn, Z)
    gap, pair = float("inf"), None
    for i in range(len(V)):
        for j in range(len(V)):
            if i != j and V[j].real > V[i].real:
                d = abs(V[i].imag - V[j].imag)
                if d < gap:
                    gap, pair = d, (i + 1, j + 1)
    scale = float(np.abs(V).max())
    import random as _random
    prng = _random.Random(7)
    pert = {}
    for eps in (1e-4, 1e-3, 3e-3):
        vals = []
        for _ in range(6):
            Zp = Z + eps * np.array([complex(prng.gauss(0, 1), prng.gauss(0, 1)) for _ in Z])
            Ap = inner_A(Zp, M=300.0)
            if Ap is not None:
                vals.append(float(min(Ap)))
        pert[str(eps)] = {"draws": len(vals), "min": min(vals) if vals else None,
                          "max": max(vals) if vals else None}
    on_wall = gap < 1e-8 * scale
    perturbed_negative = all(v["max"] is not None and v["max"] < 0
                             for k, v in pert.items() if float(k) >= 1e-3)
    verdict = ("withdrawn_saddle_connection_wall" if (on_wall or perturbed_negative)
               else "candidate_refutation_requires_exact_certificate")
    rep["refute"] = {"inner_A": A, "inner_min_A": min(A), "cases": rows,
                     "critical_values_V": [[float(v.real), float(v.imag)] for v in V],
                     "wall_gap_abs_im": gap, "wall_pair": pair, "value_scale": scale,
                     "perturbation_min_A": pert, "verdict": verdict,
                     "statement": ("wall specimen: the reported min over admissible critical "
                                   "points of L(c) > 2R is a one-sided limit across a saddle "
                                   "connection and is NOT a refutation of (MIN)"
                                   if verdict.startswith("withdrawn") else
                                   "min over admissible critical points of L(c) > 2R")}
    return ok


CHORD_ROWS = {
 "n4_s4.0": {
  "s": 4.0,
  "roots": [
   [
    0.9159449226892564,
    -0.3039976397095177
   ],
   [
    0.3089214217919549,
    0.279196175839418
   ],
   [
    -0.09768071617278762,
    -0.9952167993402097
   ],
   [
    0.606775540086394,
    0.21146676986002166
   ]
  ],
  "crit_pairs": [
   {
    "c": [
     0.7510949220407369,
     -0.12905665523185358
    ],
    "pair": [
     0,
     3
    ]
   },
   {
    "c": [
     0.4421196331713029,
     0.23046422478003228
    ],
    "pair": [
     3,
     1
    ]
   },
   {
    "c": [
     0.10725632108407357,
     -0.7078211895608945
    ],
    "pair": [
     3,
     2
    ]
   }
  ],
  "centre": [
   0.2545474119568032,
   -0.391875014740094
  ],
  "Rup": 0.6986314931994748,
  "den": 1000000000000,
  "exact": True
 },
 "n4_s8.0": {
  "s": 8.0,
  "roots": [
   [
    0.9159449226892564,
    -0.3039976397095177
   ],
   [
    0.3089214217919549,
    0.279196175839418
   ],
   [
    -0.09768071617278762,
    -0.9952167993402097
   ],
   [
    0.606775540086394,
    0.21146676986002166
   ]
  ],
  "crit_pairs": [
   {
    "c": [
     0.7510949220407369,
     -0.12905665523185358
    ],
    "pair": [
     0,
     3
    ]
   },
   {
    "c": [
     0.4421196331713029,
     0.23046422478003228
    ],
    "pair": [
     3,
     1
    ]
   },
   {
    "c": [
     0.10725632108407357,
     -0.7078211895608945
    ],
    "pair": [
     3,
     2
    ]
   }
  ],
  "centre": [
   0.2545474119568032,
   -0.391875014740094
  ],
  "Rup": 0.6986314931994748,
  "den": 1000000000000,
  "exact": True
 },
 "n5_s8.0": {
  "s": 8.0,
  "roots": [
   [
    -0.6382798282002274,
    -0.7698031312703838
   ],
   [
    -0.8325866662815654,
    -0.5538929888806584
   ],
   [
    0.866842183558375,
    0.49858061414855304
   ],
   [
    0.9994193831189837,
    0.034042571099577805
   ],
   [
    -0.5189802857448712,
    0.8547850390648936
   ]
  ],
  "crit_pairs": [
   {
    "c": [
     0.009605127456489138,
     0.06387060618384056
    ],
    "pair": [
     2,
     1
    ]
   },
   {
    "c": [
     0.8897380080526065,
     0.24838699324897967
    ],
    "pair": [
     3,
     2
    ]
   },
   {
    "c": [
     -0.7220678016636887,
     -0.6525449422516549
    ],
    "pair": [
     0,
     1
    ]
   }
  ],
  "centre": [
   -1.0974549194535062e-15,
   1.21939435494834e-16
  ],
  "Rup": 0.9999989999999992,
  "den": 1000000000000,
  "exact": True
 },
 "n3_s4.0": {
  "s": 4.0,
  "roots": [
   [
    0.9253835694701373,
    -0.37902935157545226
   ],
   [
    -0.7069811595442226,
    -0.1193310708566383
   ],
   [
    -0.6582908360048498,
    0.14355051868968577
   ]
  ],
  "crit_pairs": [
   {
    "c": [
     -0.6772543604902688,
     0.011421869017786296
    ],
    "pair": [
     2,
     1
    ]
   },
   {
    "c": [
     0.38399540977097874,
     -0.24796180484605615
    ],
    "pair": [
     0,
     1
    ]
   }
  ],
  "centre": [
   0.12691570701526908,
   -0.13783358134152832
  ],
  "Rup": 0.8341021082289519,
  "den": 1000000000000,
  "exact": False
 },
 "n3_s8.0": {
  "s": 8.0,
  "roots": [
   [
    0.9253835694701373,
    -0.37902935157545226
   ],
   [
    -0.7069811595442226,
    -0.1193310708566383
   ],
   [
    -0.6582908360048498,
    0.14355051868968577
   ]
  ],
  "crit_pairs": [
   {
    "c": [
     -0.6772543604902688,
     0.011421869017786296
    ],
    "pair": [
     2,
     1
    ]
   },
   {
    "c": [
     0.38399540977097874,
     -0.24796180484605615
    ],
    "pair": [
     0,
     1
    ]
   }
  ],
  "centre": [
   0.12691570701526908,
   -0.13783358134152832
  ],
  "Rup": 0.8341021082289519,
  "den": 1000000000000,
  "exact": False
 }
}

PARTS = {"slice": part_slice, "entry73": part_entry73, "e2e": part_e2e,
         "chord": part_chord, "climb": part_climb, "refute": part_refute}


def main() -> int:
    ap = argparse.ArgumentParser()
    ap.add_argument("--part", default="all", choices=sorted(PARTS) + ["all"])
    args = ap.parse_args()
    todo = sorted(PARTS) if args.part == "all" else [args.part]
    rep: dict = {"analysis": "ErdosProblems/Erdos1041/NearFeketeInnerModelWidening.md",
                 "parts": {}}
    ok = True
    for name in todo:
        good = bool(PARTS[name](rep))
        rep["parts"][name] = "PASS" if good else "FAIL"
        ok = ok and good
    rep["status"] = "PASS" if ok else "FAIL"
    rep["evidence_class"] = ("finite_computational_evidence_with_exact_rational_chord_"
                             "certificates_and_two_radius_branch_audit")
    print(json.dumps(rep, separators=(",", ":"), default=float))
    return 0 if ok else 1


if __name__ == "__main__":
    sys.exit(main())
