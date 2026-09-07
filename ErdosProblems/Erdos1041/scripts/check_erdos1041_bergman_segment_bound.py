#!/usr/bin/env python3
"""Erdős 1041 — the Bergman segment bound, and room-to-length without Koebe.

`AffineNormalisedModuli.md` Theorem R converts "the merge component has room"
into a bound on the descent-arc length `L(c*)` using Koebe's growth and
distortion theorems.  Koebe is sharp for the Koebe function, whose image is a
slit plane; a lemniscate component is nothing like one, and the resulting
Corollary R needs a level ratio `t/mu > coth^2(1/8) = 64.68` before it fires.

This file checks the replacement.  The descent arc is `psi([-q,q])` for the
Riemann map `psi : D -> Omega_t` (Theorem B), so the object to estimate is the
length of the image of a DIAMETER, and for that the sharp tool is not
distortion but the Bergman kernel:

    ( int_{-q}^{q} |h| ds )^2  <=  ||h||^2_{A^2(D)}  *  Lambda(q),

    Lambda(q) = int_{-q}^{q} int_{-q}^{q} ds ds' / (pi (1 - s s')^2)
              = (2/pi) log( (1+q^2)/(1-q^2) ) .

With `h = psi'`, `||psi'||^2 = Area(Omega_t)` and `q^2 = mu/t`:

    L(c*)^2  <=  (2 Area(Omega_t) / pi) * log( (t+mu)/(t-mu) )
             <=  t^{2/n} * 2 log( (t+mu)/(t-mu) )          (Polya)

so at `t = 1` the criterion is `mu < tanh(1) = 0.7616` against Corollary R's
`mu < tanh^2(1/8) = 0.01548`.

Riemann-Hurwitz gives `b = k-1`, so Theorem B needs no minimality of mu and the
machinery runs at every admissible hub; and since a two-root component is the
binding case of Conjecture (C) of CapacityGeodesicConjecture.md for a Morse f,
the same bound proves (C) outside the degree-free window [v, coth(1) v).

Arms, each fail-closed
  KERN   the closed form for Lambda(q), against an independent 40-digit double
         quadrature, plus the Lemma B majorant as an upper cross-check
  EXTR   h(z) = 1/(1-q^2 z^2) attains Lambda(q), and its primitive is univalent
         -- so 2/pi is sharp among CONFORMAL maps, not merely in the Bergman
         class
  QUAD   the quadratic equality family z^2 - d^2, where L = 2R exactly: the
         bound is 2 sqrt(1 + 1/(12 t^2) + O(t^-4)), so it must stay strictly
         above 2 and converge to it.  40 digits: float64 loses five to
         cancellation in bound^2/4 - 1
  AREA   the erode/dilate area bracket contains the exact Cassini area 2tE(1/t^2)
  POLYA  Area(Omega_t) <= pi t^{2/n}
  THMA   no L(c) > bound(area_hi) at any admissible (hub, level) pair
  REACH  settled counts against Theorem R (R1) and (R2), same hypothesis set
  SHELL  where the criterion stops firing on the near-Fekete shell, at two
         resolutions
  THRESH Corollary D against Corollary R, and Theorem E's coth(1) edge

Replay:

    ./repo-python formal_math/erdos257_period_noncollapse/ErdosProblems/\\
Erdos1041/scripts/check_erdos1041_bergman_segment_bound.py --part all \\
        --trials 3 --grid 701
"""
from __future__ import annotations

import argparse
import json
import os
import sys

import numpy as np
from scipy import ndimage
from scipy.optimize import linear_sum_assignment

REPO = os.path.abspath(os.path.join(os.path.dirname(__file__), *[os.pardir] * 5))
RECEIPT = os.path.join(
    REPO, "state", "formal_math", "erdos257_period_noncollapse",
    "erdos1041_bergman_segment_bound_receipt.json")


# ------------------------------------------------------------------ geometry
def _c2(a, b):
    return (a + b) / 2, abs(a - b) / 2


def _c3(a, b, c):
    ax, ay, bx, by, cx, cy = a.real, a.imag, b.real, b.imag, c.real, c.imag
    d = 2 * (ax * (by - cy) + bx * (cy - ay) + cx * (ay - by))
    if abs(d) < 1e-300:
        return None
    ux = ((ax**2 + ay**2) * (by - cy) + (bx**2 + by**2) * (cy - ay)
          + (cx**2 + cy**2) * (ay - by)) / d
    uy = ((ax**2 + ay**2) * (cx - bx) + (bx**2 + by**2) * (ax - cx)
          + (cx**2 + cy**2) * (bx - ax)) / d
    o = complex(ux, uy)
    return o, abs(a - o)


def min_enclosing(z):
    """Exact MEC over pairs and triples (negative_results 34: approximate MEC
    inflates R, which sits in the obligation's denominator)."""
    z = np.asarray(z, complex)
    best = None
    m = len(z)
    for i in range(m):
        for j in range(i + 1, m):
            o, r = _c2(z[i], z[j])
            if np.max(np.abs(z - o)) <= r * (1 + 1e-12) and (best is None or r < best[1]):
                best = (o, r)
    for i in range(m):
        for j in range(i + 1, m):
            for k in range(j + 1, m):
                got = _c3(z[i], z[j], z[k])
                if got is None:
                    continue
                o, r = got
                if np.max(np.abs(z - o)) <= r * (1 + 1e-12) and (best is None or r < best[1]):
                    best = (o, r)
    o, _ = best
    return complex(o), float(np.max(np.abs(z - o)))


def mesh(mu, k, logdepth=10):
    """Dense in t near 0 and in log(mu - t) near mu; depth 10 per the drift
    table in AffineNormalisedModuli.md section 2."""
    a = mu * np.sin(np.linspace(0.0, np.pi / 2, k + 1)) ** 2
    b = mu * (1.0 - np.logspace(0.0, -logdepth, k))
    return np.unique(np.concatenate([a, b[b > 0]]))


def track(coef, theta, ts, roots):
    e = np.exp(1j * theta)
    tail = coef[:-1]
    cur = np.asarray(roots, complex)
    acc = np.zeros(len(roots))
    for t in ts[1:]:
        w = np.roots(np.concatenate([tail, [coef[-1] - t * e]]))
        _, col = linear_sum_assignment(np.abs(cur[:, None] - w[None, :]))
        nxt = w[col]
        acc += np.abs(nxt - cur)
        cur = nxt
    return acc, cur


def analyse(roots, steps=420):
    """Normalise to MEC = unit disk; return mu, c*, merge pair, L(c*), t_2."""
    roots = np.asarray(roots, complex)
    n = len(roots)
    ctr, R = min_enclosing(roots)
    if R <= 0:
        return None
    rt = (roots - ctr) / R
    cf = np.poly(rt)
    cp = np.roots(np.polyder(cf))
    cv = np.polyval(cf, cp)
    if len(cp) == 0:
        return None
    mu = float(np.abs(cv).min())
    if not np.isfinite(mu) or mu <= 1e-12:
        return None
    ev = []
    for k in np.argsort(np.abs(cv)):
        c, v = cp[k], cv[k]
        m = abs(v)
        if m <= 0 or not np.isfinite(m):
            continue
        acc, cur = track(cf, float(np.angle(v)), mesh(m * (1 - 1e-13), steps), rt)
        d = np.abs(cur - c)
        o = np.argsort(d)
        i, j = int(o[0]), int(o[1])
        ev.append(dict(absv=m, c=complex(c), i=i, j=j,
                       L=float(acc[i] + acc[j] + d[i] + d[j]),
                       chord=float(abs(rt[i] - c) + abs(rt[j] - c))))
    if not ev:
        return None
    star = ev[0]
    par = list(range(n))

    def find(x):
        while par[x] != x:
            par[x] = par[par[x]]
            x = par[x]
        return x

    par[find(star["i"])] = find(star["j"])
    target = find(star["j"])
    t2 = np.inf
    for e in ev[1:]:
        ri, rj = find(e["i"]), find(e["j"])
        if ri == rj:
            continue
        if find(target) in (ri, rj):
            t2 = e["absv"]
            break
        par[ri] = rj
    return dict(n=n, roots=rt, cf=cf, mu=mu, t2=float(t2), cstar=star["c"],
                L=star["L"], chord=star["chord"], hubs=ev)


MAX_AREA_SPREAD = 1.10    # resolution gate, see Grid.component


class Grid:
    """|f| sampled once per configuration; component area BRACKETED by erosion
    and dilation, plus three fail-closed guards.

    Each guard pins a violation this arm actually produced before it existed
    (worst `L/bound` was 1.1209, eleven rows, all at degree >= 6):

    (1) NO FALLBACK.  If the hub's own cell is not below the level, the
        component through the hub is not resolved and the level is refused.
        The old code took an arbitrary neighbouring label, which at a sub-grid
        neck is ONE lobe -- an area far below the truth.  Area is a numerator,
        so that is the unsafe direction.

    (2) RIEMANN-HURWITZ CONSISTENCY.  A component holding `k` roots holds
        exactly `k-1` critical points with multiplicity, so "exactly two roots"
        and "exactly one critical point" are the same hypothesis.  They are not
        equally observable: roots sit in lobes joined by necks that go sub-grid
        as `t -> v`, whereas critical points are interior and far from the level
        set.  NINE of the eleven violations had two critical points in the
        component -- three roots -- while the root count read two.  Both counts
        are now required to agree.

    (3) AREA BRACKET.  `area_lo` erodes the component by one cell and `area_hi`
        dilates it by one; the true boundary lies within one cell of the
        sampled one, so the pair brackets the truth.  A level whose spread
        exceeds MAX_AREA_SPREAD is refused, and the two ends are then used in
        opposite directions: `area_lo` makes the theorem test STRICT (a small
        area makes the bound small, so a spurious violation is possible but a
        spurious pass is not), and `area_hi` makes a settlement claim
        CONSERVATIVE.  Arm `AREA` calibrates the bracket against the one area
        this file knows in closed form, the Cassini oval `2 t E(1/t^2)`.
    """

    def __init__(self, cf, box=2.02, N=801, centre=0j, N_refine=None):
        xs = centre.real + np.linspace(-box, box, N)
        ys = centre.imag + np.linspace(-box, box, N)
        X, Y = np.meshgrid(xs, ys, indexing="ij")
        self.xs, self.ys, self.N = xs, ys, N
        self.V = np.abs(np.polyval(cf, (X + 1j * Y).ravel()).reshape(X.shape))
        self.hx = xs[1] - xs[0]
        self.cell = self.hx ** 2
        self.cf = np.asarray(cf)
        self.crit = np.roots(np.polyder(cf)) if len(cf) > 2 else np.array([])
        self.critval = (np.abs(np.polyval(cf, self.crit)) if self.crit.size
                        else np.array([]))
        # the refinement box is a small fraction of the global one, so a
        # much smaller N there is already far finer in absolute cell size
        self.N_refine = 321 if N_refine is None else N_refine

    def _idx(self, z):
        return (int(np.argmin(np.abs(self.xs - z.real))),
                int(np.argmin(np.abs(self.ys - z.imag))))

    def _raw(self, t, cstar, roots, need_two):
        lab, _ = ndimage.label(self.V < t)
        ix, iy = self._idx(cstar)
        if not (0 <= ix < self.N and 0 <= iy < self.N):
            return None
        l0 = lab[ix, iy]
        if l0 == 0:                                              # guard (1)
            return None
        mask = lab == l0
        # a component touching the frame is truncated: refuse rather than
        # under-report its area
        if (mask[0, :].any() or mask[-1, :].any()
                or mask[:, 0].any() or mask[:, -1].any()):
            return "frame"
        st = ndimage.generate_binary_structure(2, 1)
        lo = int(ndimage.binary_erosion(mask, st).sum())
        hi = int(ndimage.binary_dilation(mask, st).sum())
        if lo == 0:
            return None
        k = sum(1 for r in roots if mask[self._idx(r)])
        if need_two:
            kc = sum(1 for c, cv in zip(self.crit, self.critval)
                     if cv < t and mask[self._idx(c)])
            if k == 2 and kc != 1:                               # guard (2)
                return None
        idx = np.argwhere(mask)
        bb = (self.xs[idx[:, 0].min()], self.xs[idx[:, 0].max()],
              self.ys[idx[:, 1].min()], self.ys[idx[:, 1].max()])
        return (float(lo * self.cell), float(hi * self.cell), k, bb)

    def component(self, t, cstar, roots, need_two=True, _depth=0):
        """(area_lo, area_hi, root count) with all guards, or (None, None, None).

        If the bracket is wider than MAX_AREA_SPREAD the component is too small
        for this grid, so it is RE-GRIDDED on its own bounding box once.  Small
        components are exactly the tight ones (a merge pair far from everything
        else, locally a Cassini oval), so refusing them outright would bias the
        measured reach downwards and hide the regime where the bound is sharp.
        """
        got = self._raw(t, cstar, roots, need_two)
        if got is None or got == "frame":
            return None, None, None
        lo, hi, k, bb = got
        if hi <= lo * MAX_AREA_SPREAD or _depth >= 1:
            if hi > lo * MAX_AREA_SPREAD:                        # guard (3)
                return None, None, None
            return lo, hi, k
        half = 0.5 * max(bb[1] - bb[0], bb[3] - bb[2])
        ctr = complex(0.5 * (bb[0] + bb[1]), 0.5 * (bb[2] + bb[3]))
        if half <= 0 or not np.isfinite(half):
            return None, None, None
        sub = Grid(self.cf, box=half * 1.35 + 3 * self.hx, N=self.N_refine,
                   centre=ctr, N_refine=self.N_refine)
        return sub.component(t, cstar, roots, need_two, _depth=1)


def two_root_window(g, c, v, roots, hi=1.0, iters=14):
    """Largest t <= hi whose component at c holds exactly two roots.

    The component grows with t, so its root count is non-decreasing and a
    bisection is valid.  Returns None when the hub is unusable -- either the
    two components merging at c already carry more than two roots between them,
    or no level below hi resolves.
    """
    lo = v + 1e-9 * max(v, 1.0)
    if lo >= hi:
        return None
    area, _, k = g.component(lo, c, roots)
    if area is not None and k is not None and k > 2:
        return None
    a2, _, k2 = g.component(hi, c, roots)
    if a2 is not None and k2 == 2:
        return hi
    a, b = lo, hi
    for _ in range(iters):
        m = 0.5 * (a + b)
        ar, _, kk = g.component(m, c, roots)
        if ar is not None and kk == 2:
            a = m
        else:
            b = m
    return a


def hub_bounds(g, rec, n, hubs=None, hi=1.0):
    """Best (over hubs and levels) value of each of the four estimates, on a
    single shared hypothesis set: hub Fekete-admissible, component two-rooted."""
    out = dict(berg=np.inf, polya=np.inf, koebe1=np.inf, koebe2=np.inf,
               trueL=np.inf, pairs=0, polya_bad=0, worst=0.0, worst_hi=0.0)
    for h in (hubs if hubs is not None else rec["hubs"]):
        v = h["absv"]
        if v > hi:
            continue
        out["trueL"] = min(out["trueL"], h["L"])
        if v >= hi:
            continue
        tmax = two_root_window(g, h["c"], v, rec["roots"], hi=hi)
        if tmax is None:
            continue
        for frac in (0.12, 0.3, 0.5, 0.7, 0.85, 0.95, 1.0):
            t = v + frac * (tmax - v)
            if t <= v:
                continue
            a_lo, a_hi, k = g.component(t, h["c"], rec["roots"])
            if a_lo is None or k != 2:
                continue
            out["pairs"] += 1
            if a_hi > np.pi * t ** (2.0 / n) * 1.02:
                out["polya_bad"] += 1
            # Two statistics, because the area is bracketed, not exact:
            #   worst_lo = L / bound(area_lo)  -- STRICT; values slightly above
            #     one are the bracket's own width and are not violations
            #   worst_hi = L / bound(area_hi)  -- the VERDICT: above one means
            #     the theorem fails even granting the largest area the
            #     instrument admits
            out["worst"] = max(out["worst"], h["L"] / bound(a_lo, v, t))
            bg = bound(a_hi, v, t)
            out["worst_hi"] = max(out["worst_hi"], h["L"] / bg)
            q = float(np.sqrt(v / t))
            out["berg"] = min(out["berg"], bg)
            out["polya"] = min(out["polya"], bound(np.pi * t ** (2.0 / n), v, t))
            out["koebe2"] = min(out["koebe2"],
                                float(8 * t ** (1.0 / n) * np.log((1 + q) / (1 - q))))
            out["koebe1"] = min(out["koebe1"],
                                float(h["chord"] * ((1 + q) / (1 - q)) ** 2))
    return out


# ------------------------------------------------------------------- the bound
def lam(q):
    """Lambda(q) = (2/pi) log((1+q^2)/(1-q^2))."""
    return (2.0 / np.pi) * np.log((1.0 + q * q) / (1.0 - q * q))


def bound(area, mu, t):
    return float(np.sqrt((2.0 * area / np.pi) * np.log((t + mu) / (t - mu))))


# ------------------------------------------------------------------------ arms
def arm_kern():
    """Lambda(q) in closed form against an independent 2-D quadrature of the
    Bergman kernel, and against the crude hyperbolic majorant of Lemma B."""
    import mpmath as mp
    mp.mp.dps = 30
    worst, worstb, rows = 0.0, 0.0, []
    for qf in (0.1, 0.35, 0.6, 0.8, 0.93, 0.99):
        q = mp.mpf(qf)
        num = mp.quad(lambda s: mp.quad(lambda u: 1 / (mp.pi * (1 - s * u) ** 2),
                                        [-q, q]), [-q, q])
        got = mp.mpf(2) / mp.pi * mp.log((1 + q * q) / (1 - q * q))
        rel = abs(num - got) / got
        # Lemma B majorant: Lambda(gamma) <= (1/pi) (int |dz|/(1-|z|^2))^2
        hyp = (mp.log((1 + q) / (1 - q))) ** 2 / mp.pi
        worst = max(worst, float(rel))
        worstb = max(worstb, float(got / hyp))
        rows.append(dict(q=qf, quad=float(num), closed=float(got), rel=float(rel),
                         lemmaB=float(hyp), sharp_over_lemmaB=float(got / hyp)))
    return dict(ok=bool(worst < 1e-12 and worstb <= 1.0), worst_rel=float(worst),
                worst_sharp_over_lemmaB=float(worstb), rows=rows)


def arm_extr():
    """h_q(z) = 1/(1-q^2 z^2) attains Lambda(q); its primitive is univalent."""
    rows = []
    ok = True
    for q in (0.25, 0.55, 0.8, 0.95):
        # ||h||^2 = pi * sum_m q^{4m}/(2m+1) = (pi/q^2) artanh(q^2)
        nrm2 = (np.pi / q ** 2) * np.arctanh(q * q)
        s = np.linspace(-q, q, 400001)
        seg = np.trapezoid(1.0 / (1 - q * q * s * s), s)   # h > 0 on [-q,q]
        ratio = seg * seg / (nrm2 * lam(q))
        # univalence of psi(z) = log((1+qz)/(1-qz)) / (2q) on a dense sample
        m = 260
        rr = np.sqrt(np.linspace(1e-6, 1.0, m))
        th = np.linspace(0, 2 * np.pi, m, endpoint=False)
        Z = (rr[:, None] * np.exp(1j * th)[None, :]).ravel()
        W = np.log((1 + q * Z) / (1 - q * Z)) / (2 * q)
        # injective iff no two distinct sample points collide
        order = np.argsort(W.real)
        Ws, Zs = W[order], Z[order]
        coll = 0
        for i in range(len(Ws)):
            j = i + 1
            while j < len(Ws) and Ws[j].real - Ws[i].real < 1e-9:
                if abs(Ws[j] - Ws[i]) < 1e-9 and abs(Zs[j] - Zs[i]) > 1e-6:
                    coll += 1
                j += 1
        good = bool(abs(ratio - 1.0) < 1e-6 and coll == 0)
        ok = ok and good
        rows.append(dict(q=q, ratio=float(ratio), collisions=int(coll), ok=bool(good)))
    return dict(ok=bool(ok), rows=rows)


def arm_quad():
    """z^2 - 1: R = 1, mu = 1, c* = 0, and L(c*) = |a-b| = 2R = 2 EXACTLY --
    the quadratic equality family of `admissible_branch_length_reformulation`.

    Here Omega_t is the whole Cassini oval {|z^2-1| < t} (connected for t > 1),
    and its area has a closed form: putting w = z^2,

        Area = (1/2) int_{|w-1|<t} dA(w)/|w| = (1/2) int_0^{2pi} rho(phi) dphi

    with rho(phi) = cos phi + sqrt(t^2 - sin^2 phi), so Area(t) = 2 t E(1/t)
    with E the complete elliptic integral of the second kind.  Then

        (2 Area/pi) log((t+1)/(t-1)) = 4 (1 + 1/(12 t^2) + O(t^-4)),

    so the bound is 2 sqrt(1 + 1/(12t^2)): strictly above the true L = 2 at
    every finite level, and converging to it.  The theorem is therefore
    ASYMPTOTICALLY EXACT on an equality family of the problem, which is what
    Koebe-based (R2) cannot do -- it loses a factor >= 2 wherever it fires.

    Fails closed if the bound ever drops below 2, or if the Richardson
    coefficient t^2 (bound^2/4 - 1) misses 1/12.
    """
    import mpmath as mp
    mp.mp.dps = 40
    rows = []
    ok = True
    for tf in (1.5, 3.0, 10.0, 100.0, 1000.0, 1e4):
        t = mp.mpf(tf)
        area = 2 * t * mp.ellipe(1 / (t * t))          # mpmath takes m = k^2
        b = mp.sqrt((2 * area / mp.pi) * mp.log((t + 1) / (t - 1)))
        coef = t * t * (b * b / 4 - 1)
        rows.append(dict(t=float(t), area=float(area), bound=float(b),
                         over=float(b - 2), richardson=float(coef)))
        if b <= 2:
            ok = False
    coef = rows[-1]["richardson"]
    ok = bool(ok and abs(coef - 1.0 / 12.0) < 1e-8
              and rows[-1]["bound"] > 2.0
              and rows[-1]["bound"] - 2.0 < 1e-8)
    return dict(ok=ok, richardson_limit=float(coef), one_twelfth=1.0 / 12.0,
                rows=rows)


def arm_area():
    """Calibrate the grid area bracket against the one area known in closed
    form: Omega = {|z^2-1| < t} has Area = 2 t E(1/t^2) exactly (see QUAD).

    Fails if the bracket ever fails to contain the exact value, or if it is
    wider than MAX_AREA_SPREAD where the gate would have admitted it.
    """
    import mpmath as mp
    mp.mp.dps = 30
    cf = np.array([1.0, 0.0, -1.0])                 # z^2 - 1
    rows, ok = [], True
    for N in (601, 801, 1201):
        g = Grid(cf, box=2.02, N=N)
        for t in (1.2, 1.6, 2.4):
            lo, hi, k = g.component(t, 0j, np.array([1.0 + 0j, -1.0 + 0j]),
                                    need_two=False)
            if lo is None:
                rows.append(dict(N=N, t=t, refused=True))
                continue
            exact = float(2 * mp.mpf(t) * mp.ellipe(1 / (mp.mpf(t) ** 2)))
            good = bool(lo <= exact <= hi and k == 2)
            ok = ok and good
            rows.append(dict(N=N, t=t, lo=lo, hi=hi, exact=exact,
                             spread=hi / lo, lo_rel=lo / exact - 1.0,
                             hi_rel=hi / exact - 1.0, brackets=good))
    live = [r for r in rows if not r.get("refused")]
    return dict(ok=bool(ok and live),
                worst_lo_rel=float(min(r["lo_rel"] for r in live)) if live else 0.0,
                worst_hi_rel=float(max(r["hi_rel"] for r in live)) if live else 0.0,
                rows=rows)


def _sample(rng, n, fam):
    if fam == "unif":
        return np.sqrt(rng.random(n)) * np.exp(2j * np.pi * rng.random(n))
    if fam == "bdry":
        return (1 - 0.15 * rng.random(n)) * np.exp(2j * np.pi * rng.random(n))
    if fam == "poly":
        return np.exp(2j * np.pi * np.arange(n) / n + 0.35j * rng.normal(size=n)) * (
            1 - 0.1 * rng.random(n))
    if fam == "clus":
        c = rng.random(3) * 2 * np.pi
        return 0.8 * np.exp(1j * c[rng.integers(0, 3, n)]) + 0.25 * (
            rng.normal(size=n) + 1j * rng.normal(size=n))
    if fam.startswith("fek"):
        eps = float(fam[3:])
        return np.exp(2j * np.pi * np.arange(n) / n + 1j * eps * rng.normal(size=n))
    raise ValueError(fam)


def arm_configs(trials, grid_n, degrees):
    """Every Fekete-admissible hub, every level inside the bisected two-root
    window: all four estimates on the SAME hypothesis set, so the comparison
    isolates Koebe against Bergman.  Riemann-Hurwitz forces one branch point in
    a two-root component, so Theorem B applies at any such hub, not only c*."""
    rng = np.random.default_rng(1041_2026)
    fams = ["unif", "bdry", "poly", "clus", "fek0.30", "fek0.10"]
    rows, npairs, polya_bad, worst, worst_hi = [], 0, 0, 0.0, 0.0
    for n in degrees:
        for fam in fams:
            for _ in range(trials):
                z = _sample(rng, n, fam)
                if np.min(np.abs(z[:, None] - z[None, :] + 9 * np.eye(n))) < 1e-3:
                    continue
                rec = analyse(z)
                if rec is None:
                    continue
                g = Grid(rec["cf"], N=grid_n)
                r = hub_bounds(g, rec, n)
                npairs += r["pairs"]
                polya_bad += r["polya_bad"]
                worst = max(worst, r["worst"])
                worst_hi = max(worst_hi, r["worst_hi"])
                if r["pairs"]:
                    r.update(n=n, fam=fam, mu=float(rec["mu"]))
                    rows.append(r)
    return rows, npairs, polya_bad, worst, worst_hi


def arm_reach(rows):
    m = len(rows)
    if m == 0:
        return dict(ok=False, note="no admissible configurations")
    nb = sum(1 for r in rows if r["berg"] < 2)
    npy = sum(1 for r in rows if r["polya"] < 2)
    n1 = sum(1 for r in rows if r["koebe1"] < 2)
    n2 = sum(1 for r in rows if r["koebe2"] < 2)
    nR = sum(1 for r in rows if min(r["koebe1"], r["koebe2"]) < 2)
    nU = sum(1 for r in rows if min(r["berg"], r["koebe1"]) < 2)
    strictly_new = sum(1 for r in rows
                       if r["berg"] < 2 <= min(r["koebe1"], r["koebe2"]))
    lost = sum(1 for r in rows if min(r["koebe1"], r["koebe2"]) < 2 <= r["berg"])
    return dict(ok=bool(nb > nR and nU >= nR), total=m, bergman=nb, polya=npy,
                koebe_R1=n1, koebe_R2=n2, theoremR_either=nR, union=nU,
                settled_only_by_bergman=strictly_new,
                settled_only_by_theoremR=lost,
                true_minL_lt_2=sum(1 for r in rows if r["trueL"] < 2))


def _shell_best(rec, n, grid_n):
    g = Grid(rec["cf"], N=grid_n)
    r = hub_bounds(g, rec, n)
    return r["berg"], r["trueL"], r["worst_hi"]


def arm_shell(grid_n):
    """Where Theorem C stops firing on the near-Fekete shell, with a resolution
    guard.

    Deterministic angular perturbation of the regular n-gon, roots kept exactly
    on the unit circle so R = 1 throughout.  `rho` is the mean critical-point
    modulus, the cusp law's parameter.

    RESOLUTION GUARD.  The area enters the bound as a numerator, so an
    UNDER-reported area makes the bound smaller -- the unsafe direction -- and
    a coarse grid under-reports exactly where the necks between petals are
    thinnest, which is the near-Fekete shell.  Every row is therefore computed
    at two resolutions and the arm fails if the coarse grid returns a bound
    more than 2% below the fine one, or if a verdict flips.
    """
    rows = []
    for n in (4, 5, 6):
        d = np.cos(np.arange(n) * 2.7 + 0.4)
        d = d - d.mean()
        d = d / np.linalg.norm(d)
        for eps in (0.6, 0.4, 0.25, 0.15, 0.08, 0.04, 0.02, 0.01, 0.005, 0.002):
            z = np.exp(2j * np.pi * np.arange(n) / n + 1j * eps * d)
            rec = analyse(z)
            if rec is None:
                continue
            b1, L1, w1 = _shell_best(rec, n, grid_n)
            b2, _, _ = _shell_best(rec, n, int(grid_n * 1.5) | 1)
            rho = float(np.mean(np.abs(np.roots(np.polyder(rec["cf"])))))
            drift = float(b1 / b2) if np.isfinite(b1) and np.isfinite(b2) else 1.0
            rows.append(dict(n=n, eps=eps, rho=rho, mu=float(rec["mu"]),
                             bound=float(b1), bound_fine=float(b2),
                             coarse_over_fine=drift, trueL=float(L1),
                             fires=bool(b1 < 2.0),
                             fires_fine=bool(b2 < 2.0)))
    # A verdict that differs between resolutions is acceptable ONLY at the
    # cut-off, where the two bounds straddle 2: that is the ladder step at
    # which the criterion switches off, and the flip locates it rather than
    # contradicting it.  Anywhere else a flip means the area is not resolved.
    flips = [r for r in rows if r["fires"] != r["fires_fine"]]
    straddle = all(min(r["bound"], r["bound_fine"]) < 2.0
                   < max(r["bound"], r["bound_fine"])
                   and abs(r["coarse_over_fine"] - 1.0) < 0.02 for r in flips)
    ok = bool(rows
              and any(r["fires"] for r in rows)
              and all(r["trueL"] < 2.0 + 1e-9 for r in rows)
              and all(abs(r["coarse_over_fine"] - 1.0) < 0.02 for r in rows)
              and straddle
              and all(sum(1 for r in flips if r["n"] == n) <= 1
                      for n in (4, 5, 6)))
    cut = {}
    for n in (4, 5, 6):
        for key in ("fires", "fires_fine"):
            sub = sorted([r for r in rows if r["n"] == n and r[key]],
                         key=lambda r: r["eps"])
            cut[f"{n}_{key}"] = sub[0]["eps"] if sub else None
    return dict(ok=ok, smallest_firing_eps=cut, verdict_flips=len(flips),
                worst_coarse_over_fine=float(min(
                    (r["coarse_over_fine"] for r in rows), default=1.0)),
                rows=rows)


def main() -> int:
    ap = argparse.ArgumentParser()
    ap.add_argument("--part", default="all",
                    choices=["all", "kern", "extr", "quad", "area", "configs",
                             "shell"])
    ap.add_argument("--trials", type=int, default=4)
    ap.add_argument("--grid", type=int, default=801)
    ap.add_argument("--degrees", type=int, nargs="+", default=[3, 4, 5, 6, 7, 8])
    ap.add_argument("--json", action="store_true")
    args = ap.parse_args()

    arms = {}
    if args.part in ("all", "kern"):
        arms["KERN"] = arm_kern()
    if args.part in ("all", "extr"):
        arms["EXTR"] = arm_extr()
    if args.part in ("all", "quad"):
        arms["QUAD"] = arm_quad()
    if args.part in ("all", "area"):
        arms["AREA"] = arm_area()
    if args.part in ("all", "shell"):
        arms["SHELL"] = arm_shell(args.grid)
    if args.part in ("all", "configs"):
        rows, npairs, bad, worst, worst_hi = arm_configs(
            args.trials, args.grid, args.degrees)
        arms["THMA"] = dict(ok=bool(worst_hi <= 1.0 and npairs > 0),
                            pairs=npairs,
                            verdict_L_over_bound_area_hi=float(worst_hi),
                            strict_L_over_bound_area_lo=float(worst))
        arms["POLYA"] = dict(ok=bool(bad == 0 and npairs > 0), violations=bad, pairs=npairs)
        arms["REACH"] = arm_reach(rows)

    # Corollary D against Corollary R, and Theorem E's window for Conjecture (C)
    # of CapacityGeodesicConjecture.md.
    thr_new = float(np.tanh(1.0))
    thr_old = float(np.tanh(0.125) ** 2)
    coth1 = 1.0 / thr_new
    # At t = coth(1) v the Polya form of Theorem C equals 2 t^{1/n} exactly, at
    # EVERY degree: the t^{1/n} cancels, which is why Theorem E's window is
    # degree-free.
    edge = abs(np.sqrt(2 * np.log((coth1 + 1.0) / (coth1 - 1.0))) - 2.0)
    arms["THRESH"] = dict(ok=bool(thr_new / thr_old > 40.0 and edge < 1e-12),
                          bergman_mu_threshold=thr_new,
                          corollaryR_mu_threshold=thr_old,
                          ratio=thr_new / thr_old,
                          theoremE_window_coth1=float(coth1),
                          theoremE_edge_residual=float(edge))

    ok = bool(all(a.get("ok") for a in arms.values()))

    def plain(o):
        if isinstance(o, dict):
            return {k: plain(v) for k, v in o.items()}
        if isinstance(o, (list, tuple)):
            return [plain(v) for v in o]
        if isinstance(o, np.bool_):
            return bool(o)
        if isinstance(o, np.integer):
            return int(o)
        if isinstance(o, np.floating):
            return float(o)
        return o

    out = plain(dict(schema="erdos1041_bergman_segment_bound_v1", ok=ok, arms=arms))
    os.makedirs(os.path.dirname(RECEIPT), exist_ok=True)
    with open(RECEIPT, "w") as fh:
        json.dump(out, fh, indent=2, sort_keys=True)
    if args.json:
        print(json.dumps(out, indent=2, sort_keys=True))
    else:
        for k, v in arms.items():
            print(f"{'PASS' if v.get('ok') else 'FAIL'}  {k}  "
                  f"{ {kk: vv for kk, vv in v.items() if kk not in ('rows',)} }")
        print(f"receipt {RECEIPT}")
    return 0 if ok else 1


if __name__ == "__main__":
    sys.exit(main())
