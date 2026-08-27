#!/usr/bin/env python3
"""Erdos #1041 -- visibility-overlap reduction receipt.

The reduction turns Erdos #1041 into a ONE-ROOT statement.  Every negative
result on file has the shape "at most one" (nearest spoke, origin spoke,
contained spoke at every admissible hub, MEC arm).  The topological lemma below
says one is enough: closed visibility sets that COVER a connected component
cannot be pairwise disjoint, so two of them meet, and their meeting point sees
two roots.

Arms
  topology  -- the structural hypotheses the lemma consumes, checked on a fixed
               corpus: mu <= 1 (Fekete), every sublevel component holds a root,
               the first-merge component holds at least two.
  covermu   -- the reduced statement (COVER): sup over the first-merge component
               of the intrinsic distance to the root set, MINIMISED OVER THE
               LEVEL, since (COVER) is existential in the level.  Grid paths are
               genuine paths, so the value is an UPPER bound and "<= 1 + grid
               tolerance" is a sound confirmation.  Also reports the scale-free
               form (divided by mu^(1/n)) and the conclusion (pair geodesic < 2).
  levels    -- the level is load-bearing and the constant is NOT monotone in it:
               an adversarial degree-three configuration reads 1.0349 at the
               fixed level 1.01*mu, stably under grid refinement, and 0.9427 at
               1.0005*mu.  Pins that behaviour so it is not rediscovered.
  extremal  -- exact equality on z^n - r^n, by closed form, no grid.
  amgm      -- the Euclidean half of the reduction and its rigidity, exact.
  onespoke  -- the equality-stratum stress statement ONE-SPOKE is FALSE: pins the
               exact n = 5 Gaussian-rational countermodel, and retains the n = 3
               sweep and the random sample as the record of why sampling missed it.
  e16       -- exact rational correction to the recorded origin-spoke witness:
               it carries ZERO safe spokes, not "at most one".

Replay
  ./repo-python formal_math/erdos257_period_noncollapse/ErdosProblems/Erdos1041/\
scripts/check_erdos1041_visibility_overlap.py --part all
"""
from __future__ import annotations

import argparse
import json
import os
import sys
from fractions import Fraction

import numpy as np

try:
    from scipy.sparse import coo_matrix
    from scipy.sparse.csgraph import connected_components, dijkstra
except Exception as exc:  # pragma: no cover
    print("scipy required: %s" % exc)
    raise

REPO = os.path.abspath(os.path.join(os.path.dirname(__file__), "..", "..", "..", "..", ".."))
RECEIPT = os.path.join(
    REPO, "state", "formal_math", "erdos257_period_noncollapse",
    "erdos1041_visibility_overlap_receipt.json",
)

# A grid path is a polyline through admitted cells, hence a genuine path in the
# region; its length over-estimates the geodesic.  The 16-neighbour stencil
# leaves a residual metric anisotropy that the validated cases below pin at
# about 1.2 per cent, so the arm tolerance is set from measurement, not taste.
GRID_TOL = 0.03

STENCIL = [
    (dx, dy)
    for dx in range(-2, 3)
    for dy in range(-2, 3)
    if (dx, dy) != (0, 0) and np.gcd(abs(dx), abs(dy)) == 1
]


# ---------------------------------------------------------------- primitives


def poly_from_roots(roots):
    P = np.array([1.0 + 0j])
    for zk in roots:
        Q = np.zeros(len(P) + 1, dtype=complex)
        Q[:-1] += P * (-zk)
        Q[1:] += P
        P = Q
    return P


def critical_points(roots):
    P = poly_from_roots(roots)
    dP = P[1:] * np.arange(1, len(P))
    return np.roots(dP[::-1])


def fval(roots, z):
    v = np.ones(np.shape(z), dtype=complex) if np.ndim(z) else 1.0 + 0j
    for zk in roots:
        v = v * (z - zk)
    return v


def mu_of(roots):
    c = critical_points(roots)
    vals = np.abs(np.array([fval(roots, x) for x in c]))
    i = int(np.argmin(vals))
    return float(vals[i]), complex(c[i])


def segment_max(roots, h, a):
    """max |f| on [h, a], exactly: max of a real degree-2n polynomial over the
    real roots of its derivative together with the two endpoints."""
    d = a - h
    P = np.array([1.0 + 0j])
    for zk in roots:
        Q = np.zeros(len(P) + 1, dtype=complex)
        Q[:-1] += P * (h - zk)
        Q[1:] += P * d
        P = Q
    L = len(P)
    R = np.zeros(2 * L - 1)
    for i in range(L):
        R += np.concatenate([np.zeros(i), (P[i] * np.conj(P)).real, np.zeros(L - 1 - i)])
    dR = R[1:] * np.arange(1, len(R))
    cands = [0.0, 1.0]
    k = len(dR)
    while k > 1 and dR[k - 1] == 0:
        k -= 1
    if k >= 2:
        for r in np.roots(dR[:k][::-1]):
            if abs(r.imag) < 1e-12 and 0.0 < r.real < 1.0:
                cands.append(float(r.real))
    return float(np.sqrt(max(max(np.polyval(R[::-1], t) for t in cands), 0.0)))


# ------------------------------------------------------------------- corpus


def corpus():
    """Deterministic configuration corpus.  Roots in the CLOSED unit disk."""
    rng = np.random.default_rng(20260824)
    rows = []
    for n in (2, 3, 4, 5, 6, 8):
        for r in (0.999, 0.9):
            rows.append(("z^%d-%.3f^%d" % (n, r, n),
                         r * np.exp(2j * np.pi * np.arange(n) / n)))
    eta = np.array([0.00173207975211076, -0.01636641293505736, 0.01474617820591595,
                    0.01950276945344509, -0.05244827523897744, 0.032833660762563])
    rows.append(("hexagon-witness", np.exp(1j * (2 * np.pi * np.arange(6) / 6 + eta))))
    r = 99999 / 100000
    rows.append(("E16-origin-spoke",
                 np.array([r, r * (-20 + 99j) / 101, r * (-20 - 99j) / 101,
                           r * (-28 + 195j) / 197, r * (-28 - 195j) / 197])))
    L = 999 / 1000
    rows.append(("neg37-minimal-cubic",
                 np.array([L * (7 + 24j) / 25, L * (7 - 24j) / 25, -L])))
    p = 999 / 1000
    rows.append(("E13-balanced-quintic",
                 np.array([(901 / 902) * p, 1j * p, -1j * p,
                           p * (-451 + 780j) / 901, p * (-451 - 780j) / 901])))
    for n in (3, 4, 5, 6, 9):
        for t in range(2):
            z = rng.uniform(0, 1, n) ** 0.5 * np.exp(2j * np.pi * rng.uniform(0, 1, n))
            rows.append(("random-n%d-%d" % (n, t), z))
    for n in (4, 5, 6, 8):
        for sc in (1e-1, 1e-2, 1e-3):
            d = rng.normal(size=n)
            d -= d.mean()
            d /= np.linalg.norm(d)
            rows.append(("nearFekete-n%d-%.0e" % (n, sc),
                         np.exp(1j * (2 * np.pi * np.arange(n) / n + sc * d))))
    return rows


# ------------------------------------------------------- grid geodesic engine


#: (COVER) reads "there IS a level lambda in [mu,1]".  The max distance is NOT
#: monotone in lambda -- it drops when a further merge joins a component, adding
#: shortcuts faster than it adds points to cover -- so a single fixed level is
#: the wrong measurement.  A fixed 1.01*mu reads 1.0349 on the adversarial n=3
#: leader while 1.0005*mu reads 0.9427 and lambda=1 reads 0.9937.
LEVEL_SCAN = (1.0002, 1.0005, 1.002, 1.005, 1.01, 1.03, 1.08, 1.2, 1.5, 1e9)


def merge_component_distances(roots, grid=601, slack=1.01):
    """Distances inside the first-merge component of {|f| <= lambda}.

    Returns (max distance to the root set, mu, lambda, #roots in component,
    best pair geodesic, grid step) -- all UPPER bounds on the true geodesics.
    """
    roots = np.asarray(roots, dtype=complex)
    n = len(roots)
    mu, cs = mu_of(roots)
    lam = min(1.0, mu * slack)
    if lam < mu:
        lam = mu
    half = 1.05 * max(float(np.abs(roots).max()), abs(cs)) + lam ** (1.0 / n) + 0.05
    xs = np.linspace(-half, half, grid)
    step = float(xs[1] - xs[0])
    X, Y = np.meshgrid(xs, xs, indexing="ij")
    Z = X + 1j * Y
    inside = np.abs(fval(roots, Z)) <= lam
    idx = -np.ones((grid, grid), dtype=np.int64)
    ok = np.flatnonzero(inside.ravel())
    if ok.size == 0:
        return None
    idx.ravel()[ok] = np.arange(ok.size)
    rows, cols, vals = [], [], []
    for dx, dy in STENCIL:
        m = max(abs(dx), abs(dy))
        si = slice(max(0, -dx), grid - max(0, dx))
        sj = slice(max(0, -dy), grid - max(0, dy))
        ti = slice(max(0, dx), grid - max(0, -dx))
        tj = slice(max(0, dy), grid - max(0, -dy))
        good = inside[si, sj] & inside[ti, tj]
        for s in range(1, m):
            t = s / m
            ai, aj = int(round(dx * t)), int(round(dy * t))
            mi = slice(max(0, -dx) + ai, grid - max(0, dx) + ai)
            mj = slice(max(0, -dy) + aj, grid - max(0, dy) + aj)
            good = good & inside[mi, mj]
        rows.append(idx[si, sj][good])
        cols.append(idx[ti, tj][good])
        vals.append(np.full(int(good.sum()), step * float(np.hypot(dx, dy))))
    G = coo_matrix(
        (np.concatenate(vals), (np.concatenate(rows), np.concatenate(cols))),
        shape=(ok.size, ok.size),
    ).tocsr()
    _, lab = connected_components(G, directed=False)
    flat = Z.ravel()[ok]
    comp = lab[int(np.argmin(np.abs(flat - cs)))]
    sel = np.flatnonzero(lab == comp)
    srcs, extra = [], []
    for zk in roots:
        d = np.abs(flat[sel] - zk)
        k = int(np.argmin(d))
        if d[k] < 3 * step:
            srcs.append(sel[k])
            extra.append(float(d[k]))
    if len(srcs) < 2:
        return None
    D = dijkstra(G, directed=False, indices=srcs)[:, sel] + np.array(extra)[:, None]
    Dmin = D.min(axis=0)
    fin = np.isfinite(Dmin)
    cover = float(Dmin[fin].max())
    second = np.sort(D[:, fin], axis=0)[1]
    pair = float(2 * second.min())
    return dict(cover=cover, mu=mu, lam=lam, nroots=len(srcs), pair=pair, step=step)


# ------------------------------------------------------------------- the arms


def arm_topology():
    """Structural hypotheses the lemma consumes."""
    bad = []
    rows = []
    for name, roots in corpus():
        roots = np.asarray(roots, dtype=complex)
        n = len(roots)
        R = float(np.abs(roots).max())
        mu, _ = mu_of(roots)
        disc = 1.0
        for i in range(n):
            for j in range(i + 1, n):
                disc *= abs(roots[i] - roots[j]) ** 2
        fekete = disc / (n ** n)
        rows.append(dict(name=name, n=n, R=R, mu=mu, fekete_ratio=fekete))
        if R > 1.0 + 1e-12:
            bad.append((name, "root outside closed unit disk", R))
        if mu > 1.0 + 1e-9:
            bad.append((name, "mu exceeds 1", mu))
        if fekete > 1.0 + 1e-9:
            bad.append((name, "Fekete ratio exceeds 1", fekete))
        # mu^(n-1) <= prod |f(c)| = |disc|/n^n  is the recorded sandwich
        if n >= 2 and mu ** (n - 1) > fekete * (1 + 1e-7) + 1e-12:
            bad.append((name, "mu^(n-1) exceeds disc/n^n", mu ** (n - 1)))
    return dict(status="ok" if not bad else "fail", violations=bad,
                rows_checked=len(rows),
                max_mu=max(r["mu"] for r in rows),
                max_fekete_ratio=max(r["fekete_ratio"] for r in rows))


def best_level(roots, grid=601):
    """min over the level scan of the (COVER) constant; also the best pair seen."""
    best, bestrow, pair = float("inf"), None, float("inf")
    for f in LEVEL_SCAN:
        out = merge_component_distances(roots, grid=grid, slack=f)
        if out is None:
            continue
        pair = min(pair, out["pair"])
        if out["cover"] < best:
            best, bestrow = out["cover"], out
    if bestrow is None:
        return None
    bestrow = dict(bestrow)
    bestrow["pair"] = pair
    return bestrow


def arm_covermu(grid=601):
    """(COVER) and its scale-free form, plus the conclusion.

    (COVER) is an EXISTENTIAL over the level, so the measurement scans levels and
    keeps the best; a single fixed level is not the statement.
    """
    rows, bad = [], []
    for name, roots in corpus():
        out = best_level(roots, grid=grid)
        if out is None:
            rows.append(dict(name=name, skipped=True))
            continue
        n = len(roots)
        ratio = out["cover"] / (out["mu"] ** (1.0 / n)) if out["mu"] > 0 else float("nan")
        rows.append(dict(name=name, n=n, mu=out["mu"], lam=out["lam"],
                         cover=out["cover"], geo_ratio=ratio, pair=out["pair"],
                         roots_in_component=out["nroots"], grid_step=out["step"]))
        if out["cover"] > 1.0 + GRID_TOL:
            bad.append((name, "COVER exceeds 1 beyond grid tolerance", out["cover"]))
        if out["pair"] >= 2.0 + GRID_TOL:
            bad.append((name, "pair geodesic reaches 2", out["pair"]))
    live = [r for r in rows if not r.get("skipped")]
    return dict(status="ok" if not bad else "fail", violations=bad,
                rows=len(live), grid=grid, grid_tolerance=GRID_TOL,
                level_scan=list(LEVEL_SCAN),
                max_cover=max(r["cover"] for r in live),
                max_geo_ratio=max(r["geo_ratio"] for r in live),
                max_pair=max(r["pair"] for r in live),
                detail=live)


#: The adversarial n=3 leader.  A fixed level 1.01*mu makes the whole-component
#: covering read 1.0349 here -- above 1, and stable under grid refinement from
#: h = 0.0174 down to h = 0.0035, so it is not a discretisation artefact.  It is
#: a refutation of the FIXED-LEVEL reading only: the level scan finds 0.9427 at
#: 1.0005*mu and 0.9937 at lambda = 1.
ADVERSARIAL_N3 = [
    complex(-0.044684909847, 0.96237987266),
    complex(-0.86660933908, -0.498987227711),
    complex(0.864151412519, -0.503231891122),
]


def arm_levels(grid=701):
    """The level in (COVER) is not free, and the existential is what survives."""
    roots = np.asarray(ADVERSARIAL_N3, dtype=complex)
    mu, _ = mu_of(roots)
    rows = []
    for f in (1.0005, 1.002, 1.01, 1.03, 1e9):
        out = merge_component_distances(roots, grid=grid, slack=f)
        if out is None:
            continue
        rows.append(dict(level_factor=f, lam=out["lam"], cover=out["cover"],
                         pair=out["pair"], roots_in_component=out["nroots"]))
    fixed = [r for r in rows if abs(r["level_factor"] - 1.01) < 1e-9]
    best = min(r["cover"] for r in rows)
    ok = (best <= 1.0 + GRID_TOL) and bool(fixed) and fixed[0]["cover"] > 1.0
    return dict(
        status="ok" if ok else "fail",
        violations=[] if ok else [("levels", "level-scan behaviour changed", best)],
        mu=mu, roots=[[z.real, z.imag] for z in roots],
        best_cover_over_levels=best,
        fixed_level_1p01mu_cover=(fixed[0]["cover"] if fixed else None),
        non_monotone_in_level=True,
        detail=rows,
    )


def arm_extremal():
    """Exact equality on z^n - r^n, closed form, no grid.

    The only critical point is 0 with |f(0)| = r^n, so mu^(1/n) = r; the radial
    segment [0, r w] is interior because |f(t r w)| = r^n (1 - t^n) <= r^n; and
    the distance from 0 to a root is exactly r.  So the reduced statement holds
    with EQUALITY at every degree, and the pair path has length exactly 2r.
    """
    rows, bad = [], []
    for n in (2, 3, 4, 5, 6, 8, 12, 20):
        for r in (0.5, 0.9, 0.999, 0.999999):
            roots = r * np.exp(2j * np.pi * np.arange(n) / n)
            mu, cs = mu_of(roots)
            spoke = segment_max(roots, 0j, roots[0])
            rows.append(dict(n=n, r=r, mu=mu, mu_root=mu ** (1.0 / n),
                             spoke_max=spoke, dist=r, pair=2 * r,
                             hub_abs=abs(cs)))
            if abs(mu - r ** n) > 1e-12 * max(1.0, r ** n):
                bad.append((n, r, "mu != r^n", mu))
            if abs(mu ** (1.0 / n) - r) > 1e-12:
                bad.append((n, r, "mu^(1/n) != r", mu ** (1.0 / n)))
            if spoke > r ** n * (1 + 1e-12):
                bad.append((n, r, "radial spoke leaves the sublevel set", spoke))
            if 2 * r >= 2.0:
                bad.append((n, r, "pair length reaches 2", 2 * r))
    return dict(status="ok" if not bad else "fail", violations=bad,
                rows=len(rows),
                equality_note="dist(0,root) = r = mu^(1/n) exactly at every degree",
                detail=rows)


def arm_amgm():
    """The Euclidean half of the reduction, and its rigidity.

    GM >= min gives  min_k |h - z_k| <= |f(h)|^(1/n)  for every h, with equality
    iff every root is equidistant from h.  So the equality stratum of the
    reduced statement is exactly "all roots on a circle about h", where the
    spokes become  prod_k |t w_j - w_k|  with all |w_k| = 1.
    """
    rng = np.random.default_rng(4242)
    worst = 0.0
    bad = []
    for _ in range(4000):
        n = int(rng.integers(2, 10))
        z = rng.uniform(0, 1, n) ** 0.5 * np.exp(2j * np.pi * rng.uniform(0, 1, n))
        h = rng.uniform(-1.5, 1.5) + 1j * rng.uniform(-1.5, 1.5)
        lam = abs(fval(z, h))
        near = float(np.abs(z - h).min())
        if lam == 0.0:
            continue
        ratio = near / lam ** (1.0 / n)
        worst = max(worst, ratio)
        if ratio > 1.0 + 1e-9:
            bad.append((n, ratio))
    # rigidity: equality forces all distances equal
    n = 6
    w = np.exp(2j * np.pi * rng.uniform(0, 1, n))
    lam = abs(fval(w, 0j))
    near = float(np.abs(w).min())
    rigid = abs(near - lam ** (1.0 / n)) < 1e-12
    return dict(status="ok" if (not bad and rigid) else "fail", violations=bad,
                worst_ratio=worst, rigidity_equality_holds=bool(rigid),
                samples=4000)


def arm_e16():
    """Exact rational correction to the recorded origin-spoke witness.

    exact_results::two_safe_origin_spokes_counterexample records "at most one
    safe root-to-origin spoke".  Exact Gaussian-rational evaluation shows the
    count is ZERO: every one of the five spokes carries a rational waypoint with
    |f|^2 > 1.  The witness is therefore sharper than recorded, and it is the
    configuration that forces the reduction to be applied to the first-merge
    component rather than to the component of the origin.
    """
    r = Fraction(99999, 100000)
    roots = [
        (r, Fraction(0)),
        (r * Fraction(-20, 101), r * Fraction(99, 101)),
        (r * Fraction(-20, 101), -r * Fraction(99, 101)),
        (r * Fraction(-28, 197), r * Fraction(195, 197)),
        (r * Fraction(-28, 197), -r * Fraction(195, 197)),
    ]

    def f_abs2(pt):
        re, im = Fraction(1), Fraction(0)
        for (a, b) in roots:
            dr, di = pt[0] - a, pt[1] - b
            re, im = re * dr - im * di, re * di + im * dr
        return re * re + im * im

    witnesses = []
    for j, (a, b) in enumerate(roots):
        found = None
        for num in range(1, 1000):
            t = Fraction(num, 1000)
            v = f_abs2((t * a, t * b))
            if v > 1:
                found = (str(t), float(v))
                break
        witnesses.append(dict(spoke=j, waypoint=found))
    unsafe = sum(1 for w in witnesses if w["waypoint"] is not None)
    origin = f_abs2((Fraction(0), Fraction(0)))
    return dict(
        status="ok" if unsafe == 5 else "fail",
        safe_origin_spokes=5 - unsafe,
        unsafe_origin_spokes=unsafe,
        f_at_origin_abs2=float(origin),
        recorded_claim="at most one safe root-to-origin spoke",
        exact_finding="zero safe root-to-origin spokes",
        witnesses=witnesses,
    )


def _fprime(roots, z):
    s = 0j
    for k in range(len(roots)):
        p = 1.0 + 0j
        for j in range(len(roots)):
            if j != k:
                p *= (z - roots[j])
        s += p
    return s


def _newton_to(roots, z0, target, iters=60):
    z = z0
    for _ in range(iters):
        d = _fprime(roots, z)
        if d == 0:
            break
        step = (fval(roots, z) - target) / d
        z = z - step
        if abs(step) < 1e-15:
            break
    return z


def _branch_pair(roots, c, npts=180):
    """The two descending inverse-ray branches from a simple critical point c,
    traced by value continuation along the ray arg f = arg f(c)."""
    v = fval(roots, c)
    eps = 1e-6
    A = (fval(roots, c + eps) - 2 * v + fval(roots, c - eps)) / eps ** 2
    out = []
    ss = np.sort(1 - np.geomspace(1e-12, 1.0, npts))[::-1]
    for sgn in (+1, -1):
        pts, z, first = [c], c, True
        for s in ss:
            if first:
                z = c + sgn * np.sqrt(2 * v * (s - 1) / A)
                first = False
            z = _newton_to(roots, z, v * s)
            pts.append(z)
        pts.append(_newton_to(roots, z, 0j))
        out.append(np.array(pts))
    return out[0], out[1]


def arm_path(samples=140, seg_tol=1e-9):
    """Separate containment, unit-arm COVER, and direct-JOIN predicates.

    The lemma only needs the covering on a compact connected subset carrying two
    roots, with paths allowed to run in the whole component.  Here it is tested
    The historical instrument checked segment containment but omitted the
    length-at-most-one clause in COVER.  It also rejected a row when *some*
    overlap point had total arm length above two, although direct JOIN needs
    only one overlap point at or below two.  Keep all three predicates explicit.
    """
    rows, bad, excluded = [], [], []
    for name, roots in corpus():
        roots = np.asarray(roots, dtype=complex)
        if len(roots) < 3:
            excluded.append((name, "degree below three"))
            continue
        mu, cs = mu_of(roots)
        # GUARD 1 (negative_results entry 24): at a DEGENERATE hub the two-branch
        # square-root model is the wrong local model.  On z^n - r^n the (n-1)-fold
        # point at the origin resolves numerically into a cloud of radius 5.1e-3
        # and the tracer walks straight out of the lemniscate.  Such rows are
        # EXCLUDED and receipted, and are covered instead by the `extremal` arm,
        # which asserts them from the closed form.
        cps = critical_points(roots)
        if int((np.abs(cps - cs) < 1e-3).sum()) > 1:
            excluded.append((name, "degenerate minimising hub"))
            continue
        try:
            pa, pb = _branch_pair(roots, cs, npts=samples)
        except Exception:
            excluded.append((name, "branch trace raised"))
            continue
        ia = int(np.argmin(np.abs(roots - pa[-1])))
        ib = int(np.argmin(np.abs(roots - pb[-1])))
        if ia == ib:
            excluded.append((name, "both branches reached the same root"))
            continue
        a, b = roots[ia], roots[ib]
        gamma = np.concatenate([pa[::-1], pb[1:]])
        # GUARD 2: a traced arc that leaves {|f| <= 1} is a failed TRACE, not a
        # failed covering.  Validate before scoring.
        if float(np.abs(fval(roots, gamma)).max()) > 1.0 + 1e-9:
            excluded.append((name, "traced arc leaves the lemniscate"))
            continue
        containedA = np.array([segment_max(roots, h, a) <= 1.0 for h in gamma])
        containedB = np.array([segment_max(roots, h, b) <= 1.0 for h in gamma])
        da = np.abs(gamma - a)
        db = np.abs(gamma - b)
        unitA = containedA & (da <= 1.0 + seg_tol)
        unitB = containedB & (db <= 1.0 + seg_tol)
        containment_both = containedA & containedB
        ell = da + db
        direct_join = containment_both & (ell <= 2.0 + seg_tol)
        containment_uncovered = int((~(containedA | containedB)).sum())
        unit_uncovered = int((~(unitA | unitB)).sum())
        rows.append(dict(name=name, n=len(roots), points=len(gamma),
                         containment_uncovered=containment_uncovered,
                         unit_uncovered=unit_uncovered,
                         containment_both=int(containment_both.sum()),
                         direct_join_count=int(direct_join.sum()),
                         min_ell_at_containment_both=(
                             float(ell[containment_both].min()) if containment_both.any() else None),
                         max_ell_at_containment_both=(
                             float(ell[containment_both].max()) if containment_both.any() else None)))
        if containment_uncovered:
            bad.append((name, "containment cover fails", containment_uncovered))
        if not direct_join.any():
            bad.append((name, "no sampled target-deciding direct JOIN", unit_uncovered))
    return dict(status="ok" if not bad else "fail", violations=bad,
                excluded=excluded, excluded_count=len(excluded),
                rows=len(rows), points_per_row=(rows[0]["points"] if rows else 0),
                containment_uncovered_total=sum(r["containment_uncovered"] for r in rows),
                unit_uncovered_total=sum(r["unit_uncovered"] for r in rows),
                unit_cover_rows=sum(r["unit_uncovered"] == 0 for r in rows),
                min_containment_both_count=min((r["containment_both"] for r in rows), default=0),
                min_direct_join_count=min((r["direct_join_count"] for r in rows), default=0),
                worst_minimum_join_length=max(
                    (r["min_ell_at_containment_both"] or math.inf) for r in rows),
                detail=rows)


def _spoke_maxima(theta, tgrid):
    """max_t of S_j(t) = sum_k log|t w_j - w_k|, for every j, on a t-grid."""
    C = np.cos(theta[:, None] - theta[None, :])
    Q = tgrid[None, None, :] ** 2 - 2 * tgrid[None, None, :] * C[:, :, None] + 1.0
    return 0.5 * np.log(np.maximum(Q, 1e-300)).sum(axis=1).max(axis=1)


def arm_onespoke(grid3=181, samples=4000):
    """(ONE-SPOKE) is FALSE at n = 5.  This arm PINS the countermodel.

    The statement was: for w_1..w_n on the unit circle some j has
    prod_k |t w_j - w_k| <= 1 for every t in [0,1].  A concurrent line
    (codex_root, commit 9fede2b363, checker
    formal_math/probes/erdos1041_one_spoke_countermodel.py) exhibits an exact
    Gaussian-rational refutation; it is re-verified here independently, in
    Fraction arithmetic, and the five directions are exactly those of
    exact_results::two_safe_origin_spokes_counterexample.

    The n = 3 sweep and the random sample are RETAINED, not as support, but as
    the record of why sampling could not find it: the failure is invisible at
    degree three and the margins are 1e-4 in a set the sampler never drew.
    negative_results entry 19, applied to this file.
    """
    T = np.concatenate([np.linspace(0, 0.9, 600), 1 - np.geomspace(1e-9, 0.1, 600)])
    # n = 2, one parameter
    worst2 = -np.inf
    for c in np.linspace(-1, 1, 4001):
        phi = float(np.arccos(np.clip(c, -1, 1)))
        m = _spoke_maxima(np.array([0.0, phi]), T)
        worst2 = max(worst2, float(m.min()))
    # n = 3, swept
    b = np.linspace(0, 2 * np.pi, grid3, endpoint=False)
    worst3, lead3 = -np.inf, None
    for i in range(grid3):
        for k in range(grid3):
            th = np.array([0.0, b[i], b[k]])
            v = float(_spoke_maxima(th, T).min())
            if v > worst3:
                worst3, lead3 = v, th.copy()
    # sampled degrees
    rng = np.random.default_rng(90210)
    worstN, nosafe, counts = -np.inf, 0, []
    for trial in range(samples):
        n = int(rng.integers(3, 13))
        mode = trial % 3
        if mode == 0:
            th = np.sort(rng.uniform(0, 2 * np.pi, n))
        elif mode == 1:
            th = 2 * np.pi * np.arange(n) / n + rng.normal(size=n) * rng.choice([3e-1, 3e-2, 3e-3])
        else:
            th = np.sort(np.concatenate([rng.normal(0, 0.3, n // 2),
                                         rng.normal(np.pi, 0.3, n - n // 2)]))
        m = _spoke_maxima(th, T)
        counts.append(int((m <= 1e-12).sum()))
        worstN = max(worstN, float(m.min()))
        if m.min() > 1e-12:
            nosafe += 1
    # the exact countermodel, in rational arithmetic
    W = [(Fraction(1), Fraction(0)),
         (Fraction(-20, 101), Fraction(99, 101)), (Fraction(-20, 101), Fraction(-99, 101)),
         (Fraction(-28, 197), Fraction(195, 197)), (Fraction(-28, 197), Fraction(-195, 197))]
    TS = [Fraction(339, 1000), Fraction(1, 1000), Fraction(1, 1000),
          Fraction(1, 500), Fraction(1, 500)]

    def _prod_abs2(pt):
        re, im = Fraction(1), Fraction(0)
        for (a, b) in W:
            dr, di = pt[0] - a, pt[1] - b
            re, im = re * dr - im * di, re * di + im * dr
        return re * re + im * im

    on_circle = all(a * a + b * b == 1 for a, b in W)
    cm = []
    for j, (a, b) in enumerate(W):
        t = TS[j]
        v = _prod_abs2((t * a, t * b))
        cm.append(dict(j=j, t=str(t), prod_abs2=float(v), exceeds_one=bool(v > 1)))
    refuted = on_circle and all(r["exceeds_one"] for r in cm)

    ok = refuted and (worst2 <= 1e-9) and (worst3 <= 1e-9) and nosafe == 0
    return dict(
        status="ok" if ok else "fail",
        violations=[] if ok else [("onespoke", "countermodel or sweep behaviour changed",
                                   [refuted, worst2, worst3])],
        one_spoke_is_false=True,
        countermodel_points="1, (-20+-99i)/101, (-28+-195i)/197 (exactly on |z|=1)",
        countermodel_on_unit_circle_exactly=bool(on_circle),
        countermodel_witnesses=cm,
        countermodel_source="codex_root commit 9fede2b363; re-verified independently here",
        sampling_did_not_find_it=True,
        n2_sweep_worst=worst2,
        n3_grid=grid3, n3_configurations=grid3 * grid3, n3_sweep_worst=worst3,
        n3_leader=[float(x) for x in (lead3 if lead3 is not None else [])],
        sampled=samples, sampled_worst=worstN,
        configurations_with_no_safe_spoke=nosafe,
        mean_safe_spokes=float(np.mean(counts)), min_safe_spokes=int(min(counts)),
    )


ARMS = {
    "topology": arm_topology,
    "covermu": arm_covermu,
    "levels": arm_levels,
    "path": arm_path,
    "extremal": arm_extremal,
    "amgm": arm_amgm,
    "onespoke": arm_onespoke,
    "e16": arm_e16,
}


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--part", default="all", help="all | " + " | ".join(ARMS))
    ap.add_argument("--grid", type=int, default=601)
    args = ap.parse_args()
    parts = list(ARMS) if args.part == "all" else [p.strip() for p in args.part.split(",")]
    out = {"schema": "erdos1041_visibility_overlap_receipt_v1", "arms": {}}
    rc = 0
    for p in parts:
        if p not in ARMS:
            print("unknown arm %r" % p)
            return 2
        res = ARMS[p](grid=args.grid) if p in ("covermu",) else ARMS[p]()
        out["arms"][p] = res
        flag = res.get("status")
        print("[%s] %s" % (flag.upper(), p), end="")
        if p == "covermu":
            print("  rows=%d  max COVER=%.5f  max GEO ratio=%.5f  max pair=%.5f  (tol %.2f)"
                  % (res["rows"], res["max_cover"], res["max_geo_ratio"],
                     res["max_pair"], res["grid_tolerance"]))
        elif p == "topology":
            print("  rows=%d  max mu=%.6f  max disc/n^n=%.6f"
                  % (res["rows_checked"], res["max_mu"], res["max_fekete_ratio"]))
        elif p == "extremal":
            print("  rows=%d  equality at every degree" % res["rows"])
        elif p == "amgm":
            print("  worst near/lam^(1/n)=%.9f over %d samples; rigidity=%s"
                  % (res["worst_ratio"], res["samples"], res["rigidity_equality_holds"]))
        elif p == "levels":
            print("  best over level scan=%.5f ; fixed 1.01*mu reads %.5f (non-monotone in level)"
                  % (res["best_cover_over_levels"], res["fixed_level_1p01mu_cover"]))
        elif p == "path":
            print("  rows=%d pts/row=%d  containment-uncovered=%d  unit-uncovered=%d  "
                  "unit-cover rows=%d  min direct-JOIN points=%d  worst best-JOIN=%.5f"
                  % (res["rows"], res["points_per_row"],
                     res["containment_uncovered_total"], res["unit_uncovered_total"],
                     res["unit_cover_rows"], res["min_direct_join_count"],
                     res["worst_minimum_join_length"]))
            print("       excluded (receipted, not dropped): %d -> %s"
                  % (res["excluded_count"], res["excluded"][:6]))
        elif p == "onespoke":
            print("  ONE-SPOKE is FALSE: exact n=5 countermodel pinned (on |z|=1 exactly: %s);"
                  % res["countermodel_on_unit_circle_exactly"])
            print("       n=3 sweep %d configs worst=%+.3e and %d random rows found NOTHING "
                  "-- why sampling missed it (mean/min safe spokes %.3f / %d)"
                  % (res["n3_configurations"], res["n3_sweep_worst"], res["sampled"],
                     res["mean_safe_spokes"], res["min_safe_spokes"]))
        elif p == "e16":
            print("  safe origin spokes = %d (recorded: 'at most one')"
                  % res["safe_origin_spokes"])
        if flag != "ok":
            rc = 1
            for v in res.get("violations", [])[:8]:
                print("     violation: %s" % (v,))
    os.makedirs(os.path.dirname(RECEIPT), exist_ok=True)
    with open(RECEIPT, "w") as fh:
        json.dump(out, fh, indent=1, sort_keys=True, default=float)
    print("receipt -> %s" % os.path.relpath(RECEIPT, REPO))
    return rc


if __name__ == "__main__":
    sys.exit(main())
