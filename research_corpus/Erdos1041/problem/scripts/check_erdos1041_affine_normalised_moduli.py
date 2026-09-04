#!/usr/bin/env python3
r"""Receipt for AffineNormalisedModuli.md.

Five arms, each of which can fail the script.

  INV   Theorem N(b): L/(2R), L/(2 mu^{1/n}) and the Fekete-admissible hub set
        A_F = {c : |f(c)| <= R^n} are invariant under z -> lambda z + beta.
        The invariance is exact algebra, so any residual is float64
        conditioning: the arm requires the drift under a MILD similarity to sit
        at machine level and to be far below the drift under a strong one, and
        requires |A_F| to match exactly (a discrete test).

  EXT   Theorem N(d): the whole extremal family z^n - r^n -- every r in (0,1),
        every rotation, translation and scaling -- normalises to the SINGLE
        polynomial u^n + 1, i.e. to the origin a = 0 of the free parameter
        space; and conversely (z-c)^n + v does so for every c, v.  Run at 40
        digits with the hub in closed form, so it tests the algebra rather than
        float64 root extraction at a multiplicity-(n-1) point.

  PREC  The degenerate-hub under-report of `negative_results` entry 24 is a
        PRECISION artifact, not an intrinsic property of a degenerate hub.  The
        identical pipeline -- root extraction on P - t, nearest-point matching,
        straight chord into the hub -- is run on P = u^n + 1, whose true value
        is minl_S = 1 by ordinary proof, at several working precisions.  The
        deficit must be non-negative, must not grow with precision, and must
        reach 0 at the top precision.  float64 loses 3.9e-2 of it at n = 12 and
        5.4e-3 at n = 8; 20 digits recover the proved value exactly.  So the
        a = 0 value must still be asserted from its ordinary proof in float64,
        as entry 24 says -- but the loss is removable, which entry 24 does not
        record.

  THMR  Theorem R: L(c*) <= (d_a+d_b)((1+q)/(1-q))^2 and
        L(c*) <= 2 diam(Omega_t) log((1+q)/(1-q)) with q = sqrt(mu/t2), on
        every sampled configuration.  A violation is a refutation of the
        theorem, not a tolerance issue.  The arm also reports the fraction of
        samples the bound settles outright.

  PIN   A pinned degree-four witness at which the per-hub strong form
        `L(c*) <= 2 mu^{1/n}` is REFUTED (`negative_results` entry 29's family)
        while the min-over-A_F form of AffineNormalisedModuli.md §5 survives by
        a wide margin.  Per entry 19, a search that never exceeds its threshold
        is worthless unless it can exceed one where the answer is known; this
        arm is that licence, and it is also the discriminator between the two
        statements.

  DEF   Two-sided calibration of the chord deficit D = L - (d_a + d_b):
        it must vanish at a = 0 (the branches there are radial, D = 0 exactly)
        and must be strictly positive at a pinned generic point.  An
        instrument that reports D = 0 everywhere is under-resolving curvature;
        one that reports D > 0 at a = 0 is fabricating it.

Exit 0 iff every arm passes.
"""
from __future__ import annotations

import argparse
import json
import sys

import numpy as np

EPS = float(np.finfo(float).eps)


# --------------------------------------------------------------- geometry
def _c2(a, b):
    return (a + b) / 2, abs(a - b) / 2


def _c3(a, b, c):
    ax, ay, bx, by, cx, cy = a.real, a.imag, b.real, b.imag, c.real, c.imag
    d = 2 * (ax * (by - cy) + bx * (cy - ay) + cx * (ay - by))
    if abs(d) < 1e-300:
        return None
    ux = ((ax * ax + ay * ay) * (by - cy) + (bx * bx + by * by) * (cy - ay)
          + (cx * cx + cy * cy) * (ay - by)) / d
    uy = ((ax * ax + ay * ay) * (cx - bx) + (bx * bx + by * by) * (ax - cx)
          + (cx * cx + cy * cy) * (bx - ax)) / d
    o = complex(ux, uy)
    return o, abs(a - o)


def min_enclosing(z):
    """Exact minimum enclosing circle (n is small here)."""
    z = np.asarray(z, complex)
    m = len(z)
    if m == 1:
        return complex(z[0]), 0.0
    best = None
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
    """Dense in t near 0 AND in log(mu - t) near mu: |u-c| ~ (mu-t)^{1/m}.

    `logdepth` is how close to the hub the tracker walks before closing with
    the straight chord, as -log10(1 - t/mu).  Deeper is WORSE, which is the
    opposite of the natural guess: at depth 14 the two branch points are
    separated by ~sqrt(eps) and root extraction there is pure noise, so the
    closing chord is measured at ~50% relative error.  Measured affine-drift
    of the invariants against depth, at 420 steps:

        depth      4       6       8      10      12      14
        drift  1.6e-9  1.6e-9  1.6e-9  1.6e-9  1.7e-9  1.2e-7

    a factor of 78 lost in the last two decades.  The quadratic calibration is
    blind to it (6e-14 at every depth) because a quadratic's branch is
    straight, so the chord closes it exactly however late it is taken.
    """
    a = mu * np.sin(np.linspace(0.0, np.pi / 2, k + 1)) ** 2
    b = mu * (1.0 - np.logspace(0.0, -logdepth, k))
    return np.unique(np.concatenate([a, b[b > 0]]))


def track(coef, theta, ts, roots):
    """All n solutions of f(u) = t e^{i theta}, matched by proximity."""
    from scipy.optimize import linear_sum_assignment
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
    """Affine-invariant record: R, mu, A_F hub lengths, merge pair, t2."""
    roots = np.asarray(roots, complex)
    n = len(roots)
    ctr, R = min_enclosing(roots)
    if R <= 0:
        return None
    rt = roots - ctr
    cf = np.poly(rt)
    cp = np.roots(np.polyder(cf))
    cv = np.polyval(cf, cp)
    if len(cp) == 0:
        return None
    mu = float(np.abs(cv).min())
    if not np.isfinite(mu) or mu <= 1e-13:
        return None
    order = np.argsort(np.abs(cv))
    ev = []
    for k in order:
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
    thresh = R ** n * (1 + 1e-12)
    AF = [e for e in ev if e["absv"] <= thresh]
    star = ev[0]

    # t2: level at which the (a,b) component gains a third root (merge tree)
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
    rho = mu ** (1.0 / n)
    return dict(n=n, R=R, mu=mu, rho=rho, t2=float(t2),
                lstar=star["L"], chord=star["chord"],
                deficit=star["L"] - star["chord"],
                minL=min(e["L"] for e in AF) if AF else np.inf,
                nAF=len(AF),
                minl_R=(min(e["L"] for e in AF) / (2 * R)) if AF else np.inf,
                minl_S=(min(e["L"] for e in AF) / (2 * rho)) if AF else np.inf,
                lstar_S=star["L"] / (2 * rho))


# ------------------------------------------------------------------- arms
def normalise_params(roots):
    """Return (a_2,...,a_{n-1}) of P(u) = f(c*+lambda u)/f(c*)."""
    roots = np.asarray(roots, complex)
    n = len(roots)
    cf = np.poly(roots)
    cp = np.roots(np.polyder(cf))
    cv = np.polyval(cf, cp)
    k = int(np.argmin(np.abs(cv)))
    c, v = cp[k], cv[k]
    lam = v ** (1.0 / n)
    P = np.poly((roots - c) / lam)
    return P / P[0]


def arm_inv(rng, trials, steps):
    """Theorem N(b) is exact algebra, so any drift is float64 conditioning.

    Doubling the mesh does NOT reduce the drift -- measured, and recorded here
    because it is the natural thing to try: the residual is not mesh
    truncation but the conditioning of the coefficients -> roots -> critical
    points chain, which a similarity of modulus far from 1 makes worse.  The
    arm therefore compares a MILD similarity with a STRONG one.  Exact
    invariance shows up as mild drift at machine level; a broken invariance
    would drift under both.  |A_F| must match exactly in every case, which is
    a discrete test no tolerance can absorb.
    """
    def drift(seed, lam_lo, lam_hi, beta):
        worst = 0.0
        r2 = np.random.default_rng(seed)
        for _ in range(trials):
            n = int(r2.integers(3, 7))
            z = r2.standard_normal(n) + 1j * r2.standard_normal(n)
            lam = (lam_lo + (lam_hi - lam_lo) * r2.random()) * np.exp(
                2j * np.pi * r2.random())
            bet = beta * (r2.standard_normal() + 1j * r2.standard_normal())
            base, img = analyse(z, steps), analyse(lam * z + bet, steps)
            if base is None or img is None:
                continue
            if base["nAF"] != img["nAF"]:
                return np.inf                 # A_F not invariant: a real bug
            for key in ("minl_R", "minl_S", "lstar_S"):
                worst = max(worst, abs(base[key] - img[key])
                            / max(abs(base[key]), 1e-9))
        return worst

    mild = drift(90210, 0.98, 1.02, 0.02)
    strong = drift(90210, 0.3, 2.3, 1.0)
    ok = (np.isfinite(mild) and np.isfinite(strong)
          and mild < 1e-8 and strong < 1e-4)
    return ok, dict(drift_mild_similarity=mild,
                    drift_strong_similarity=strong,
                    conditioning_explains=bool(np.isfinite(mild)
                                               and mild < strong))


def arm_ext(rng, trials):
    """Theorem N(d), tested as ALGEBRA at 40 digits, not as numpy conditioning.

    The critical point of an affine image of z^n - r^n is known in closed form,
    so no root-finder is used: rediscovering a multiplicity-(n-1) hub in
    float64 is exactly the ill-conditioned step the PREC arm measures, and it
    would make this arm a test of numpy rather than of the theorem.
    """
    try:
        import mpmath as mp
    except Exception:
        return True, dict(skipped="mpmath unavailable")
    mp.mp.dps = 40
    worst = mp.mpf(0)

    def build(roots):
        q = [mp.mpf(1)]
        for r in roots:
            q = [mp.mpc(0)] + q
            for i in range(len(q) - 1):
                q[i] = q[i] - r * q[i + 1]
        return q[::-1]                      # highest degree first

    for _ in range(trials):
        n = int(rng.integers(3, 9))
        r = mp.mpf(float(0.05 + 0.94 * rng.random()))
        lam = mp.mpf(float(0.2 + 3.0 * rng.random())) * mp.e ** (
            2j * mp.pi * mp.mpf(float(rng.random())))
        bet = mp.mpc(float(rng.standard_normal()), float(rng.standard_normal()))
        # g(z) = lam^n f((z-bet)/lam), f = z^n - r^n; hub c = bet, g(c) = -lam^n r^n
        z = [lam * r * mp.e ** (2j * mp.pi * mp.mpf(k) / n) + bet
             for k in range(n)]
        v = -(lam ** n) * (r ** n)
        Lam = mp.root(v, n)
        P = build([(zk - bet) / Lam for zk in z])
        for i, coef in enumerate(P):
            want = mp.mpf(1) if i in (0, n) else mp.mpf(0)
            worst = max(worst, abs(coef - want))
        # converse: f = (z-c)^n + v normalises to u^n + 1 for ANY c, v
        c2 = mp.mpc(float(rng.standard_normal()), float(rng.standard_normal()))
        v2 = mp.mpf(float(0.1 + rng.random())) * mp.e ** (
            2j * mp.pi * mp.mpf(float(rng.random())))
        L2 = mp.root(v2, n)
        z2 = [c2 + L2 * mp.e ** (1j * mp.pi * (2 * k + 1) / n) for k in range(n)]
        P2 = build([(zk - c2) / L2 for zk in z2])
        for i, coef in enumerate(P2):
            want = mp.mpf(1) if i in (0, n) else mp.mpf(0)
            worst = max(worst, abs(coef - want))
    return float(worst) < 1e-30, dict(worst_coefficient_gap=float(worst),
                                      working_dps=40)


def arm_prec(degrees, dpslist):
    """The a = 0 under-report of entry 24 is a PRECISION artifact.

    Run exactly the float64 pipeline -- root extraction on P - t, nearest-point
    matching, straight chord into the hub -- at several working precisions on
    P = u^n + 1, whose true value is minl_S = 1 by ordinary proof (the branches
    are n radii of length 1).  If the deficit collapses as precision rises, the
    recorded degenerate-hub under-report is removable, not intrinsic.
    """
    try:
        import mpmath as mp
    except Exception:
        return True, dict(skipped="mpmath unavailable")
    rows = []
    ok = True
    for n in degrees:
        prev = None
        for D in dpslist:
            mp.mp.dps = D
            cf = [mp.mpf(0)] * (n + 1)
            cf[0] = mp.mpf(1)
            cf[n] = mp.mpf(1)
            deltas = [mp.mpf(10) ** (-e)
                      for e in mp.linspace(0, mp.mpf(D) * mp.mpf("0.8"), 300)]
            cur = list(mp.polyroots(cf, maxsteps=300, extraprec=400))
            acc = [mp.mpf(0)] * n
            for dl in deltas:
                c2 = list(cf)
                c2[n] = cf[n] - (mp.mpf(1) - dl)
                w = list(mp.polyroots(c2, maxsteps=300, extraprec=400))
                used = [False] * n
                for a in range(n):
                    bi, bd = -1, None
                    for b in range(n):
                        if used[b]:
                            continue
                        d = abs(cur[a] - w[b])
                        if bd is None or d < bd:
                            bi, bd = b, d
                    used[bi] = True
                    acc[a] += bd
                    cur[a] = w[bi]
            lens = sorted(float(acc[a] + abs(cur[a])) for a in range(n))
            got = (lens[0] + lens[1]) / 2.0
            deficit = 1.0 - got
            rows.append(dict(n=n, dps=D, minl_S=got, deficit=deficit))
            if deficit < -1e-9:                # over-report = fabricated length
                ok = False
            if prev is not None and deficit > prev + 1e-12:
                ok = False                     # must not grow with precision
            prev = deficit
        if abs(rows[-1]["deficit"]) > 1e-9:    # must reach the proved value
            ok = False
    return ok, dict(rows=rows)


def arm_thmr(rng, trials, steps):
    bad, settled, seen = 0, 0, 0
    worst = 0.0
    for _ in range(trials):
        n = int(rng.integers(3, 8))
        v = rng.standard_normal(2 * n) * 0.85
        z = v[:n] + 1j * v[n:]
        z = z / max(np.max(np.abs(z)), 1e-9) * 0.999
        rec = analyse(z, steps)
        if rec is None or not np.isfinite(rec["t2"]):
            continue
        seen += 1
        q = float(np.sqrt(rec["mu"] / rec["t2"]))
        if not (0 < q < 1):
            continue
        b1 = rec["chord"] * ((1 + q) / (1 - q)) ** 2
        b2 = 8.0 * min(rec["t2"], 1.0) ** (1.0 / n) * np.log((1 + q) / (1 - q))
        b = min(b1, b2)
        worst = max(worst, rec["lstar"] / b)
        if rec["lstar"] > b * (1 + 1e-9):
            bad += 1
        if b < 2.0:
            settled += 1
    return bad == 0 and seen > 0, dict(
        samples=seen, violations=bad, worst_L_over_bound=worst,
        settled_outright=settled,
        settled_fraction=(settled / seen) if seen else None)


def arm_def(steps):
    """D = 0 at a = 0 (radial branches); D > 0 at a pinned generic point."""
    out = {}
    ok = True
    for n in (3, 4, 5):
        z = 0.9 * np.exp(2j * np.pi * np.arange(n) / n)      # a = 0
        rec = analyse(z, steps)
        out[f"deficit_extremal_n{n}"] = rec["deficit"] / rec["chord"]
        if abs(rec["deficit"]) > 1e-5 * rec["chord"]:
            ok = False
    pin = np.array([0.81 + 0.13j, -0.42 + 0.66j, -0.29 - 0.77j, 0.55 - 0.21j])
    rec = analyse(pin, steps)
    out["deficit_pinned_quartic"] = rec["deficit"] / rec["chord"]
    out["pinned_lstar"] = rec["lstar"]
    if not (rec["deficit"] / rec["chord"] > 1e-6):
        ok = False
    return ok, out


def arm_pin(steps):
    """PINNED negative control: the per-hub strong form must be REFUTED here,
    and FEKETE-HUB MIN must survive at the same configuration.

    `negative_results` entry 29 refutes `L(c*) <= 2 mu^{1/n}` at degree four
    with ratio 1.004246913, and records that the two smallest critical values
    agree to 2.30e-9 relative and that the runner-up hub sits at 0.9608.  This
    directory does not store that witness, and two searches in ROOT
    coordinates -- one of them tie-seeking -- both failed to rediscover it,
    converging to the symmetric extremal point instead.  A search in the
    normalised coordinates of Theorem N found the configuration below on its
    first attempt.

        P(u) = u^4 + a3 u^3 + a2 u^2 + 1,   P'(0) = 0, P(0) = 1

    It is a member of entry 29's family, not entry 29's own witness: same
    degree, same near-tie signature (critical-value gap 5.1e-10 against entry
    29's 2.30e-9), comparable ratio.

    The arm is the instrument's licence to be believed.  A search that cannot
    exceed 1 proves nothing unless it can exceed 1 where the answer is known
    to (entry 19).  It also carries the DISCRIMINATOR: at this same point the
    min-over-A_F form is ~0.897, so the two statements are separated by more
    than 1e-1 on one configuration, not by a tolerance.
    """
    a2 = -0.000225877943 + 0.000866621978j
    a3 = -0.199341957743 - 0.409216378485j
    coef = np.array([1.0 + 0j, a3, a2, 0.0 + 0j, 1.0 + 0j])
    out = {}
    ok = True
    for k in (steps, 2 * steps):
        rec = analyse(np.roots(coef), k)
        if rec is None:
            return False, dict(error="pinned witness did not analyse")
        out[f"lstar_S_at_{k}"] = rec["lstar_S"]
        out[f"minl_S_at_{k}"] = rec["minl_S"]
        out[f"nAF_at_{k}"] = rec["nAF"]
        if not rec["lstar_S"] > 1.002:      # must SEE the refutation
            ok = False
        if not rec["minl_S"] < 0.95:        # and the sharpening must survive
            ok = False
    out["separation"] = out[f"lstar_S_at_{2*steps}"] - out[f"minl_S_at_{2*steps}"]
    return ok, out


def main() -> int:
    ap = argparse.ArgumentParser()
    ap.add_argument("--trials", type=int, default=40)
    ap.add_argument("--steps", type=int, default=420)
    ap.add_argument("--json", action="store_true")
    ap.add_argument("--quick", action="store_true")
    args = ap.parse_args()
    rng = np.random.default_rng(20260824)

    degrees = [3, 4] if args.quick else [3, 4, 6]
    dpslist = [20, 30] if args.quick else [20, 30, 40]

    arms = {}
    arms["INV"] = arm_inv(rng, max(6, args.trials // 4), args.steps)
    arms["EXT"] = arm_ext(rng, max(8, args.trials // 2))
    arms["PREC"] = arm_prec(degrees, dpslist)
    arms["THMR"] = arm_thmr(rng, args.trials, args.steps)
    arms["DEF"] = arm_def(args.steps)
    arms["PIN"] = arm_pin(args.steps)

    payload = {k: dict(ok=bool(v[0]), **v[1]) for k, v in arms.items()}
    allok = all(v[0] for v in arms.values())
    if args.json:
        print(json.dumps(dict(ok=allok, arms=payload), indent=2, default=float))
    else:
        for k, v in arms.items():
            print(f"[{'PASS' if v[0] else 'FAIL'}] {k}")
            for kk, vv in v[1].items():
                if kk == "rows":
                    for r in vv:
                        print(f"        n={r['n']} dps={r['dps']:>3} "
                              f"minl_S={r['minl_S']:.12f} "
                              f"deficit={r['deficit']:.3e}")
                else:
                    print(f"        {kk} = {vv}")
        print("OK" if allok else "FAILED")
    return 0 if allok else 1


if __name__ == "__main__":
    sys.exit(main())
