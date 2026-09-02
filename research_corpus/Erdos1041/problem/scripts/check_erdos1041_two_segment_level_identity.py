#!/usr/bin/env python3
"""Erdos #1041: the two-segment mechanism is level-optimal, and its threshold is Fekete's.

Five arms, all fail-closed.

  floor      V_E >= mu is a THEOREM (sec 2 of TwoSegmentLevelIdentity.md); this arm only
             checks the instrument never reports below it.
  identity   V_E == mu measured over four root families.  V_E is the ellipse-restricted
             infimum over hubs of max|f| on the two segments; mu = min_c |f(c)|.
  fekete     mu <= R^n, from disc(f) = (-1)^... n^n prod_c f(c) and the Fekete bound
             prod_{i<j}|z_i-z_j| <= n^{n/2} on the closed unit disk.
  extremal   Lambda(z^n - 1) = 2 exactly, via the closed-form petal decomposition
             {|z^n-1| <= 1} = {0} u {rho^n <= 2 cos(n theta)}.
  degeneracy The float64 trap: at z^n - 1 the excess |f(h)| - 1 is Theta(|h|^n) near the
             origin, so for |h| >~ 10^{-16/n} an infeasible hub reads as feasible.  The arm
             requires float64 to accept a hub that mpmath rejects, then requires mpmath to
             reject it.  If float64 ever stopped being fooled this arm fails, which is the
             point: it pins the defect rather than the symptom.

Segment maxima are never sampled: max_{t in [0,1]} |f(h+t(a-h))|^2 is the maximum of an
explicit real polynomial of degree 2n, taken over the real roots of its derivative and the
two endpoints.
"""
from __future__ import annotations

import argparse
import itertools
import json
import sys
from pathlib import Path

import numpy as np

REPO = Path(__file__).resolve().parents[5]
RECEIPT = REPO / "state" / "formal_math" / "erdos257_period_noncollapse" / \
    "erdos1041_two_segment_level_identity_receipt.json"

# --------------------------------------------------------------------------- exact segment max


def seg_poly(roots: np.ndarray, h: complex, a: complex) -> np.ndarray:
    """ascending real coefficients of g(t) = |f(h + t(a-h))|^2, degree 2n."""
    d = a - h
    coef = np.array([1.0 + 0j])
    for z in roots:
        new = np.zeros(len(coef) + 1, dtype=complex)
        new[:-1] += (h - z) * coef
        new[1:] += d * coef
        coef = new
    return np.convolve(coef, np.conj(coef)).real


def segmax(roots: np.ndarray, h: complex, a: complex) -> float:
    g = seg_poly(roots, h, a)
    dg = g[1:] * np.arange(1, len(g))
    ts = [0.0, 1.0]
    if dg.size and np.any(dg != 0):
        for x in np.roots(dg[::-1]):
            if abs(x.imag) < 1e-9 and -1e-12 < x.real < 1 + 1e-12:
                ts.append(min(1.0, max(0.0, float(x.real))))
    return float(np.sqrt(max(max(np.polyval(g[::-1], t) for t in ts), 0.0)))


def pair_obj(roots: np.ndarray, h: complex, a: complex, b: complex) -> float:
    return max(segmax(roots, h, a), segmax(roots, h, b))


# --------------------------------------------------------------------------- hub search


def ellipse_grid(a: complex, b: complex, cap: float, m: int) -> np.ndarray:
    ctr = 0.5 * (a + b)
    c = 0.5 * abs(a - b)
    A = cap / 2.0
    B = float(np.sqrt(max(A * A - c * c, 0.0)))
    u = 1.0 + 0j if abs(a - b) < 1e-14 else (b - a) / abs(b - a)
    s = np.linspace(-1, 1, m)
    P = [ctr + u * (A * x + 1j * B * y) for x in s for y in s if x * x + y * y <= 1.0]
    return np.array(P) if P else np.zeros(0, dtype=complex)


def sampled_scores(roots: np.ndarray, a: complex, b: complex, H: np.ndarray, K: int) -> np.ndarray:
    t = np.linspace(0.0, 1.0, K)
    out = None
    for e in (a, b):
        Z = H[:, None] + t[None, :] * (e - H[:, None])
        d = np.abs(Z[:, :, None] - roots[None, None, :])
        np.maximum(d, 1e-300, out=d)
        v = np.log(d).sum(axis=2).max(axis=1)
        out = v if out is None else np.maximum(out, v)
    return np.exp(out)


def inner_min(roots, a, b, cap=2.0, m=29, rounds=45, K=56, rng=None):
    rng = rng or np.random.default_rng(0)
    P = ellipse_grid(a, b, cap, m)
    if not len(P):
        return np.inf, None
    v = sampled_scores(roots, a, b, P, K)
    k = int(np.argmin(v))
    best, bh = float(v[k]), P[k]
    rad = cap / (2.0 * (m - 1)) * 2.5
    for _ in range(rounds):
        C = bh + rad * (rng.normal(size=64) + 1j * rng.normal(size=64))
        C = C[(np.abs(C - a) + np.abs(C - b)) <= cap]
        if len(C):
            vv = sampled_scores(roots, a, b, C, K)
            k = int(np.argmin(vv))
            if vv[k] < best:
                best, bh = float(vv[k]), C[k]
        rad *= 0.90
    return best, bh


def V_ellipse(roots, cap=2.0, m=29, rounds=45, K=56, seed=0):
    """ellipse-restricted inf over hubs of max|f| on the two segments (exact re-score)."""
    rng = np.random.default_rng(seed)
    best, arg = np.inf, None
    for i, j in itertools.combinations(range(len(roots)), 2):
        _, h = inner_min(roots, roots[i], roots[j], cap, m, rounds, K, rng)
        if h is None:
            continue
        v = pair_obj(roots, h, roots[i], roots[j])
        if v < best:
            best, arg = v, (i, j, complex(h))
    return best, arg


def mu_of(roots: np.ndarray) -> float:
    p = np.poly(roots)
    return float(np.abs(np.polyval(p, np.roots(np.polyder(p)))).min())


def miniball(z: np.ndarray, iters: int = 6000) -> complex:
    c = complex(z.mean())
    for k in range(iters):
        c = c + (z[int(np.argmax(np.abs(z - c)))] - c) / (k + 2)
    return c


def family(kind: str, n: int, rng) -> np.ndarray:
    if kind == "unif":
        return np.sqrt(rng.uniform(0, 1, n)) * np.exp(2j * np.pi * rng.uniform(0, 1, n))
    if kind == "bdry":
        return rng.uniform(0.95, 1.0, n) * np.exp(2j * np.pi * rng.uniform(0, 1, n))
    if kind == "poly":
        w = np.exp(2j * np.pi * np.arange(n) / n)
        return w * rng.uniform(0.97, 1.0) * np.exp(1j * rng.normal(0, 0.05, n))
    k = max(2, n // 3)
    c = np.sqrt(rng.uniform(0, 1, k)) * np.exp(2j * np.pi * rng.uniform(0, 1, k))
    z = np.array([c[i % k] + 0.08 * (rng.normal() + 1j * rng.normal()) for i in range(n)])
    return np.where(np.abs(z) > 1, z / np.abs(z), z)


# --------------------------------------------------------------------------- arms


def arm_floor(rng) -> dict:
    worst, rows = 0.0, 0
    for kind in ("unif", "bdry", "poly", "clus"):
        for n in (3, 4, 5, 6):
            for _ in range(2):
                z = family(kind, n, rng)
                v, _ = V_ellipse(z, seed=rows)
                worst = max(worst, mu_of(z) / v)
                rows += 1
    return {"rows": rows, "worst_mu_over_V": worst, "ok": worst <= 1 + 1e-6}


def arm_identity(rng, degrees=(3, 4, 5, 6, 8), reps=3) -> dict:
    worst, rows, detail = 0.0, 0, []
    for kind in ("unif", "bdry", "poly", "clus"):
        for n in degrees:
            for t in range(reps):
                z = family(kind, n, rng)
                mu = mu_of(z)
                v, arg = V_ellipse(z, seed=t)
                r = v / mu
                worst = max(worst, r)
                rows += 1
                if r > 1 + 1e-4:
                    detail.append({"kind": kind, "n": n, "mu": mu, "V": v, "ratio": r})
    return {"rows": rows, "worst_V_over_mu": worst, "outliers": detail,
            "ok": worst <= 1 + 1e-4}


def arm_fekete(rng) -> dict:
    worst, rows = 0.0, 0
    for kind in ("unif", "bdry", "poly", "clus"):
        for n in (3, 4, 5, 6, 8, 10):
            for _ in range(4):
                z = family(kind, n, rng)
                R = float(np.abs(z - miniball(z)).max())
                if R < 1e-9:
                    continue
                worst = max(worst, mu_of(z) / R ** n)
                rows += 1
    return {"rows": rows, "worst_mu_over_Rn": worst, "ok": worst <= 1 + 1e-8}


def arm_extremal(degrees=(2, 3, 4, 5, 6, 8, 10, 12)) -> dict:
    """Lambda(z^n - 1) = 2 exactly.  Three exact checks, no search and no grid.

    (a) the petal decomposition is the algebraic identity
        |z^n - 1|^2 - 1 = rho^n (rho^n - 2 cos n theta),  rho = |z|, theta = arg z,
        so the set minus the origin is {rho^n <= 2 cos n theta}, which is n disjoint sectors
        of half-angle pi/(2n) about the roots (spacing 2pi/n);
    (b) the origin hub is feasible with total length exactly 2;
    (c) the whole open bisector ray between two adjacent roots is OUTSIDE the set:
        there theta = pi/n so n theta = pi and |f(s e^{i pi/n})| = 1 + s^n > 1 for s > 0.
        This is the mechanism of the lower bound -- the petals meet only at 0 -- and it is
        exact in closed form, so no float64 tolerance enters.
    """
    rows, ok = [], True
    for n in degrees:
        roots = np.exp(2j * np.pi * np.arange(n) / n)
        rng = np.random.default_rng(n)
        rho = rng.uniform(1e-3, 1.3, 4000)
        th = rng.uniform(0, 2 * np.pi, 4000)
        zz = rho * np.exp(1j * th)
        ident = float(np.max(np.abs((np.abs(zz ** n - 1.0) ** 2 - 1.0)
                                    - rho ** n * (rho ** n - 2 * np.cos(n * th)))
                             / (1.0 + np.abs(rho ** n * (rho ** n - 2 * np.cos(n * th))))))
        att = max(segmax(roots, 0j, roots[0]), segmax(roots, 0j, roots[1]))
        length = abs(roots[0]) + abs(roots[1])
        # (c) closed form on the bisector: |f| = |s^n e^{i pi} - 1| = 1 + s^n
        s = np.linspace(1e-4, 1.2, 2000)
        bis = np.abs((s * np.exp(1j * np.pi / n)) ** n - 1.0)
        bis_resid = float(np.max(np.abs(bis - (1.0 + s ** n))))
        # strictness is exact (1 + s^n > 1 for s > 0) but is BELOW float64 resolution
        # once s^n < eps -- the same degeneracy the `degeneracy` arm pins -- so the
        # numeric arm asserts only the closed form plus non-strict exclusion.
        bis_excluded = bool((bis >= 1.0).all())
        rows.append({"n": n, "identity_resid": ident, "origin_hub_max_abs_f": att,
                     "origin_hub_length": length, "bisector_closed_form_resid": bis_resid,
                     "bisector_excluded": bis_excluded})
        ok &= (ident < 1e-12) and (att <= 1 + 1e-12) and (abs(length - 2.0) < 1e-12) \
            and (bis_resid < 1e-12) and bis_excluded
    return {"rows": rows, "ok": ok}


def arm_degeneracy() -> dict:
    """float64 must be fooled where mpmath is not; both halves are required."""
    try:
        import mpmath as mp
    except Exception:
        return {"ok": False, "reason": "mpmath unavailable"}
    mp.mp.dps = 80
    n = 10
    roots = np.exp(2j * np.pi * np.arange(n) / n)
    # a hub on the bisector between two adjacent roots: provably OUTSIDE {|f|<=1}
    h = 0.02 * np.exp(1j * (2 * np.pi / n) * 0.5)
    f64 = float(np.abs(np.prod(h - roots)))
    hm = mp.mpc(h.real, h.imag)
    exact = mp.fabs(mp.mpc(1) * mp.fprod([hm - mp.mpc(z.real, z.imag) for z in roots]))
    excess = float(exact - 1)
    fooled = abs(f64 - 1.0) <= 1e-15          # float64 sees no excess
    caught = excess > 0                        # mpmath sees a real one
    return {"n": n, "hub_abs": float(abs(h)), "float64_abs_f": f64,
            "mp_excess": excess, "predicted_scale": float(abs(h) ** n),
            "float64_fooled": fooled, "mpmath_caught": caught,
            "ok": bool(fooled and caught)}


def _max_on(g, lo, hi):
    dg = g[1:] * np.arange(1, len(g))
    cand = [lo, hi]
    if dg.size and np.any(dg != 0):
        for x in np.roots(dg[::-1]):
            if abs(x.imag) < 1e-9 and lo - 1e-12 < x.real < hi + 1e-12:
                cand.append(min(hi, max(lo, float(x.real))))
    return max(np.polyval(g[::-1], t) for t in cand)


def best_interior_spoke(z, delta=1e-3):
    """min over roots of  max_{t <= 1-delta} |f| on [z_k, c*]  /  mu.

    A sublevel-contained spoke has its maximum AT the endpoint c*, where |f| = mu
    exactly, so the naive ratio is identically 1 and an adversarial search has
    nothing to move.  Excising the endpoint makes the objective informative: the
    value is < 1 iff some spoke is contained.
    """
    p = np.poly(z)
    cs = np.roots(np.polyder(p))
    fv = np.abs(np.polyval(p, cs))
    k = int(np.argmin(fv))
    c, mu = cs[k], float(fv[k])
    if mu <= 0:
        return None
    return float(min(np.sqrt(max(_max_on(seg_poly(z, w, c), 0.0, 1.0 - delta), 0.0)) / mu
                     for w in z))


def arm_spoke(rng, degrees=(3, 4, 5, 6, 8), restarts=3, iters=200) -> dict:
    """(SPOKE>=1): at c*, at least one straight spoke to a root is sublevel-contained.

    Necessary for the level identity: a two-segment path at level mu must cross the
    neck at c*, so one of its segments contains c* and the sub-segment from its root
    to c* is a contained spoke.
    """
    rows, worst = [], 0.0
    for n in degrees:
        best = 0.0
        for s in range(restarts):
            r = np.random.default_rng(1000 * n + s)
            cur = r.uniform(0.5, 1.0, n) * np.exp(2j * np.pi * r.uniform(0, 1, n))
            cv = best_interior_spoke(cur) or 0.0
            step = 0.3
            for it in range(iters):
                k = r.integers(0, n)
                cand = cur.copy()
                cand[k] += step * (r.normal() + 1j * r.normal())
                if abs(cand[k]) > 1:
                    cand[k] /= abs(cand[k])
                v = best_interior_spoke(cand)
                if v is not None and v > cv:
                    cur, cv = cand, v
                if (it + 1) % 40 == 0:
                    step *= 0.75
            best = max(best, cv)
        rows.append({"n": n, "sup_best_interior_ratio": best})
        worst = max(worst, best)
    return {"rows": rows, "sup": worst, "ok": worst <= 1.0}


# hexagon perturbed by at most 3.00 degrees; only ONE radius stays inside {|f| <= 1}
NEAR_FEKETE_HEX_ETA = [
    0.00173207975211076, -0.01636641293505736, 0.01474617820591595,
    0.01950276945344509, -0.05244827523897744, 0.032833660762563,
]


def arm_originhub() -> dict:
    """The centre hub is not stable at the Fekete configuration.

    Two halves, both required.
    (1) the exact radial product identity for roots on the unit circle,
        prod_j |f(t z_j)| = exp( - sum_m t^m |p_m|^2 / m )  <=  1;
    (2) an explicit hexagon perturbed by <= 3 degrees on which only ONE of the six
        radii stays inside {|f| <= 1}, so the origin hub carries no two-segment path.
    """
    ident = 0.0
    rng = np.random.default_rng(7)
    for n in (3, 5, 8):
        z = np.exp(1j * (2 * np.pi * np.arange(n) / n + rng.normal(0, 0.3, n)))
        for t in (0.3, 0.7, 0.95):
            lhs = float(np.prod([abs(np.prod(t * z[j] - z)) for j in range(n)]))
            rhs = float(np.exp(-sum(t ** m / m * abs((z ** m).sum()) ** 2
                                    for m in range(1, 3000))))
            ident = max(ident, abs(lhs - rhs) / rhs)
    eta = np.array(NEAR_FEKETE_HEX_ETA)
    z = np.exp(1j * (2 * np.pi * np.arange(6) / 6 + eta))
    rad = [segmax(z, 0j, z[j]) for j in range(6)]
    nsafe = sum(1 for v in rad if v <= 1 + 1e-11)
    second = float(sorted(rad)[1])
    return {"identity_rel_resid": ident, "hex_eta_max_deg": float(np.abs(eta).max() * 180 / np.pi),
            "hex_radial_maxima": [float(v) for v in rad], "hex_safe_radii": nsafe,
            "hex_second_smallest": second,
            "ok": bool(ident < 1e-12 and nsafe < 2 and second > 1 + 1e-5)}


def lambda_of(roots, m=121, K=90, cap=2.0, ntry=40):
    """cheapest feasible two-segment length: min |h-a|+|h-b| over hubs with max|f| <= 1.

    Feasibility of the returned hub is decided by the EXACT degree-2n segment maximum,
    so the value is an achieved upper bound on the true infimum.
    """
    best = np.inf
    for i, j in itertools.combinations(range(len(roots)), 2):
        a, b = roots[i], roots[j]
        H = ellipse_grid(a, b, cap, m)
        if not len(H):
            continue
        S = sampled_scores(roots, a, b, H, K)
        Hf = H[S <= 1.0]
        if not len(Hf):
            continue
        g = np.abs(Hf - a) + np.abs(Hf - b)
        for idx in np.argsort(g)[:ntry]:
            h = Hf[idx]
            if pair_obj(roots, h, a, b) <= 1.0:
                cur, bh = float(g[idx]), h
                rad = cap / (m - 1)
                rng = np.random.default_rng(int(1e6 * abs(a - b)) % 99991)
                for _ in range(50):
                    C = bh + rad * (rng.normal(size=24) + 1j * rng.normal(size=24))
                    for hc in C:
                        gc = abs(hc - a) + abs(hc - b)
                        if gc < cur and pair_obj(roots, hc, a, b) <= 1.0:
                            cur, bh = gc, hc
                    rad *= 0.93
                best = min(best, cur)
                break
    return best


def arm_cusp(n=4, epsvals=(1e-2, 1e-3, 1e-4)) -> dict:
    """The extremal is a CUSP maximum, with the critical-point splitting exponent.

    Breaking the Fekete degeneracy by an angular perturbation of size eps splits the
    n-1 critical points from the origin onto a ring of radius rho ~ (eps/n)^{1/(n-1)}
    (the near-Fekete cusp law's scale).  The two-segment hub has to follow them off the
    centre, and the length gain is linear in the hub displacement, so 2 - Lambda should
    be proportional to rho -- not merely of the same exponent.  The arm therefore checks
    the RATIO is constant, which is a much stronger statement than an exponent fit.
    """
    rng = np.random.default_rng(100 + n)
    d = rng.normal(0, 1, n)
    d = (d - d.mean())
    d /= np.linalg.norm(d)
    rows = []
    for e in epsvals:
        z = np.exp(1j * (2 * np.pi * np.arange(n) / n + e * d))
        L = lambda_of(z)
        rho = (e / n) ** (1.0 / (n - 1))
        rows.append({"eps": e, "Lambda": float(L), "gap": float(2 - L),
                     "rho": float(rho), "gap_over_rho": float((2 - L) / rho)})
    r = [x["gap_over_rho"] for x in rows]
    xs = np.log([x["eps"] for x in rows])
    ys = np.log([x["gap"] for x in rows])
    alpha = float(np.polyfit(xs, ys, 1)[0])
    spread = float(max(r) / min(r))
    return {"n": n, "rows": rows, "fitted_alpha": alpha, "target_1_over_n_minus_1": 1.0 / (n - 1),
            "ratio_spread": spread,
            "ok": bool(spread < 1.15 and abs(alpha - 1.0 / (n - 1)) < abs(alpha - 1.0 / n))}


def main() -> int:
    ap = argparse.ArgumentParser()
    ap.add_argument("--part", default="all",
                    choices=["all", "floor", "identity", "fekete", "extremal", "degeneracy", "spoke", "originhub", "cusp"])
    ap.add_argument("--seed", type=int, default=11)
    ap.add_argument("--json", action="store_true")
    args = ap.parse_args()

    out, ok = {}, True
    if args.part in ("all", "floor"):
        out["floor"] = arm_floor(np.random.default_rng(args.seed))
        ok &= out["floor"]["ok"]
    if args.part in ("all", "identity"):
        out["identity"] = arm_identity(np.random.default_rng(args.seed))
        ok &= out["identity"]["ok"]
    if args.part in ("all", "fekete"):
        out["fekete"] = arm_fekete(np.random.default_rng(args.seed + 1))
        ok &= out["fekete"]["ok"]
    if args.part in ("all", "extremal"):
        out["extremal"] = arm_extremal()
        ok &= out["extremal"]["ok"]
    if args.part in ("all", "spoke"):
        out["spoke"] = arm_spoke(np.random.default_rng(args.seed + 2))
        ok &= out["spoke"]["ok"]
    if args.part in ("all", "originhub"):
        out["originhub"] = arm_originhub()
        ok &= out["originhub"]["ok"]
    if args.part in ("all", "cusp"):
        out["cusp"] = arm_cusp()
        ok &= out["cusp"]["ok"]
    if args.part in ("all", "degeneracy"):
        out["degeneracy"] = arm_degeneracy()
        ok &= out["degeneracy"]["ok"]
    out["ok"] = bool(ok)

    if args.json:
        print(json.dumps(out, indent=1, default=float))
    else:
        for k, v in out.items():
            if k == "ok":
                continue
            print(f"[{k}] " + json.dumps({a: b for a, b in v.items() if a != "rows"}
                                         if isinstance(v, dict) else v, default=float)[:400])
        print("OK" if ok else "FAILED")
    if args.part == "all":
        RECEIPT.parent.mkdir(parents=True, exist_ok=True)
        RECEIPT.write_text(json.dumps(out, indent=1, default=float) + "\n")
    return 0 if ok else 1


if __name__ == "__main__":
    sys.exit(main())
