"""Erdős 1041: falsifier for the disk-family critical-value separation bound.

Normalisation.  At a simple non-root critical point c of a monic f of degree n
put rho = |f(c)|^(1/n) and P(w) = f(c + rho w)/f(c).  Then |lead P| = 1,
P(0) = 1, P'(0) = 0, and the other critical values of P are v_j = f(d_j)/f(c).
The canonical connector is Z([-1,1]) where P(Z(xi)) = 1 - xi^2, Z(0) = 0.

Claim under test (DiskFamilyCriticalValueSeparation.md).  For every real
w0 in [0,1] and every S > max(w0, 1-w0) with |v_j - w0| >= S for all j,

    len(Z([-1,1]))^2  <  2 (S/(n-1))^(2/n) log((S^2+S+p)/(S^2-S+p)),
    p = w0 (1-w0).

The probe

  * traces both descending branches of the connector by integrating
    dz/ds = -2 s / P'(z) with the exact series start, polishing with Newton;
  * evaluates the bound at a grid of centres w0 and the sharpest admissible
    S, records the worst ratio len/bound over every simple critical point of
    random, near-Fekete, clustered and boundary-heavy root configurations;
  * hill-climbs the ratio adversarially from the worst seeds;
  * estimates Area(U) for the two-sheeted component U on a grid and checks
    the exterior-fibre gap Area(U) < pi (S/(n-1))^(2/n);
  * prints the per-degree thresholds S_n^*(w0) and the residual lens.

Any ratio above 1 falsifies the theorem.  A ratio close to 1 measures its
sharpness.  Nothing here is proof authority.
"""

from __future__ import annotations

import argparse
import json
import math
import sys

import numpy as np
from scipy.integrate import solve_ivp

RNG = np.random.default_rng(20260902)


# --------------------------------------------------------------------------
# polynomial helpers
# --------------------------------------------------------------------------


def poly_from_roots(roots):
    return np.poly(roots)  # monic, highest degree first


def critical_points(coeffs):
    return np.roots(np.polyder(coeffs))


def normalise_at_hub(coeffs, c):
    """Return (Pcoeffs, rho, v_others) for the hub c."""
    n = len(coeffs) - 1
    fc = np.polyval(coeffs, c)
    rho = abs(fc) ** (1.0 / n)
    # P(w) = f(c + rho w)/fc : compose
    # coefficients of f(c + rho w) via Taylor shift
    shifted = np.polynomial.polynomial.polyfromroots(
        (np.roots(coeffs) - c) / rho
    )[::-1]  # monic in w with roots (a_i - c)/rho
    # f(c + rho w) = rho^n prod (w - (a_i-c)/rho)
    P = shifted * (rho**n) / fc
    crit = critical_points(P)
    # remove the hub (0) itself: keep those with |d| not tiny
    vals = []
    for d in crit:
        if abs(d) < 1e-9:
            continue
        vals.append(np.polyval(P, d))
    return P, rho, np.array(vals)


def branch_length(P, sign, tol=1e-11):
    """Length of one branch Z(xi), xi in [0,1] (sign=+1) or [-1,0]."""
    dP = np.polyder(P)
    d2P = np.polyder(dP)
    A = np.polyval(d2P, 0.0) / 2.0  # P = 1 + A z^2 + ...
    if abs(A) < 1e-14:
        return math.nan
    # series start: z ~ sign * s / sqrt(-A)
    s0 = 1e-4
    root_negA = np.sqrt(-A + 0j)
    z0 = sign * s0 / root_negA
    # polish z0 so that P(z0) = 1 - s0^2 on the correct branch
    for _ in range(20):
        F = np.polyval(P, z0) - (1 - s0**2)
        dF = np.polyval(dP, z0)
        if abs(dF) < 1e-300:
            break
        z0 = z0 - F / dF
    length0 = abs(z0)  # tiny straight start

    def rhs(s, y):
        z = y[0] + 1j * y[1]
        dz = -2.0 * s / np.polyval(dP, z)
        return [dz.real, dz.imag, abs(dz)]

    sol = solve_ivp(
        rhs,
        (s0, 1.0),
        [z0.real, z0.imag, 0.0],
        method="DOP853",
        rtol=tol,
        atol=tol,
        max_step=5e-3,
    )
    zend = sol.y[0, -1] + 1j * sol.y[1, -1]
    resid = abs(np.polyval(P, zend))
    return sol.y[2, -1] + length0, zend, resid


def connector_length(P):
    Lp, zp, rp = branch_length(P, +1)
    Lm, zm, rm = branch_length(P, -1)
    ok = (rp < 1e-6) and (rm < 1e-6) and abs(zp - zm) > 1e-6
    return Lp + Lm, ok, (zp, zm)


# --------------------------------------------------------------------------
# the bound
# --------------------------------------------------------------------------


def coefficient(n, S, p):
    """C(n,S,p) = (S/(n-1))^(2/n) log((S^2+S+p)/(S^2-S+p))."""
    return (S / (n - 1)) ** (2.0 / n) * math.log((S * S + S + p) / (S * S - S + p))


def old_coefficient(n, S):
    return (1 + S) ** (2.0 / n) * math.log(S / (S - 1))


def best_bound(n, vals, w0_grid):
    """Return (best_len_bound, best_w0, best_S, old_bound_at_w0=1)."""
    best = (math.inf, None, None)
    old = math.inf
    for w0 in w0_grid:
        need = max(w0, 1 - w0)
        if len(vals) == 0:
            S = 1e6
        else:
            S = float(np.min(np.abs(vals - w0)))
        if S <= need + 1e-12:
            continue
        p = w0 * (1 - w0)
        b = math.sqrt(2.0 * coefficient(n, S, p))
        if b < best[0]:
            best = (b, w0, S)
        if abs(w0 - 1.0) < 1e-12 and S > 1:
            old = 2.0 * math.sqrt(old_coefficient(n, S))
    return best, old


def threshold_S(n, p, lo=None, hi=50.0):
    """Smallest S with C(n,S,p) < 2, via bisection (C decreasing in S)."""
    if lo is None:
        lo = 0.5 * (1 + math.sqrt(1 - 4 * p)) + 1e-5  # S^2-S+p>0 boundary
    f = lambda S: coefficient(n, S, p) - 2.0
    if f(hi) > 0:
        return math.inf
    a, b = lo, hi
    if f(a) < 0:
        return a
    for _ in range(200):
        m = 0.5 * (a + b)
        if f(m) > 0:
            a = m
        else:
            b = m
    return b


# --------------------------------------------------------------------------
# configurations
# --------------------------------------------------------------------------


def random_roots(n, kind):
    if kind == "uniform":
        r = np.sqrt(RNG.uniform(0, 1, n)) * RNG.uniform(0.3, 0.999)
        th = RNG.uniform(0, 2 * np.pi, n)
        return r * np.exp(1j * th)
    if kind == "boundary":
        r = RNG.uniform(0.9, 0.9999, n)
        th = RNG.uniform(0, 2 * np.pi, n)
        return r * np.exp(1j * th)
    if kind == "fekete":
        eps = 10.0 ** RNG.uniform(-6, -1)
        r = RNG.uniform(0.8, 0.999)
        k = np.arange(n)
        return r * (1 + eps * RNG.normal(size=n)) * np.exp(
            1j * (2 * np.pi * k / n + eps * RNG.normal(size=n))
        )
    if kind == "cluster":
        m = RNG.integers(2, n)
        centre = RNG.uniform(0, 0.7) * np.exp(1j * RNG.uniform(0, 2 * np.pi))
        eps = 10.0 ** RNG.uniform(-3, -0.5)
        a = centre + eps * (RNG.normal(size=m) + 1j * RNG.normal(size=m))
        rest = np.sqrt(RNG.uniform(0, 1, n - m)) * 0.98 * np.exp(
            1j * RNG.uniform(0, 2 * np.pi, n - m)
        )
        return np.concatenate([a, rest])
    if kind == "circle":
        r = RNG.uniform(0.5, 0.999)
        th = np.sort(RNG.uniform(0, 2 * np.pi, n))
        return r * np.exp(1j * th)
    raise ValueError(kind)


def evaluate_roots(roots, w0_grid, only_min_hub=False):
    """Yield dict rows: one per simple admissible hub."""
    n = len(roots)
    coeffs = poly_from_roots(roots)
    crit = critical_points(coeffs)
    vals = np.array([np.polyval(coeffs, c) for c in crit])
    order = np.argsort(np.abs(vals))
    rows = []
    for idx in order[: (1 if only_min_hub else len(order))]:
        c = crit[idx]
        # simplicity: distance to other critical points
        others = np.delete(crit, idx)
        if len(others) and np.min(np.abs(others - c)) < 1e-6:
            continue
        if abs(vals[idx]) < 1e-12:
            continue
        P, rho, vothers = normalise_at_hub(coeffs, c)
        L, ok, ends = connector_length(P)
        if not ok:
            continue
        best, old = best_bound(n, vothers, w0_grid)
        rows.append(
            dict(
                n=n,
                hub=complex(c),
                fc=complex(vals[idx]),
                length_norm=L,
                best_bound=best[0],
                best_w0=best[1],
                best_S=best[2],
                old_bound=old,
                ratio=(L / best[0]) if best[0] < math.inf else math.nan,
                fires=(best[0] < 2.0),
                min_ratio_second=(float(np.min(np.abs(vothers))) if len(vothers) else math.inf),
                min_dist_one=(float(np.min(np.abs(vothers - 1))) if len(vothers) else math.inf),
            )
        )
    return rows


# --------------------------------------------------------------------------
# area check for the exterior-fibre gap
# --------------------------------------------------------------------------


def area_of_two_sheeted_component(P, w0, S, grid=700):
    """Grid estimate of Area(U), U = component of {|P-w0|<S} containing 0."""
    # bounding box: {|P-w0|<S} subset {|P| < S+|w0|}; roots of P... use
    # |z| <= 1 + (S+1)^(1/n) generous.
    n = len(P) - 1
    R = 1.5 + (S + 1) ** (1.0 / n) + max(abs(np.roots(P)))
    xs = np.linspace(-R, R, grid)
    X, Y = np.meshgrid(xs, xs)
    Z = X + 1j * Y
    mask = np.abs(np.polyval(P, Z) - w0) < S
    # flood fill from the grid point nearest 0
    from scipy import ndimage

    lab, _ = ndimage.label(mask)
    i0 = np.argmin(np.abs(xs))
    l0 = lab[i0, i0]
    if l0 == 0:
        return math.nan
    cell = (xs[1] - xs[0]) ** 2
    return float(np.sum(lab == l0)) * cell


# --------------------------------------------------------------------------
# main
# --------------------------------------------------------------------------


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--degrees", default="3,4,5,6,7,8")
    ap.add_argument("--samples", type=int, default=120)
    ap.add_argument("--climb", type=int, default=150)
    ap.add_argument("--area-checks", type=int, default=25)
    ap.add_argument("--json", default=None)
    args = ap.parse_args()

    degrees = [int(d) for d in args.degrees.split(",")]
    w0_grid = np.linspace(0.0, 1.0, 21)
    kinds = ["uniform", "boundary", "fekete", "cluster", "circle"]

    report = dict(thresholds={}, random={}, climb={}, area={})

    print("== per-degree thresholds S_n^*(w0): smallest S with C(n,S,p)<2 ==")
    for n in degrees + [10, 20, 50, 100, 1000]:
        row = {}
        for w0 in [0.0, 0.25, 0.5, 0.75, 1.0]:
            p = w0 * (1 - w0)
            row[str(w0)] = threshold_S(n, p)
        report["thresholds"][n] = row
        print(
            f"n={n:5d}  "
            + "  ".join(f"w0={w0}: S*={row[str(w0)]:.5f}" for w0 in [0.0, 0.25, 0.5, 0.75, 1.0])
        )
    print(f"limit n->oo at p=0: coth(1) = {1/math.tanh(1):.6f}")
    print("uniform S=4/3, all n>=3: max_n C(n,4/3,p) over p in [0,1/4] =",
          max(coefficient(n, 4 / 3, p) for n in range(3, 400) for p in np.linspace(0, 0.25, 6)))
    print("uniform S=2,   all n>=3: max_n C(n,2,0) =", max(coefficient(n, 2.0, 0.0) for n in range(3, 400)))

    worst_seed = {}
    print("\n== random + adversarial-family sweep (all simple hubs) ==")
    for n in degrees:
        worst = None
        count = 0
        fires_min = 0
        total_min = 0
        for kind in kinds:
            for _ in range(args.samples):
                roots = random_roots(n, kind)
                rows = evaluate_roots(roots, w0_grid)
                for r in rows:
                    count += 1
                    if not math.isnan(r["ratio"]) and (worst is None or r["ratio"] > worst["ratio"]):
                        worst = dict(r, kind=kind, roots=[complex(x) for x in roots])
                mrows = evaluate_roots(roots, w0_grid, only_min_hub=True)
                for r in mrows:
                    total_min += 1
                    fires_min += int(r["fires"])
        worst_seed[n] = worst
        report["random"][n] = dict(
            hubs=count,
            worst_ratio=worst["ratio"] if worst else None,
            worst_kind=worst["kind"] if worst else None,
            worst_length=worst["length_norm"] if worst else None,
            worst_bound=worst["best_bound"] if worst else None,
            worst_w0=worst["best_w0"] if worst else None,
            worst_S=worst["best_S"] if worst else None,
            worst_roots=[[x.real, x.imag] for x in worst["roots"]] if worst else None,
            min_hub_fires_fraction=(fires_min / total_min if total_min else None),
        )
        print(
            f"n={n}: hubs={count} worst len/bound={worst['ratio']:.6f} ({worst['kind']}), "
            f"len={worst['length_norm']:.5f} bound={worst['best_bound']:.5f} "
            f"w0={worst['best_w0']:.2f} S={worst['best_S']:.4f}; "
            f"min-hub theorem fires on {fires_min}/{total_min}"
        )

    print("\n== adversarial hill-climb of len/bound from the worst seed ==")
    for n in degrees:
        seed = worst_seed[n]
        if seed is None:
            continue
        roots = np.array(seed["roots"])
        best_ratio = seed["ratio"]
        step = 0.05
        for it in range(args.climb):
            cand = roots + step * (RNG.normal(size=n) + 1j * RNG.normal(size=n))
            cand = cand / max(1.0, np.max(np.abs(cand)) / 0.999)
            rows = evaluate_roots(cand, w0_grid)
            if not rows:
                continue
            r = max(rows, key=lambda q: (q["ratio"] if not math.isnan(q["ratio"]) else -1))
            if r["ratio"] > best_ratio:
                best_ratio, roots = r["ratio"], cand
            else:
                step *= 0.97
        report["climb"][n] = dict(best_ratio=best_ratio, roots=[[x.real, x.imag] for x in roots])
        print(f"n={n}: climbed worst len/bound = {best_ratio:.6f}")

    print("\n== exterior-fibre area gap check: Area(U)/(pi (S/(n-1))^(2/n)) at w0 in {0,1} ==")
    for n in degrees:
        worst_area = 0.0
        checks = 0
        for _ in range(args.area_checks):
            roots = random_roots(n, kinds[RNG.integers(0, len(kinds))])
            coeffs = poly_from_roots(roots)
            crit = critical_points(coeffs)
            vals = np.array([np.polyval(coeffs, c) for c in crit])
            idx = int(np.argmin(np.abs(vals)))
            if abs(vals[idx]) < 1e-12:
                continue
            P, rho, vothers = normalise_at_hub(coeffs, crit[idx])
            for w0 in (0.0, 1.0):
                S = float(np.min(np.abs(vothers - w0))) if len(vothers) else 5.0
                if S <= 1.0:
                    continue
                S = min(S, 6.0) * 0.999
                A = area_of_two_sheeted_component(P, w0, S)
                if math.isnan(A):
                    continue
                q = A / (math.pi * (S / (n - 1)) ** (2.0 / n))
                worst_area = max(worst_area, q)
                checks += 1
        report["area"][n] = dict(checks=checks, worst_area_ratio=worst_area)
        print(f"n={n}: {checks} checks, worst Area(U)/(pi (S/(n-1))^(2/n)) = {worst_area:.5f}")

    if args.json:
        with open(args.json, "w", encoding="utf-8") as fh:
            json.dump(report, fh, indent=1, ensure_ascii=False)
        print("wrote", args.json)


if __name__ == "__main__":
    sys.exit(main())
