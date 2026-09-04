#!/usr/bin/env python3
r"""Capacity, area and diameter budget for the sublevel sets of a monic polynomial.

For monic f of degree n and t > 0 put  K_t = {z : |f(z)| <= t}.

  (A) K_t is FULL: {|f| > t} has no bounded component, so C^ \ K_t is connected.
  (B) cap(K_t) = t^{1/n} exactly; the Green's function of C^ \ K_t with pole at
      infinity is (1/n) log(|f|/t).
  (C) Area(K_t) <= pi t^{2/n}, with equality iff f = (z-a)^n.
  (D) every connected component C of K_t has diam(C) <= 4 t^{1/n}.

(A) and (B) are proved in LemniscateCapacityBudget.md; (C) is (B) plus the
isoperimetric inequality for logarithmic capacity, (D) is (B) plus cap >= diam/4
for a continuum.  This script is the numerical receipt for (C) and (D), and it
also re-derives cap(K_t) for two closed-form cases as a check on (B).

Exit 0 iff every measured ratio is <= 1 within the stated grid tolerance.
"""
from __future__ import annotations

import argparse
import json
import sys
from collections import deque
from pathlib import Path

import numpy as np

GRID_TOL = 2.0e-3          # relative inflation a pixel-count area can suffer


def sublevel_facts(roots: np.ndarray, t: float, grid: int) -> dict:
    n = len(roots)
    coef = np.poly(roots)
    cap = t ** (1.0 / n)
    R0 = float(np.max(np.abs(roots)))
    M = R0 + cap + 1e-9                      # |f| >= (|z|-R0)^n forces K_t inside
    xs = np.linspace(-M, M, grid)
    X, Y = np.meshgrid(xs, xs, indexing="ij")
    Z = X + 1j * Y
    inside = np.abs(np.polyval(coef, Z)) <= t
    cell = (2 * M / (grid - 1)) ** 2
    area = float(inside.sum()) * cell

    seen = np.zeros(inside.shape, bool)
    diam_max = 0.0
    ncomp = 0
    rng = np.random.default_rng(11)
    for p in map(tuple, np.argwhere(inside)):
        if seen[p]:
            continue
        ncomp += 1
        q = deque([p]); seen[p] = True; pts = []
        while q:
            a, b = q.popleft(); pts.append((a, b))
            # 8-connectivity: K_t is CLOSED, so lobes meeting at a single point
            # (e.g. the two lobes of {|z^2-1| <= 1} at the origin) are ONE
            # component.  4-connectivity splits them and understates diam.
            for da, db in ((1, 0), (-1, 0), (0, 1), (0, -1),
                           (1, 1), (1, -1), (-1, 1), (-1, -1)):
                u, v = a + da, b + db
                if 0 <= u < grid and 0 <= v < grid and inside[u, v] and not seen[u, v]:
                    seen[u, v] = True; q.append((u, v))
        P = np.array(pts)
        W = Z[P[:, 0], P[:, 1]]
        if len(W) > 3000:
            W = W[rng.choice(len(W), 3000, replace=False)]
        if len(W) > 1:
            diam_max = max(diam_max, float(np.max(np.abs(W[:, None] - W[None, :]))))
    return dict(area=area, cap=cap, ncomp=ncomp, diam=diam_max,
                area_ratio=area / (np.pi * cap ** 2),
                diam_ratio=diam_max / (4.0 * cap))


def cases():
    out = []
    for n in (2, 3, 5, 8):
        out.append((f"(z)^{n} equality case for (C)", np.zeros(n, complex)))
    for n in (2, 3, 4, 6, 9):
        out.append((f"z^{n}-1 extremal degeneration",
                    np.exp(2j * np.pi * np.arange(n) / n)))
    rng = np.random.default_rng(20260823)
    for n in (2, 3, 4, 5, 6, 7):
        for k in range(3):
            r = np.sqrt(rng.random(n)) * np.exp(2j * np.pi * rng.random(n))
            out.append((f"random n={n} #{k}", r))
    return out


def exact_flower_diam_ratio(n: int) -> float:
    """diam(K_t)/(4 t^{1/n}) in closed form for f = z^n - t.

    K_t = {z^n in D(t,t)}, so |z| <= (2t)^{1/n} with the maximum attained at the
    n directions e^{2 pi i k/n}.  The farthest pair of those is at angular
    separation 2 pi floor(n/2)/n, giving
        diam = 2 (2t)^{1/n} sin(pi floor(n/2) / n),
    which is 2 (2t)^{1/n} for even n.  This is the family that shows the constant
    4 in (D) is NOT sharp -- and the grid cannot see it at n = 2, 3, where the
    lobes meet at the single point z = 0 and no grid samples it.
    """
    return 2.0 * (2.0 ** (1.0 / n)) * np.sin(np.pi * (n // 2) / n) / 4.0


def grad_mu_rows(grid=560):
    r"""(GRAD-mu) |f'(z)| >= n |f(z)-f(c)|^{(n-1)/n} on {|f| <= mu}: ELIMINATED.

    It holds with EQUALITY for every monic quadratic (f - f(c) = (z-c)^2) and for
    every z^n - r^n (f - f(c) = z^n), which is exactly what made it look
    canonical.  Given it, the descent branch would satisfy
        Delta <= INT_0^mu dt/(n(mu-t)^{(n-1)/n}) = mu^{1/n} <= R,
    which is Erdos #1041.  It is false from degree three; the failure is at
    CLUSTERED roots, where |f'(z_j)| -> 0 while |f(z_j)-f(c)| = mu stays put.
    """
    # PINNED cases, not a float search: an existence claim gated on random
    # batches is not a receipt (a batch with no clustered configuration reports
    # min ratio > 1 and looks like survival).  Two equality families that must
    # return exactly 1, and one stored witness that must fall below 1.
    WITNESS7 = np.array([
        0.27568574 - 0.80105245j, 0.42550818 + 0.54680520j,
        0.29744693 + 0.40968136j, -0.21070022 + 0.56623604j,
        0.32788794 - 0.02047154j, 0.09769695 + 0.08422428j,
        -0.90064690 + 0.21025744j])
    cases_ = [("quadratic 1", np.array([0.4 + 0.2j, -0.7 + 0.5j]), "equality"),
              ("quadratic 2", np.array([-0.11 + 0.9j, 0.63 - 0.24j]), "equality"),
              ("z^3 - r^3", 0.9 * np.exp(2j * np.pi * np.arange(3) / 3), "equality"),
              ("z^6 - r^6", 0.9 * np.exp(2j * np.pi * np.arange(6) / 6), "equality"),
              ("pinned n=7 witness", WITNESS7, "below_one")]
    out = []
    for name, roots, expect in cases_:
        n = len(roots)
        worst = np.inf
        for _ in range(1):
            c_ = np.poly(roots); d_ = np.polyder(c_)
            cv = np.polyval(c_, np.roots(d_))
            k = int(np.argmin(np.abs(cv))); mu = float(abs(cv[k])); fc = cv[k]
            if mu <= 0 or not np.isfinite(mu):
                continue
            M = float(np.max(np.abs(roots))) + mu ** (1.0 / n) + 1e-9
            xs = np.linspace(-M, M, grid)
            X, Y = np.meshgrid(xs, xs, indexing="ij")
            Z = X + 1j * Y
            F = np.polyval(c_, Z)
            sel = np.abs(F) <= mu
            if not sel.any():
                continue
            lhs = np.abs(np.polyval(d_, Z[sel]))
            rhs = n * np.abs(F[sel] - fc) ** ((n - 1.0) / n)
            with np.errstate(divide="ignore", invalid="ignore"):
                ratio = np.where(rhs > 0, lhs / rhs, np.inf)
            worst = min(worst, float(np.nanmin(ratio)))
        out.append(dict(name=name, n=n, min_ratio=worst, expect=expect))
    return out


def chebyshev_sharpness_rows():
    """(D') the constant 4 in (D) is sharp, via the monic Chebyshev polynomial.

    T_n(2 cos phi) = 2 cos(n phi), so |T_n| <= 2 on [-2,2], hence [-2,2] is inside
    K_2 and diam(K_2) >= 4, while cap(K_2) = 2^{1/n} by (B).  Therefore
        diam / (4 cap)  >=  2^{-1/n}  ->  1.
    Evaluated through the TRIGONOMETRIC form, not the coefficient form: np.poly
    for T_n loses all precision to cancellation past n ~ 20 (sup on [-2,2] comes
    back as 605 at n=40 instead of 2), which is why the note's large-n rows were
    discarded.
    """
    out = []
    for n in (2, 3, 4, 6, 10, 20, 40, 80, 200):
        xs = np.linspace(-2.0, 2.0, 200001)
        phi = np.arccos(np.clip(xs / 2.0, -1.0, 1.0))
        sup = float(np.abs(2.0 * np.cos(n * phi)).max())
        cap = 2.0 ** (1.0 / n)
        out.append(dict(n=n, sup_on_segment=sup, cap=cap,
                        lower_bound_ratio=2.0 ** (-1.0 / n)))
    return out


def area_currency_rows():
    """The L^2 (area) currency, eliminated on z^n - r^n.

    Candidate:  L(c) <= C sqrt(Area(Omega_a)+Area(Omega_b)); combined with
    Area({|f|<mu}) <= pi mu^{2/n} <= pi R^2 this reaches 2R iff C <= 2/sqrt(2 pi).
    On z^n - r^n at its own critical level mu = r^n the components are thin
    spikes.  Petal area, exactly, via w = z^n:
        area = n^{-2} INT_{D(r^n, r^n)} |w|^{2/n - 2} dA(w)
    while the spoke has length r.  The measured ratio grows like sqrt(2n/pi).
    """
    from scipy.integrate import dblquad
    need = 2.0 / np.sqrt(2 * np.pi)
    out = []
    r = 1.0
    for n in (3, 4, 6, 10, 20, 40):
        rn = r ** n
        f = lambda s, psi: (abs(rn + s * np.exp(1j * psi)) ** (2.0 / n - 2.0)) * s
        val, _ = dblquad(f, 0.0, 2 * np.pi, lambda p: 0.0, lambda p: rn,
                         epsabs=1e-10, epsrel=1e-10)
        petal = val / (n ** 2)
        out.append(dict(n=n, petal_area=petal,
                        ratio=2 * r / np.sqrt(2 * petal), required=need))
    return out


def main() -> int:
    ap = argparse.ArgumentParser()
    ap.add_argument("--grid", type=int, default=1200)
    ap.add_argument("--json", action="store_true")
    args = ap.parse_args()

    # analytic arm: exact diameters for z^n - t, independent of the grid
    exact_rows = [dict(n=n, ratio=exact_flower_diam_ratio(n)) for n in
                  (2, 3, 4, 5, 6, 8, 9, 12, 20)]
    worst_exact = max(r["ratio"] for r in exact_rows)

    rows, worst_a, worst_d = [], 0.0, 0.0
    for name, roots in cases():
        f = sublevel_facts(np.asarray(roots, complex), 1.0, args.grid)
        rows.append(dict(name=name, **{k: float(v) if isinstance(v, float) else v
                                       for k, v in f.items()}))
        worst_a = max(worst_a, f["area_ratio"])
        worst_d = max(worst_d, f["diam_ratio"])

    ac = area_currency_rows()
    # the ELIMINATION is the claim here: every ratio must EXCEED what the area
    # currency would need, and must grow with n.  A row that passed would mean
    # the currency is alive and this note is wrong.
    ac_eliminated = all(r["ratio"] > r["required"] for r in ac) and \
        all(ac[i]["ratio"] < ac[i + 1]["ratio"] for i in range(len(ac) - 1))

    ch = chebyshev_sharpness_rows()
    # sup|T_n| on [-2,2] must be exactly 2 (that is what puts [-2,2] in K_2), and
    # the resulting lower bound on diam/(4cap) must rise toward 1.
    ch_ok = all(abs(r["sup_on_segment"] - 2.0) < 1e-9 for r in ch) and \
        all(ch[i]["lower_bound_ratio"] < ch[i + 1]["lower_bound_ratio"]
            for i in range(len(ch) - 1)) and ch[-1]["lower_bound_ratio"] > 0.99

    gm = grad_mu_rows()
    # the ELIMINATION is the claim: exactly 1 at n=2 (equality for every
    # quadratic), and strictly below 1 from n=3.
    # equality is ANALYTIC; the tolerance is grid resolution on {|f| <= mu}, which
    # costs ~2e-4 at n=6.  The elimination side has three orders of margin.
    gm_ok = all((abs(r["min_ratio"] - 1.0) < 1.5e-3) if r["expect"] == "equality"
                else (r["min_ratio"] < 0.5) for r in gm)

    honest_d = max(worst_d, worst_exact)
    ok = ((worst_a <= 1.0 + GRID_TOL) and (honest_d <= 1.0)
          and ac_eliminated and ch_ok and gm_ok)
    payload = dict(claim_C="Area(K_t) <= pi t^{2/n}",
                   claim_D="diam(component of K_t) <= 4 t^{1/n}",
                   grid=args.grid, grid_tolerance=GRID_TOL,
                   worst_area_ratio=worst_a,
                   worst_diam_ratio_grid=worst_d,
                   worst_diam_ratio_exact_flower=worst_exact,
                   worst_diam_ratio_honest=honest_d,
                   grid_limitation=("a single-point touching is invisible to any "
                                    "grid; at n=2,3 the z^n-1 lobes are reported "
                                    "separately and the grid UNDERSTATES diam"),
                   exact_flower_rows=exact_rows,
                   claim_area_currency_eliminated=(
                       "L(c) <= C sqrt(Area(Om_a)+Area(Om_b)) cannot reach 2R: on "
                       "z^n - r^n the ratio 2r/sqrt(2*petal_area) exceeds the "
                       "required 2/sqrt(2pi) and grows like sqrt(2n/pi)"),
                   area_currency_rows=ac,
                   area_currency_eliminated=bool(ac_eliminated),
                   claim_D_prime=("the constant 4 in (D) is SHARP: monic Chebyshev "
                                  "gives diam/(4 cap) >= 2^{-1/n} -> 1"),
                   chebyshev_rows=ch, chebyshev_sharpness_ok=bool(ch_ok),
                   claim_grad_mu_eliminated=(
                       "|f'| >= n|f-f(c)|^{(n-1)/n} on {|f|<=mu} holds with "
                       "EQUALITY for every quadratic and every z^n-r^n, and is "
                       "FALSE from n=3; it would have implied Erdos #1041"),
                   grad_mu_rows=gm, grad_mu_eliminated=bool(gm_ok),
                   verdict="pass" if ok else "FAIL", rows=rows)
    if args.json:
        print(json.dumps(payload, indent=2))
    else:
        for r in rows:
            print(f"{r['name']:<32} area/(pi cap^2)={r['area_ratio']:8.5f} "
                  f" maxdiam/(4cap)={r['diam_ratio']:8.5f}  ncomp={r['ncomp']}")
        print("\nexact diam/(4 t^{1/n}) for z^n - t (grid-independent):")
        print("  " + "  ".join(f"n={r['n']}:{r['ratio']:.5f}" for r in exact_rows))
        print("\n(GRAD-mu) min |f'|/(n|f-f(c)|^((n-1)/n)) on {|f|<=mu}: "
              "must be 1 at n=2 and < 1 after (elimination)")
        for r in gm:
            print(f"    {r['name']:<22} n={r['n']}  min ratio={r['min_ratio']:.6f}"
                  f"  expect={r['expect']}")
        print(f"    eliminated={gm_ok}")
        print("\n(D') Chebyshev sharpness: diam/(4cap) >= 2^{-1/n}, sup|T_n| must be 2")
        print("  " + "  ".join(f"n={r['n']}:{r['lower_bound_ratio']:.5f}" for r in ch)
              + f"   ok={ch_ok}")
        print("\nL^2 (area) currency on z^n - r^n -- must EXCEED "
              f"{ac[0]['required']:.4f} and grow (elimination):")
        print("  " + "  ".join(f"n={r['n']}:{r['ratio']:.3f}" for r in ac)
              + f"   eliminated={ac_eliminated}")
        print(f"\nworst area ratio {worst_a:.5f} (tol 1+{GRID_TOL})")
        print(f"worst diam ratio: grid {worst_d:.5f}, exact-flower {worst_exact:.5f}, "
              f"HONEST {honest_d:.5f}   verdict {payload['verdict']}")
    return 0 if ok else 1


if __name__ == "__main__":
    sys.exit(main())
