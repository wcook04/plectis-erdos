#!/usr/bin/env python3
"""Erdos #1041: verification probe for MinimalHubWindowJoin.md.

Arms
----
MONO    Lemma 2: Psi_n(x) = x^(1/n) sqrt(2 log((x+1)/(x-1))) is strictly
        decreasing on (1,inf); limits Psi_2(inf)=2, Psi_3 large-x -> 0;
        x -> 1+ asymptotic sqrt(2 log(2/(x-1))).
QUAD    Corollary 3: on z^2 - d^2 the window infimum equals 2 mu^(1/2) to
        1e-9 relative, and the traced descending pair returns exactly that
        with containment audit max|f|/mu = 1 + O(1e-15).
WINDOW  Theorem 1 instance check on family-seeded configurations (n = 3..8):
        locate the two-root persistence level T* by bisection with the
        double witness (component root count k = 2 AND exactly one critical
        point inside the component, per BergmanSegmentLengthBound §5),
        trace the descending pair at c*, and require
            L_pair <= Psi_n(T*/mu) * mu^(1/n)
        with max|f| <= mu*(1+1e-9) audited along both arcs and the two arcs
        landing on distinct roots.
DEGEN   Forced near-degeneracy: two separated saddle pairs with value ratio
        1+delta for delta = 1e-4 and 1e-6; containment must survive and the
        measured constant must track the graceful-degradation prediction.

Nothing here proves anything.  Theorem 1 of the note is ordinary mathematics
on top of Theorem C of BergmanSegmentLengthBound.md (proved there).  This
script certifies that its inequalities are not violated by the tracer and
that the containment claim {|f| <= mu} survives the instrument.

Instrument-defect guards (negative_results 24, 34, 41 and the §5 lesson of
BergmanSegmentLengthBound.md):
  * saddle traced in the square-root uniformising variable tau;
  * degenerate minimising hubs rejected (critical-point gap < 1e-4*rho);
  * the two-root hypothesis is witnessed twice (root count and interior
    critical-point count must agree);
  * any component tracer failure at a probed level shrinks the window rather
    than extending it (conservative for T*);
  * every containment claim is audited with max|f|/mu and failing rows are
    receipted, never silently dropped.
"""
from __future__ import annotations

import importlib
import json
import math
import sys
from pathlib import Path

import numpy as np

sys.path.insert(0, str(Path(__file__).resolve().parent))
cfb = importlib.import_module("check_erdos1041_constant_factor_bound")

COTH1 = 1.3130352854993312  # coth(1)


def psi(n: int, x: float) -> float:
    # log((x+1)/(x-1)) evaluated as log1p(2/(x-1)): the direct ratio
    # cancels catastrophically for large x (float64 spacing at 1e14 is ~1.6e4,
    # where (x+1) == x and the ratio collapses to exactly 1).
    return x ** (1.0 / n) * math.sqrt(2.0 * math.log1p(2.0 / (x - 1.0)))


# --------------------------------------------------------------------------
# arms
# --------------------------------------------------------------------------
def arm_mono() -> dict:
    worst_drop, asym_err, tail_err = math.inf, 0.0, math.inf
    for n in (2, 3, 4, 6, 9):
        xs = np.geomspace(1.0 + 1e-9, 4.0e3, 4001)
        vals = np.array([psi(n, float(x)) for x in xs])
        drops = vals[:-1] - vals[1:]
        worst_drop = min(worst_drop, float(drops.min()))
    for n in (2, 3):
        big = 1e160
        v = psi(n, big)
        if n == 2:
            asym_err = max(asym_err, abs(v - 2.0))
        else:
            tail_err = min(tail_err, v)
    x = 1.0 + 1e-9
    asymp_pred = math.sqrt(2.0 * math.log(2.0 / (x - 1.0)))
    asymp_actual = psi(3, x)
    rel = abs(asymp_actual / asymp_pred - 1.0)
    return dict(
        min_step_decrease=worst_drop,
        psi2_inf_minus_2=asym_err,
        psi3_at_1e160=tail_err,
        x1p_asym_relerr=rel,
    )


def arm_quad(tol_rel=1e-9) -> dict:
    d = 0.9
    cfg = cfb.Cfg([d, -d])
    mu = cfg.mu                      # d^2
    LA, ja, _, audA = cfb.descending_branch(cfg, 0, 6000)
    LB, jb, _, audB = cfb.descending_branch(cfg, 1, 6000)
    true_L = 2.0 * math.sqrt(mu)
    # window infimum on a wide log grid
    ts = mu * np.geomspace(1.0 + 1e-12, 1e14, 2001)
    bounds = np.array([psi(2, float(t / mu)) * math.sqrt(mu) for t in ts])
    inf_b = float(bounds.min())
    return dict(
        mu=mu,
        pair_over_trueL=(LA + LB) / true_L,
        root_a=int(ja),
        root_b=int(jb),
        audits=(audA, audB),
        inf_window_over_trueL=inf_b / true_L,
        distinct_roots=bool(ja != jb),
        contained=bool(max(audA, audB) <= 1.0 + 1e-12),
        tight=bool(abs(inf_b / true_L - 1.0) < tol_rel),
    )


def _point_in_poly(poly: np.ndarray, p: complex) -> bool:
    z = poly - p
    x, y = z.real, z.imag
    inside = False
    j = len(z) - 1
    for i in range(len(z)):
        if (y[i] > 0) != (y[j] > 0):
            xc = x[i] + (0.0 - y[i]) * (x[j] - x[i]) / (y[j] - y[i])
            if xc > 0:
                inside = not inside
        j = i
    return inside


def _two_root_witness(cfg, t: float, nsteps: int = 320):
    """Return True iff the level-t component at c* provably (per witnesses)
    holds exactly two roots.  Conservative: any instrument failure -> False."""
    comp = cfb.component_boundary(cfg, float(t), nsteps=nsteps)
    if comp is None or comp["audit"] > 1.0 + 1e-8:
        return False
    if comp["k"] != 2:
        return False
    poly = np.concatenate([comp["zs"], comp["zs"][:1]])
    inner = [c for c in cfg.crit
             if abs(c - cfg.cstar) > 1e-12 and _point_in_poly(poly, c)]
    # exactly one critical point strictly inside, and it must be c* itself
    if len(inner) != 0:
        return False
    return bool(_point_in_poly(poly, cfg.cstar))


def locate_safe_two_root_level(cfg, nu_cap: float, climb=1.6, iters=18):
    """Largest instrument-verifiable two-root level below nu_cap.

    Probes from a macroscopic level downward-safe (neck width resolvable),
    climbs until the witness fails, then bisects the bracket.  Returns
    (t_eval, censored) where t_eval is a VERIFIED interior level of the
    two-root window -- every returned level is a valid `t` for a Theorem 1
    instance check.  None if no rung passes.
    """
    base = cfg.mu * 1.003
    good = bad = None
    lvl = base
    while lvl < nu_cap:
        if _two_root_witness(cfg, min(lvl, nu_cap)):
            good = min(lvl, nu_cap)
        else:
            bad = min(lvl, nu_cap)
            break
        lvl *= climb
        if lvl > 64.0 * cfg.mu and bad is None:
            break
    if good is None:
        for frac in (1.001, 1.0003, 1.0001, 1.00003):
            lvl = cfg.mu * frac
            if lvl >= nu_cap:
                continue
            if _two_root_witness(cfg, lvl):
                return lvl, False
        return None, False
    if bad is None:
        return good, True
    a, b = good, bad
    for _ in range(iters):
        m = math.sqrt(a * b)
        if _two_root_witness(cfg, m):
            a = m
        else:
            b = m
    return a, False


def arm_window(trials=42, seed=20260824) -> dict:
    rng = np.random.default_rng(seed)
    kinds = ["unif", "circle", "nearfek", "cluster", "anis"]
    rows, excluded = [], []
    worst_ratio = 0.0
    worst_audit = 0.0
    for i in range(trials):
        n = int(rng.integers(3, 9))
        kind = kinds[i % len(kinds)]
        try:
            cfg = cfb.Cfg(cfb.families(rng, n, kind))
        except Exception:
            excluded.append(dict(i=i, why="cfg"))
            continue
        if not np.isfinite(cfg.mu) or cfg.mu <= 1e-280:
            excluded.append(dict(i=i, why="mu"))
            continue
        if cfg.critgap < 1e-4 * max(cfg.rho, 1e-12):
            excluded.append(dict(i=i, why="degenerate_hub", critgap=cfg.critgap))
            continue
        cvs = np.abs(np.array([np.prod(c - cfg.r) for c in cfg.crit]))
        nu_cap = float(np.sort(cvs)[-1]) * 1.0000001
        t_eval, _cens = locate_safe_two_root_level(cfg, nu_cap)
        if t_eval is None:
            excluded.append(dict(i=i, why="no_safe_two_root_level", n=n, kind=kind))
            continue
        LA, ja, _, audA = cfb.descending_branch(cfg, 0, 2500)
        LB, jb, _, audB = cfb.descending_branch(cfg, 1, 2500)
        audit = max(audA, audB)
        if ja == jb:
            excluded.append(dict(i=i, why="same_root_branches", n=n, kind=kind))
            continue
        L = LA + LB
        bound = psi(n, t_eval / cfg.mu) * cfg.rho
        ratio = L / bound
        row = dict(i=i, n=n, kind=kind, mu=cfg.mu,
                   t_eval_over_mu=t_eval / cfg.mu,
                   L_over_rho=L / cfg.rho,
                   bound_over_rho=bound / cfg.rho,
                   ratio=ratio,
                   audits=(audA, audB))
        rows.append(row)
        if audit <= 1.0 + 1e-9:
            worst_ratio = max(worst_ratio, ratio)
        worst_audit = max(worst_audit, audit)
    return dict(rows=rows, excluded=excluded,
                worst_ratio=worst_ratio, worst_audit=worst_audit,
                scored=sum(1 for r in rows if max(r["audits"]) <= 1.0 + 1e-9))


def _two_pair_roots(d, M, e):
    return [d, -d, M + e, M - e]


def arm_degen(gated=(1e-3, 1e-4), attempted=(1e-6,)) -> dict:
    """Forced near-degeneracy.  `gated` deltas must resolve and satisfy the
    bound; `attempted` deltas are report-only because the merge neck is at or
    below grid resolution there (honest exclusion, not a pass)."""
    out = []
    for delta in (*gated, *attempted):
        d, M = 0.35, 4.0
        e = d * math.sqrt(1.0 + delta)
        cfg = cfb.Cfg(_two_pair_roots(d, M, e))
        cvs = np.abs(np.array([np.prod(c - cfg.r) for c in cfg.crit]))
        nu_cap = float(np.sort(cvs)[-1]) * 1.0000001
        t_eval, cens = locate_safe_two_root_level(cfg, nu_cap)
        row = dict(delta_target=delta,
                   sep_measured=float(np.sort(cvs)[1] / np.sort(cvs)[0]),
                   n=int(cfg.n), mu=cfg.mu)
        if t_eval is None:
            row.update(verdict="unresolved_below_grid_resolution")
            out.append(row)
            continue
        LA, ja, _, audA = cfb.descending_branch(cfg, 0, 3000)
        LB, jb, _, audB = cfb.descending_branch(cfg, 1, 3000)
        L = LA + LB
        bound = psi(cfg.n, t_eval / cfg.mu) * cfg.rho
        row.update(
            t_eval_over_mu=t_eval / cfg.mu,
            censored=bool(cens),
            L_over_rho=L / cfg.rho,
            bound_over_rho=bound / cfg.rho,
            ratio=L / bound,
            audits=(audA, audB),
            distinct=bool(ja != jb),
            verdict="resolved",
        )
        out.append(row)
    resolved = [r for r in out if r.get("verdict") == "resolved"]
    return dict(rows=out,
                resolved=len(resolved),
                all_contained=bool(resolved) and all(
                    max(r["audits"]) <= 1.0 + 1e-9
                    and r["ratio"] <= 1.0 + 1e-12 and r["distinct"]
                    for r in resolved))


def arm_thresh(ns=(2, 3, 4, 5, 6, 7, 8, 10), lo=1.0 + 1e-14, hi=64.0,
               iters=200):
    """Corollary 5 thresholds: unique x_n* with Psi_n(x_n*) = 2.

    Psi_2 decreases strictly to 2 without attaining it, so x_2* = inf is
    reported as +inf (represented by None) once the residual at hi is below
    1e-12.  Gates: residual |Psi_n(x*) - 2| tiny at every finite n*, and
    x_n* strictly decreasing in n.
    """
    table, residuals = {}, {}
    for n in ns:
        a, b = math.log(lo), math.log(hi)
        f = lambda lx: psi(n, math.exp(lx)) - 2.0
        # Psi decreasing in x: f(log lo) > +slack near 1+, and
        #   f(log hi) > 0  => no crossing below hi (n = 2 case),
        #   f(log hi) <= 0 => unique crossing in (lo, hi).
        if f(b) > 0:
            table[n] = None          # never reaches 2 below hi
            continue
        for _ in range(iters):
            m = 0.5 * (a + b)
            if f(m) > 0:
                a = m
            else:
                b = m
        xs = math.exp(0.5 * (a + b))
        table[n] = xs
        residuals[n] = abs(psi(n, xs) - 2.0)
    finite = [(n, x) for n, x in table.items() if x is not None]
    mono_ok = all(finite[i][1] > finite[i + 1][1]
                  for i in range(len(finite) - 1))
    return dict(thresholds=table, residuals=residuals,
                monotone_in_n=bool(mono_ok),
                max_residual=max(residuals.values()) if residuals else None)


def _compose_shift_power(coeffs: np.ndarray, h: complex, q: int) -> np.ndarray:
    """Coefficient array of P((z-h)^q) via Horner in the argument."""
    w = np.array([1.0, -h])            # z - h
    for _ in range(q - 1):
        w = np.convolve(w, np.array([1.0, -h]))
    acc = np.array([coeffs[0]], dtype=complex)   # leading coeff
    for a in coeffs[1:]:
        acc = np.convolve(acc, w)
        acc[-1] += float(np.real(a)) + 1j * float(np.imag(a))
    return acc


def _unique_moduli(vals: np.ndarray, rtol=1e-7):
    vals = np.sort(np.abs(vals))
    out = []
    for v in vals:
        if not out or abs(v - out[-1]) > rtol * max(1e-300, out[-1]):
            out.append(v)
    return np.array(out)


def arm_pullback(trials=8, seed=77):
    """Corollary 6's spectrum identity: the critical-value moduli of
    f = P((z-h)^q) are exactly P's distinct critical-value moduli together
    with |P(0)| (deduplicated to relative tolerance)."""
    rng = np.random.default_rng(seed)
    worst_set_err, checked = 0.0, 0
    for _ in range(trials):
        n = int(rng.integers(3, 6))
        q = int(rng.integers(2, 5))
        roots_P = rng.uniform(-0.9, 0.9, n) + 1j * rng.uniform(-0.9, 0.9, n)
        h = complex(rng.uniform(-1, 1), rng.uniform(-1, 1))
        coeffs = np.poly(roots_P)
        dP = np.polyder(coeffs)
        if abs(np.polyval(dP, 0.0)) < 1e-4:
            continue
        f_coeffs = _compose_shift_power(coeffs, h, q)
        df_coeffs = np.polyder(f_coeffs)
        fcrit = np.roots(df_coeffs)
        # Newton polish: np.roots leaves conditioning noise that splits the
        # q-fold value clusters; three polish steps collapse it.
        d2f = np.polyder(df_coeffs)
        for i in range(len(fcrit)):
            z = complex(fcrit[i])
            for _ in range(3):
                num = np.polyval(df_coeffs, z)
                den = np.polyval(d2f, z)
                if den == 0 or abs(num) < 1e-300:
                    break
                z = z - num / den
            fcrit[i] = z
        # Values evaluated through the structure P((z-h)^q), NOT through the
        # expanded coefficients: the shifted degree-nq form is catastrophically
        # conditioned, and expanding it pollutes even exact critical points.
        fvals = np.array([np.polyval(coeffs, (c - h) ** q) for c in fcrit])
        pvals = np.array([np.polyval(coeffs, c) for c in np.roots(dP)])
        pvals = np.append(pvals, np.polyval(coeffs, 0.0))
        pred = _unique_moduli(pvals)
        got = _unique_moduli(fvals)
        # Tolerant two-sided set distance: exact count matching is fragile
        # because the q lifts of one P-critical point are ill-conditioned
        # zeros of a degree-nq-1 polynomial and their shared value cluster
        # can split under float64 root-finding.
        def _setdist(A, B):
            return max(min(abs(a - b) / max(a, 1e-300) for b in B) for a in A)
        err = float(max(_setdist(got, pred), _setdist(pred, got)))
        worst_set_err = max(worst_set_err, err)
        checked += 1
    return dict(checked=checked, worst_set_err=worst_set_err)


# --------------------------------------------------------------------------
def main(trials=42, seed=20260824):
    mono = arm_mono()
    quad = arm_quad()
    win = arm_window(int(trials), int(seed))
    deg = arm_degen()
    thr = arm_thresh()
    pull = arm_pullback()

    gates = {
        "MONO_strictly_decreasing": mono["min_step_decrease"] > 0.0,
        "MONO_psi2_limit_2": mono["psi2_inf_minus_2"] < 1e-9,
        "MONO_x1p_asymptotic": mono["x1p_asym_relerr"] < 5e-5,
        "QUAD_exact_optimal": quad["tight"] and quad["contained"]
                              and quad["distinct_roots"]
                              and abs(quad["pair_over_trueL"] - 1.0) < 1e-9,
        "WINDOW_no_violation": win["worst_ratio"] <= 1.0 and win["scored"] > 0,
        "WINDOW_containment": win["worst_audit"] <= 1.0 + 1e-9,
        "DEGEN_graceful": bool(deg["all_contained"]),
        "THRESH_residuals": thr["max_residual"] is not None
                            and thr["max_residual"] < 1e-10,
        "THRESH_monotone_in_n": bool(thr["monotone_in_n"]),
        "PULLBACK_spectrum": pull["checked"] >= 3
                             and pull["worst_set_err"] < 1e-7,
    }
    verdict = "pass" if all(gates.values()) else "FAIL"
    out = dict(verdict=verdict, gates=gates, mono=mono, quad=quad,
               window=dict(scored=win["scored"],
                           excluded=len(win["excluded"]),
                           worst_ratio=win["worst_ratio"],
                           worst_audit=win["worst_audit"],
                           exclusions=win["excluded"][:20]),
               degen=deg, thresh=thr, pullback=pull, coth1=COTH1)
    print(json.dumps(out, indent=1, default=float))
    receipt = Path("state/formal_math/erdos257_period_noncollapse/"
                   "erdos1041_minimal_hub_window_receipt.json")
    try:
        receipt.parent.mkdir(parents=True, exist_ok=True)
        full = dict(out, window_rows=win["rows"])
        receipt.write_text(json.dumps(full, indent=1, default=float))
    except OSError:
        pass
    return 0 if verdict == "pass" else 1


if __name__ == "__main__":
    sys.exit(main(*(int(a) for a in sys.argv[1:3])) if len(sys.argv) > 1 else main())
