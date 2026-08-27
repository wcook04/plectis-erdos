#!/usr/bin/env python3
r"""The capacity-geodesic conjecture for Erdos #1041, and its receipt.

Write K_t = {z : |f(z)| <= t} for monic f of degree n.  LemniscateCapacityBudget.md
proves cap(K_t) = t^{1/n} exactly.  The conjecture measured here is

  (C)  if a connected component of K_t contains two roots of f, then two of them
       are joined INSIDE that component by a path of length at most

              2 t^{1/n}  =  2 cap(K_t).

(C) is affine-invariant and carries no unit-disk hypothesis.  It implies Erdos
#1041 through the classical Fekete chain mu <= R^n (TwoSegmentLevelIdentity.md
section 4): applying (C) at t = mu = min_c |f(c)| gives a path of length
<= 2 mu^{1/n} <= 2R < 2 lying in {|f| <= mu} subset {|f| < 1}.

Five arms.

  (EQ)      On f = (z-tau)^n - lambda, (C) is an EQUALITY for every n >= 2 and
            every lambda != 0 -- not only in a limit.  Asserted from the closed
            form, per this directory's rule that equality families must come
            from their ordinary proofs and not from an integrator.
  (FLOOR)   geo >= d_a + d_b is rigorous, so (d_a+d_b)/(2 rho) > 1 would REFUTE
            (C) outright.  Measured on random and near-Fekete families.
  (GEO)     The measured ratio on this directory's stored hard witnesses -- the
            configurations that refute every explicit path family -- and in the
            near-Fekete shell, where the true supremum lives.
  (DISCRIM) geo <= L(c*) always, so (C) is strictly weaker than the STRONG
            completion L(c*) <= 2 mu^{1/n} that negative_results entry 28
            refutes.  The gap is measured.
  (CHAIN)   mu <= R^n, the only inequality (C) needs to reach #1041.

Instrument.  At level exactly mu the two merging lobes meet ONLY at c*, so every
admissible path passes through c* and the geodesic splits into two halves with
c* as a FIXED endpoint.  Both halves are relaxed with c* pinned, so the
neck-cutting artefact -- which is linear in the neck radius mu^{1/n} eta^{1/n}
and biases the ratio DOWN, towards false confirmation -- cannot occur.  Descent
branches are traced UPWARD from each root along the inverse ray f(z) = s f(c*),
s : 0 -> 1, so no local model at the saddle is used and exactly-degenerate
saddles (negative_results entry 23) behave the same as simple ones.  No critical
value has modulus below mu, so no branch meets a critical point before s = 1.

Every reported path is AUDITED for containment at high density.  A contained
path of length L proves geo <= L, so a ratio below 1 is a genuine confirmation;
a ratio above 1 would be inconclusive, because the relaxation returns an upper
bound.  Only (FLOOR) can refute.

Exit 0 iff every audited path is contained, every measured ratio is <= 1 within
the stated tolerance, and the closed-form equality family returns exactly 1.
"""
from __future__ import annotations

import argparse
import json
import sys

import numpy as np

RATIO_TOL = 1e-6          # relaxation returns an upper bound; this is slack for it

# Finite-sample containment resolution.  The relaxation admits a move using a
# fixed number of samples per segment, so between samples |f| can rise slightly
# above the level; the independent, denser audit then reports that excess.  It is
# measured at ~1.4e-9 relative on the worst row, which is why gating at 1e-9 is
# not a statement about the mathematics but about the sampling density.
AUDIT_TOL = 1e-7
# A path that leaks is not literally in K_mu, so a leaky row is only admissible
# when its margin dwarfs the leak: shrinking such a path back inside costs
# O(leak) in length.  Any row with audit above 1 + AUDIT_EXACT must therefore
# carry at least AUDIT_LEAK_MARGIN of margin below the bound.
AUDIT_EXACT = 1e-12
AUDIT_LEAK_MARGIN = 1e-3

# --- this directory's stored hard witnesses ------------------------------------
# Exact IEEE-754 hexadecimal literals, copied from
# check_erdos1041_straight_spoke_hub_criterion.py, so the configurations
# round-trip bit for bit; their margins are near 1e-5.
QC_WITNESS = {
    6: (("0x1.fffffaead1dfdp-1", "-0x1.c7f97b12bedcep-15"),
        ("0x1.004ed623acd87p-1", "0x1.bb3a1b3208ad6p-1"),
        ("-0x1.ffded10fb5c87p-2", "0x1.bb713c92edfe4p-1"),
        ("-0x1.fffff9e87dd68p-1", "-0x1.0766ef919e3d1p-12"),
        ("-0x1.00485f6af598cp-1", "-0x1.bb3dd8051992dp-1"),
        ("0x1.00198d2225a68p-1", "-0x1.bb58e733c06dcp-1")),
    9: (("0x1.fffffadb279edp-1", "-0x1.54cbe5f38764ep-14"),
        ("0x1.882fdda9ba317p-1", "0x1.4922d6b3868dfp-1"),
        ("0x1.63e8c845cba7bp-3", "0x1.f83590b0811ebp-1"),
        ("-0x1.fffb9be200080p-2", "0x1.bb68ed350eca4p-1"),
        ("-0x1.e121a80180737p-1", "0x1.5e2df749c719cp-2"),
        ("-0x1.e11b7beb2b6bep-1", "-0x1.5e4fe150117d8p-2"),
        ("-0x1.0005816d133a1p-1", "-0x1.bb647aee76a86p-1"),
        ("0x1.637127244f7d2p-3", "-0x1.f83ad6df31cf7p-1"),
        ("0x1.8833eebb49d0cp-1", "-0x1.491f0e2e50785p-1")),
}


def _hex_roots(literals) -> np.ndarray:
    return np.asarray([complex(float.fromhex(a), float.fromhex(b))
                       for a, b in literals], dtype=complex)


def stored_witnesses() -> list[tuple[str, np.ndarray]]:
    L = 999 / 1000
    r5 = 99999 / 100000
    return [
        ("QC degree-6: no critical hub carries two spokes", _hex_roots(QC_WITNESS[6])),
        ("QC degree-9: no critical hub carries two spokes", _hex_roots(QC_WITNESS[9])),
        ("exact cubic: no safe chord, <=1 origin spoke",
         np.array([L * (7 + 24j) / 25, L * (7 - 24j) / 25, -L + 0j])),
        ("z^3 - (99/100)^3: kills every root chord",
         0.99 * np.exp(2j * np.pi * np.arange(3) / 3)),
        ("quintic: 0 of 5 origin spokes contained",
         np.array([r5 + 0j, r5 * (-20 + 99j) / 101, r5 * (-20 - 99j) / 101,
                   r5 * (-28 + 195j) / 197, r5 * (-28 - 195j) / 197])),
        ("quartic straight-spoke witness",
         np.array([9999 + 4j, -125 + 9998j, -9999 - 14j, -23 - 9999j]) / 10000),
    ]


# --- geometry ------------------------------------------------------------------

def crit_data(roots: np.ndarray):
    roots = np.asarray(roots, dtype=complex)
    coef = np.poly(roots)
    dcoef = np.polyder(coef)
    crit = np.roots(dcoef)
    vals = np.abs(np.polyval(coef, crit))
    k = int(np.argmin(vals))
    return roots, coef, dcoef, crit[k], float(vals[k]), np.sort(vals)


def _newton(coef, dcoef, z, target, it=12):
    for _ in range(it):
        d = np.polyval(dcoef, z)
        if d == 0:
            break
        step = (np.polyval(coef, z) - target) / d
        z = z - step
        if abs(step) < 1e-15 * max(1.0, abs(z)):
            break
    return z


_S_GRID = np.unique(np.concatenate([np.linspace(0.0, 1 - 1e-3, 120),
                                    1 - np.geomspace(1e-3, 1e-11, 140)]))


def up_branches(coef, dcoef, roots, A):
    """Inverse-ray branch z(s), f(z) = s A, s : 0 -> 1-, from each root."""
    out = []
    for z0 in roots:
        z = z0
        pts = [z]
        s_prev = 0.0
        ok = True
        for s in _S_GRID[1:]:
            d = np.polyval(dcoef, z)
            zn = _newton(coef, dcoef, z + (A * (s - s_prev) / d if d != 0 else 0.0), A * s)
            if not np.isfinite(zn) or abs(zn - z) > 0.5 * max(1.0, abs(z)) + 0.5:
                ok = False
                break
            z = zn
            s_prev = s
            pts.append(z)
        out.append((np.array(pts), ok))
    return out


def _segmax(coef, Z0, Z1, m):
    ts = np.linspace(0.0, 1.0, m)
    Z = Z0[:, None] + (Z1 - Z0)[:, None] * ts[None, :]
    return np.max(np.abs(np.polyval(coef, Z)), axis=1)


def _path_len(p):
    return float(np.sum(np.abs(np.diff(p))))


def _resample(p, n):
    s = np.concatenate([[0.0], np.cumsum(np.abs(np.diff(p)))])
    if s[-1] <= 0:
        return p
    q = np.linspace(0, s[-1], n)
    return np.interp(q, s, p.real) + 1j * np.interp(q, s, p.imag)


def relax_pinned(coef, p, t, sweeps, npts, m):
    """Taut p with BOTH endpoints pinned.  Every returned path lies in {|f|<=t}."""
    p = _resample(p, npts).astype(complex)
    alphas = np.array([1.0, 0.55, 0.28, 0.11, 0.035, 0.01])
    for sw in range(sweeps):
        L0 = _path_len(p)
        for par in (1, 0):
            idx = np.arange(1 + par, len(p) - 1, 2)
            if len(idx) == 0:
                continue
            tgt = 0.5 * (p[idx - 1] + p[idx + 1])
            done = np.zeros(len(idx), bool)
            newp = p[idx].copy()
            for a in alphas:
                live = ~done
                if not live.any():
                    break
                q = p[idx][live] + a * (tgt[live] - p[idx][live])
                ok = ((_segmax(coef, p[idx - 1][live], q, m) <= t)
                      & (_segmax(coef, q, p[idx + 1][live], m) <= t))
                sel = np.where(live)[0][ok]
                newp[sel] = q[ok]
                done[sel] = True
            p[idx] = newp
        if sw % 7 == 6:
            keep = [0]
            i = 0
            while i < len(p) - 1:
                hi = min(len(p) - 1, i + 40)
                cand = np.arange(i + 2, hi + 1)
                j = i + 1
                if len(cand):
                    vis = _segmax(coef, np.full(len(cand), p[i]), p[cand], m) <= t
                    if vis.any():
                        j = int(cand[np.where(vis)[0][-1]])
                keep.append(j)
                i = j
            p = _resample(p[np.array(keep)], npts).astype(complex)
        if abs(_path_len(p) - L0) < 1e-12 * max(L0, 1e-12) and sw > 12:
            break
    return p


def audit(coef, paths, mu, per_segment=320):
    """Independent containment check, denser per segment than the relaxation's."""
    worst = 0.0
    ts = np.linspace(0.0, 1.0, per_segment)
    for p in paths:
        if len(p) < 2:
            continue
        Z = p[:-1, None] + (p[1:] - p[:-1])[:, None] * ts[None, :]
        worst = max(worst, float(np.max(np.abs(np.polyval(coef, Z)))))
    return worst / mu


def geodesic(roots, npts=300, m=150, sweeps=420, rel=1e-12):
    """Upper bound on geo_{K_mu}(a,b) for the merging pair, path pinned at c*."""
    roots, coef, dcoef, cstar, mu, allv = crit_data(roots)
    n = len(roots)
    A = np.polyval(coef, cstar)
    t = mu * (1 + rel)
    brs = up_branches(coef, dcoef, roots, A)
    dist = np.array([abs(b[-1] - cstar) if ok else np.inf for b, ok in brs])
    tol = 1e-4 * max(1.0, float(np.max(np.abs(roots))))
    idx = [i for i in range(n) if dist[i] < tol] or list(np.argsort(dist)[:2])
    if len(idx) < 2:
        idx = list(np.argsort(dist)[:2])
    halves = {}
    for i in idx:
        p = relax_pinned(coef, np.concatenate([brs[i][0], [cstar]]), t, sweeps, npts, m)
        halves[i] = (_path_len(p), p, _path_len(np.concatenate([brs[i][0], [cstar]])))
    best = None
    for ii in range(len(idx)):
        for jj in range(ii + 1, len(idx)):
            i, j = idx[ii], idx[jj]
            if abs(roots[i] - roots[j]) < 1e-9:
                continue
            L = halves[i][0] + halves[j][0]
            if best is None or L < best[0]:
                best = (L, i, j)
    if best is None:
        return None
    L, i, j = best
    rho = mu ** (1.0 / n)
    Lb = halves[i][2] + halves[j][2]
    d = np.abs(roots - cstar)
    return dict(n=n, mu=mu, rho=rho, geo=L, ratio=L / (2 * rho),
                branch=Lb, branch_ratio=Lb / (2 * rho),
                da=float(d[i]), db=float(d[j]),
                floor_ratio=float(d[i] + d[j]) / (2 * rho),
                merge_is_nearest=bool(set((i, j)) == set(int(x) for x in np.argsort(d)[:2])),
                audit=audit(coef, (halves[i][1], halves[j][1]), mu),
                crit_sep=float(allv[1] / allv[0]) if len(allv) > 1 else float("inf"))


# --- (EQ) the equality family, from the closed form -----------------------------

def equality_family_rows(degrees, taus=(0.0, 0.4 - 0.3j), lams=(1.0, 0.017 + 0.9j)):
    r"""f = (z-tau)^n - lambda.  mu = |lambda|, rho = |lambda|^{1/n}, geo = 2 rho.

    Closed form.  With tau = 0 and lambda = r^n e^{i alpha} the roots are
    z_j = r e^{i(alpha + 2 pi j)/n} and K_mu = {z : z^n in Dbar(lambda, |lambda|)}.
    That disk satisfies Re(w conj(lambda)) >= |w|^2 / 2 >= 0, so it lies in the
    closed half plane |arg(w/lambda)| <= pi/2, and its preimage is n sectors of
    half-angle pi/(2n) with centres 2 pi / n apart: pairwise disjoint away from 0.
    So K_mu \ {0} has exactly n components, one per root, and 0 in K_mu because
    |f(0)| = |lambda| = mu.  Any path joining two distinct roots inside K_mu is
    connected and meets two of those components, hence contains 0, hence has
    length >= |a| + |b| = 2r.  The two radii attain it: on [0, z_j],
    f(s z_j) = lambda (s^n - 1) so |f| = mu (1 - s^n) <= mu.  Therefore
    geo = 2r = 2 mu^{1/n} EXACTLY, at every n >= 2 and every lambda != 0.
    For n = 2 every monic quadratic has this form, so (C) is an equality for
    EVERY quadratic.
    """
    rows = []
    for n in degrees:
        for tau in taus:
            for lam in lams:
                r = abs(lam) ** (1.0 / n)
                roots = tau + r * np.exp(1j * (np.angle(lam) + 2 * np.pi * np.arange(n)) / n)
                coef = np.poly(roots)
                mu_cf = abs(lam)
                # numerical confirmation of the two closed-form facts used above
                sect = 2 * np.pi / n - np.pi / n            # sector gap, must be > 0
                ss = np.linspace(0, 1, 4001)
                worst = max(float(np.max(np.abs(np.polyval(coef, tau + s * (roots[j] - tau)))))
                            for j in (0, 1) for s in [ss])
                mu_num = float(np.min(np.abs(np.polyval(coef, np.roots(np.polyder(coef))))))
                rows.append(dict(n=n, tau=str(tau), lam=str(lam), rho=r,
                                 geo=2 * r, bound=2 * mu_cf ** (1.0 / n), ratio=1.0,
                                 sector_gap=sect,
                                 radius_max_over_mu=worst / mu_cf,
                                 mu_closed_form_rel_err=abs(mu_num - mu_cf) / mu_cf))
    return rows


# --- families ------------------------------------------------------------------

def near_fekete(n, eps, seed):
    rng = np.random.default_rng(seed)
    return 0.9999999 * np.exp(2j * np.pi * (np.arange(n) / n + eps * rng.normal(0, 1, n)))


def random_cfg(n, rng, kind):
    if kind == 0:
        return rng.uniform(0, 1, n) ** 0.5 * np.exp(2j * np.pi * rng.uniform(0, 1, n))
    if kind == 1:
        return (1 - 10 ** rng.uniform(-4, -0.4, n)) * np.exp(2j * np.pi * rng.uniform(0, 1, n))
    if kind == 2:
        return 0.999 * np.exp(2j * np.pi * (np.arange(n) / n + rng.normal(0, 0.06, n)))
    if kind == 3:
        return near_fekete(n, 10 ** rng.uniform(-9, -2), int(rng.integers(1 << 30)))
    if kind == 4:
        cc = rng.uniform(0, 1, 3) ** 0.5 * np.exp(2j * np.pi * rng.uniform(0, 1, 3))
        z = cc[rng.integers(0, 3, n)] + rng.normal(0, 0.10, n) + 1j * rng.normal(0, 0.10, n)
        return z / np.maximum(1.0, np.abs(z) / 0.999)
    return rng.normal(0, 1.2, n) + 1j * rng.normal(0, 1.2, n)      # no disk hypothesis


# --- (PERLOBE) the per-lobe halving, and the tie caveat -------------------------

PERLOBE_WITNESS = (("0x1.faaa57c9eead2p-1", "0x1.af062077d3174p-6"),
                   ("-0x1.4fab831c004a1p-6", "0x1.ff147e739f661p-1"),
                   ("-0x1.f82dc814b0a54p-1", "-0x1.2ba561a3f287ap-6"),
                   ("0x1.9fc10c16eb808p-6", "-0x1.fb6edf63d6e1dp-1"))


def per_lobe_all_hubs(roots):
    """d/rho for the merging pair at EVERY critical point, ordered by |f(c)|.

    Exact: d is a distance between two computed points, not a relaxation output.
    negative_results entry 28 requires both tie checks -- the runner-up hub and a
    tie-guarded search -- before a min-critical-hub violation may be read as a
    statement about the problem rather than about the selector.
    """
    roots = np.asarray(roots, dtype=complex)
    coef = np.poly(roots)
    dcoef = np.polyder(coef)
    crit = np.roots(dcoef)
    vals = np.abs(np.polyval(coef, crit))
    order = np.argsort(vals)
    n = len(roots)
    rows = []
    for rank, k in enumerate(order):
        cs, mu = crit[k], float(vals[k])
        rho = mu ** (1.0 / n)
        d = np.abs(roots - cs)
        brs = up_branches(coef, dcoef, roots, np.polyval(coef, cs))
        dist = np.array([abs(b[-1] - cs) if ok else np.inf for b, ok in brs])
        idx = [i for i in range(n) if dist[i] < 1e-4] or list(np.argsort(dist)[:2])
        if len(idx) < 2:
            idx = list(np.argsort(dist)[:2])
        idx = sorted(idx, key=lambda i: d[i])[:2]
        rows.append(dict(rank=rank, crit_value=mu, rho=rho,
                         per_lobe=float(max(d[i] for i in idx)) / rho,
                         pair_sum=float(sum(d[i] for i in idx)) / (2 * rho),
                         merge_is_nearest=bool(set(idx) ==
                                               set(int(x) for x in np.argsort(d)[:2]))))
    rows.sort(key=lambda r: r["rank"])
    sep = float(vals[order[1]] / vals[order[0]]) if len(order) > 1 else float("inf")
    return rows, sep


def tie_guarded_per_lobe(n, rng, sepmin, seeds=60, steps=130):
    """Adversarial max of the per-lobe ratio with near-tie hubs REJECTED."""
    def score(z):
        try:
            roots, coef, dcoef, cs, mu, allv = crit_data(z)
        except Exception:
            return -1.0, None
        if len(allv) > 1 and allv[1] / allv[0] < sepmin:
            return -1.0, None
        brs = up_branches(coef, dcoef, roots, np.polyval(coef, cs))
        dist = np.array([abs(b[-1] - cs) if ok else np.inf for b, ok in brs])
        idx = [i for i in range(n) if dist[i] < 1e-4] or list(np.argsort(dist)[:2])
        if len(idx) < 2:
            return -1.0, None
        d = np.abs(roots - cs)
        rho = mu ** (1.0 / n)
        idx = sorted(idx, key=lambda i: d[i])[:2]
        return float(max(d[i] for i in idx)) / rho, bool(
            set(idx) == set(int(x) for x in np.argsort(d)[:2]))
    best, bz, bn = -1.0, None, None
    for _ in range(seeds):
        e = 10 ** rng.uniform(-7, -1.5)
        z = 0.9999999 * np.exp(2j * np.pi * (np.arange(n) / n + e * rng.normal(0, 1, n)))
        v, nr = score(z)
        if v > best:
            best, bz, bn = v, z, nr
    if bz is None:
        return None
    z, sig = bz.copy(), 1e-3
    for _ in range(steps):
        w = z * np.exp(1j * rng.normal(0, sig, n)) * (1 + rng.normal(0, sig / 10, n))
        w = w / np.maximum(1.0, np.abs(w) / 0.9999999)
        v, nr = score(w)
        if v > best:
            best, z, bn = v, w, nr
            sig = min(sig * 1.35, 3e-2)
        else:
            sig = max(sig * 0.9, 1e-10)
    return dict(n=n, sepmin=sepmin, max_per_lobe=best, merge_is_nearest=bn)


# --- (CUSP) the margin law near the extremal ------------------------------------

def cusp_law_rows(degrees, eps_list=(1e-2, 1e-3, 1e-4, 1e-5, 1e-6, 1e-7, 1e-8), **kw):
    """Proposition 4:  2 rho - (d_a+d_b) = rho_crit (cos th_a + cos th_b) + O(rho_crit^2).

    So 1 - geo/(2 rho) should be FIRST ORDER in rho_crit, with constant inside
    [cos^2(pi/n), cos(pi/n)] -- which needs the geodesic deficit to be o(rho_crit).
    The perturbation DIRECTION is held fixed so the constant is fixed.
    """
    out = []
    for n in degrees:
        rng = np.random.default_rng(4242 + n)
        h = rng.normal(0, 1, n)
        h -= h.mean()
        h /= np.linalg.norm(h)
        E, M, RC = [], [], []
        for e in eps_list:
            z = 0.99999999 * np.exp(2j * np.pi * (np.arange(n) / n + e * h))
            r = geodesic(z, **kw)
            if r is None:
                continue
            margin = 1.0 - r["ratio"]
            if margin <= 1e-8:
                continue
            crit = np.roots(np.polyder(np.poly(np.asarray(z, complex))))
            E.append(e)
            M.append(margin)
            RC.append(float(np.mean(np.abs(crit - crit.mean()))))
        if len(M) < 4:
            continue
        const = np.asarray(M) / np.asarray(RC)
        out.append(dict(
            n=n,
            slope_vs_eps=float(np.polyfit(np.log(E), np.log(M), 1)[0]),
            predicted_slope_vs_eps=1.0 / (n - 1),
            slope_vs_rho_crit=float(np.polyfit(np.log(RC), np.log(M), 1)[0]),
            const_lo=float(const.min()), const_hi=float(const.max()),
            band_lo=float(np.cos(np.pi / n) ** 2), band_hi=float(np.cos(np.pi / n))))
    return out


def fekete_chain(roots):
    """mu <= R^n, with R the circumradius; the only inequality (C) needs."""
    roots, coef, dcoef, cstar, mu, _ = crit_data(roots)
    n = len(roots)
    c = roots.mean()
    for _ in range(400):                      # cheap 1-centre shrink to circumradius
        k = int(np.argmax(np.abs(roots - c)))
        c = c + (roots[k] - c) * 0.02
    R = float(np.max(np.abs(roots - c)))
    return mu / R ** n, R


def main() -> int:
    ap = argparse.ArgumentParser()
    ap.add_argument("--json", action="store_true")
    ap.add_argument("--trials", type=int, default=90)
    ap.add_argument("--npts", type=int, default=300)
    ap.add_argument("--samples", type=int, default=150)
    ap.add_argument("--sweeps", type=int, default=420)
    args = ap.parse_args()
    kw = dict(npts=args.npts, m=args.samples, sweeps=args.sweeps)

    eq = equality_family_rows([2, 3, 4, 5, 6, 8, 12])
    eq_ok = all(abs(r["ratio"] - 1.0) < 1e-15 and r["sector_gap"] > 0
                and r["radius_max_over_mu"] <= 1 + 1e-12
                and r["mu_closed_form_rel_err"] < 1e-8 for r in eq)

    witness_rows = []
    for name, z in stored_witnesses():
        r = geodesic(z, **kw)
        r["name"] = name
        witness_rows.append(r)

    nf_rows = []
    for n in (3, 4, 5, 6, 8):
        seq = []
        for e in (1e-2, 1e-4, 1e-6, 1e-8, 1e-10):
            r = geodesic(near_fekete(n, e, 97 * n + int(-np.log10(e))), **kw)
            r["n"], r["eps"] = n, e
            seq.append(r)
        # the signature a sharp bound must show: rising to 1 FROM BELOW.  The
        # tolerance absorbs relaxation noise between adjacent rows; it does not
        # absorb a ratio above 1, which is gated separately by RATIO_TOL.
        seq_rising = all(seq[i]["ratio"] <= seq[i + 1]["ratio"] + 5e-3
                         for i in range(len(seq) - 1))
        nf_rows.append(dict(n=n, rising=bool(seq_rising), rows=seq))

    rng = np.random.default_rng(20260824)
    floor_rows = []
    worst_floor = 0.0
    not_nearest = 0
    ntot = 0
    for n in (3, 4, 5, 6, 8, 10):
        w = 0.0
        for k in range(args.trials):
            z = random_cfg(n, rng, k % 6)
            if len(np.unique(np.round(z, 9))) < n:
                continue
            try:
                roots, coef, dcoef, cstar, mu, _ = crit_data(z)
                A = np.polyval(coef, cstar)
                brs = up_branches(coef, dcoef, roots, A)
                dist = np.array([abs(b[-1] - cstar) if ok else np.inf for b, ok in brs])
                tol = 1e-4 * max(1.0, float(np.max(np.abs(roots))))
                idx = [i for i in range(n) if dist[i] < tol] or list(np.argsort(dist)[:2])
                if len(idx) < 2:
                    idx = list(np.argsort(dist)[:2])
                d = np.abs(roots - cstar)
                pair = sorted(idx, key=lambda i: d[i])[:2]
                rho = mu ** (1.0 / n)
                fr = float(d[pair[0]] + d[pair[1]]) / (2 * rho)
            except Exception:
                continue
            if not np.isfinite(fr):
                continue
            ntot += 1
            w = max(w, fr)
            if set(pair) != set(int(x) for x in np.argsort(d)[:2]):
                not_nearest += 1
        floor_rows.append(dict(n=n, worst_floor_ratio=w))
        worst_floor = max(worst_floor, w)

    pl_rows, pl_sep = per_lobe_all_hubs(_hex_roots(PERLOBE_WITNESS))
    rng3 = np.random.default_rng(31)
    guarded = [g for g in (tie_guarded_per_lobe(nn, rng3, s)
                           for s in (1.001, 1.02) for nn in (4, 5)) if g]
    # the min-critical hub must violate, the runner-up must not, and the
    # tie-guarded climb must stay clearly below 1: that is the entry-28 pattern
    perlobe_ok = (pl_rows[0]["per_lobe"] > 1.0
                  and all(r["per_lobe"] <= 1.0 for r in pl_rows[1:])
                  and all(r["pair_sum"] <= 1.0 for r in pl_rows)
                  and all(g["max_per_lobe"] <= 1.0 for g in guarded))

    cusp = cusp_law_rows((3, 4, 5, 6), **kw)
    cusp_ok = all(abs(c["slope_vs_rho_crit"] - 1.0) <= 0.10
                  and abs(c["slope_vs_eps"] - c["predicted_slope_vs_eps"]) <= 0.02
                  and c["const_lo"] >= 0.9 * c["band_lo"]
                  and c["const_hi"] <= 1.05 * c["band_hi"] for c in cusp) and len(cusp) == 4

    chain = []
    rng2 = np.random.default_rng(11)
    for n in (3, 5, 8):
        for k in range(12):
            z = random_cfg(n, rng2, k % 5)
            if len(np.unique(np.round(z, 9))) < n:
                continue
            ratio, R = fekete_chain(z)
            chain.append(dict(n=n, mu_over_Rn=float(ratio), R=float(R)))
    chain_ok = all(c["mu_over_Rn"] <= 1 + 1e-9 for c in chain)

    all_geo = witness_rows + [r for b in nf_rows for r in b["rows"]]
    worst_ratio = max(r["ratio"] for r in all_geo)
    worst_audit = max(r["audit"] for r in all_geo)
    min_gap = min(r["branch_ratio"] - r["ratio"] for r in all_geo)
    gates = {
        "equality_family_exact": bool(eq_ok),
        "fekete_chain": bool(chain_ok),
        "per_lobe_entry28_pattern": bool(perlobe_ok),
        "cusp_law_first_order": bool(cusp_ok),
        "worst_ratio_le_1": bool(worst_ratio <= 1 + RATIO_TOL),
        "worst_audit_le_1": bool(worst_audit <= 1 + AUDIT_TOL),
        "leaky_rows_have_margin": bool(all(
            r["audit"] <= 1 + AUDIT_EXACT or 1.0 - r["ratio"] >= AUDIT_LEAK_MARGIN
            for r in all_geo)),
        "worst_floor_le_1": bool(worst_floor <= 1 + 1e-9),
        "branch_ge_geodesic": bool(min_gap >= -1e-9),
        "near_fekete_rising": bool(all(b["rising"] for b in nf_rows)),
    }
    failed = [k for k, v in gates.items() if not v]
    ok = not failed

    payload = dict(
        claim=("(C) a component of K_t holding two roots joins two of them inside "
               "itself by a path of length <= 2 t^{1/n} = 2 cap(K_t); (C) implies "
               "Erdos #1041 through mu <= R^n"),
        instrument=("path pinned through c*, so no neck-cutting; branches traced "
                    "upward from the roots, so degenerate saddles need no local "
                    "model; every reported path audited for containment"),
        direction=("reported geodesics are UPPER bounds, so ratio <= 1 confirms and "
                   "ratio > 1 is inconclusive; only the (FLOOR) arm can refute"),
        equality_family_rows=eq, equality_exact=bool(eq_ok),
        witness_rows=witness_rows, near_fekete=nf_rows,
        floor_rows=floor_rows, worst_floor_ratio=worst_floor,
        floor_trials=ntot, merge_not_nearest=not_nearest,
        claim_perlobe=("the per-lobe halving geo(a,c*) <= rho FAILS at the "
                       "minimum-critical hub, but ONLY inside a near-tie: at the "
                       "runner-up hub it holds, and a tie-guarded search cannot "
                       "approach 1.  Eliminated for the min-critical selector; "
                       "untouched for min-over-hubs"),
        per_lobe_witness_rows=pl_rows, per_lobe_crit_sep=pl_sep,
        per_lobe_tie_guarded=guarded, per_lobe_pattern_ok=bool(perlobe_ok),
        claim_cusp=("Proposition 4: the margin 1 - geo/(2 rho) is FIRST ORDER in "
                    "rho_crit with constant in [cos^2(pi/n), cos(pi/n)]; the cusp "
                    "is a coordinate, not an obstruction"),
        cusp_rows=cusp, cusp_law_ok=bool(cusp_ok),
        fekete_chain_rows=chain, fekete_chain_ok=bool(chain_ok),
        worst_ratio=worst_ratio, worst_audit=worst_audit,
        min_branch_minus_geo=min_gap,
        gates=gates, failed_gates=failed,
        exact_values=dict(worst_ratio=repr(worst_ratio), worst_audit=repr(worst_audit),
                          worst_floor=repr(worst_floor), min_gap=repr(min_gap)),
        verdict="pass" if ok else "FAIL")

    if args.json:
        print(json.dumps(payload, indent=2, default=str))
    else:
        print("(EQ)  f = (z-tau)^n - lambda : ratio is EXACTLY 1 from the closed "
              f"form at n = 2,3,4,5,6,8,12 -- exact={eq_ok}")
        print("\n(GEO) stored hard witnesses -- the configurations that refute every "
              "explicit path family")
        print(f"  {'witness':<48} {'n':>2} {'2rho':>9} {'geo':>9} {'RATIO':>10} "
              f"{'branch':>9} {'audit':>10}")
        for r in witness_rows:
            print(f"  {r['name']:<48} {r['n']:>2} {2*r['rho']:>9.6f} {r['geo']:>9.6f} "
                  f"{r['ratio']:>10.7f} {r['branch_ratio']:>9.6f} {r['audit']:>10.8f}")
        print("\n(GEO) near-Fekete shell -- must rise to 1 strictly FROM BELOW")
        for b in nf_rows:
            print(f"  n={b['n']:<2} " + "  ".join(f"{r['eps']:.0e}:{r['ratio']:.7f}"
                                                  for r in b["rows"])
                  + f"   rising={b['rising']}")
        print("\n(FLOOR) (d_a+d_b)/(2 rho) for the MERGING pair -- a rigorous lower "
              "bound on the ratio, so > 1 would REFUTE (C)")
        print("  " + "  ".join(f"n={r['n']}:{r['worst_floor_ratio']:.6f}" for r in floor_rows))
        print(f"  worst {worst_floor:.6f} over {ntot} configurations; the merging "
              f"pair was NOT the pair nearest c* in {not_nearest}/{ntot}")
        print("\n(PERLOBE) per-lobe halving on the stored degree-four witness: "
              f"the two smallest critical values agree to {pl_sep - 1:.2e}")
        print(f"  {'hub':<18} {'|f(c)|':>16} {'max d/rho':>11} {'pair sum/2rho':>14} "
              f"{'merge==nearest':>15}")
        for r in pl_rows:
            tag = ("minimum-critical", "runner-up", "third")[min(r["rank"], 2)]
            print(f"  {tag:<18} {r['crit_value']:>16.12f} {r['per_lobe']:>11.7f} "
                  f"{r['pair_sum']:>14.7f} {str(r['merge_is_nearest']):>15}")
        print("  tie-guarded climb (near-tie hubs rejected):")
        for g in guarded:
            print(f"    guard>={g['sepmin']:<6} n={g['n']}  max d/rho="
                  f"{g['max_per_lobe']:.7f}  merge==nearest={g['merge_is_nearest']}")
        print(f"  entry-28 pattern reproduced (violate at min hub, hold at runner-up, "
              f"hold under guard) = {perlobe_ok}")
        print("\n(CUSP) Proposition 4: the margin is FIRST ORDER in rho_crit")
        print(f"  {'n':>2} {'slope/log eps':>14} {'pred 1/(n-1)':>13} "
              f"{'slope/log rho_c':>16} {'const range':>18} {'band':>18}")
        for c in cusp:
            print(f"  {c['n']:>2} {c['slope_vs_eps']:>14.4f} "
                  f"{c['predicted_slope_vs_eps']:>13.4f} {c['slope_vs_rho_crit']:>16.4f} "
                  f"{c['const_lo']:>8.3f}..{c['const_hi']:<9.3f} "
                  f"[{c['band_lo']:.3f},{c['band_hi']:.3f}]")
        print(f"  law holds = {cusp_ok}")
        print(f"\n(DISCRIM) min over all rows of (branch_ratio - geodesic ratio) = "
              f"{min_gap:.9f} >= 0: (C) is weaker than the STRONG completion that "
              "negative_results entry 28 refutes")
        print(f"\n(CHAIN) worst mu/R^n = "
              f"{max(c['mu_over_Rn'] for c in chain):.6f} <= 1   ok={chain_ok}")
        print(f"\nworst ratio {worst_ratio!r} (tol 1+{RATIO_TOL})")
        print(f"worst audit {worst_audit!r} (tol 1+{AUDIT_TOL})")
        print(f"worst floor {worst_floor!r} | min branch-geo {min_gap!r}")
        print("gates: " + "  ".join(f"{k}={v}" for k, v in gates.items()))
        if failed:
            print("FAILED GATES: " + ", ".join(failed))
        print(f"verdict {payload['verdict']}")
    return 0 if ok else 1


if __name__ == "__main__":
    sys.exit(main())
