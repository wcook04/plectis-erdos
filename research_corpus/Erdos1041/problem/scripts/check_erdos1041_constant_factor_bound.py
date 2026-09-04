#!/usr/bin/env python3
"""Erdos #1041: verification probe for UnconditionalConstantFactorBound.md.

Arms
----
tracer     validate the square-root-uniformised tracer against closed forms
           (Bernoulli half-loop sqrt(2)*varpi, descending pair exactly 2*rho)
lemma1     Cauchy-Schwarz per-component perimeter bound  H^1(dC)^2 <= 2 pi k t A'(t)
area       Gronwall/capacity area bound  Area(C_t) <= pi t^(2/n)
path       assemble the Theorem 1 path and check length and containment
conjP      measure Conjecture P:  H^1(dU) <= sqrt(2) varpi * sigma^(1/n)

Nothing here proves anything.  Theorem 1 of the note is an ordinary proof; this
script only certifies that its inequalities are not violated and that its
construction returns an actually-contained path.

Instrument-defect guards (negative_results 24, 34, 41):
  * saddle handled in tau with psi = tau^2 / s = 1 - tau^2, so the critical
    point is a regular point of the parametrisation;
  * degenerate minimising hub rejected (another critical point within 1e-4*rho);
  * every traced curve is audited for max |f| before any containment claim is
    scored, and excluded rows are receipted rather than dropped.
"""
from __future__ import annotations

import json
import math
import sys
from fractions import Fraction
from pathlib import Path

import numpy as np

VARPI = 2.6220575542921198104648395898911194136827549514316231628168
SQRT2_VARPI = math.sqrt(2.0) * VARPI          # 3.7081445...


def exact_seventy_one_tenths_certificate():
    """Rational certificate for the improved lambda=2, r=3/20 constant."""
    log2_lower = Fraction(842, 1215)
    log2_upper = Fraction(23581, 34020)
    sqrt_log2_lower = Fraction(104, 125)
    sqrt_log_40_over_3_upper = Fraction(161, 100)
    log_40_over_3_upper = 4 * log2_upper - Fraction(2, 11)
    coefficient_upper = (
        Fraction(60, 289) * Fraction(283, 200)
        + Fraction(63, 50)
        * (
            sqrt_log_40_over_3_upper
            + Fraction(22, 7) / sqrt_log2_lower
        )
    )
    gates = {
        "log2_lower": log2_lower > sqrt_log2_lower**2,
        "log2_upper": log2_upper - log2_lower == Fraction(1, 6804),
        "log_40_over_3_upper": (
            log_40_over_3_upper < sqrt_log_40_over_3_upper**2
        ),
        "sqrt2_upper": Fraction(283, 200) ** 2 > 2,
        "cuberoot2_upper": Fraction(63, 50) ** 3 > 2,
        "coefficient_below_71_over_10": (
            coefficient_upper < Fraction(71, 10)
        ),
    }
    return {
        "gates": gates,
        "coefficient_upper": str(coefficient_upper),
        "coefficient_upper_float": float(coefficient_upper),
        "target": "71/10",
        "pass": all(gates.values()),
    }


def exact_seventeen_root_low_critical_certificate():
    """Exact certificate for Corollary 3: mu<=1/2 and first-merge k>=17."""
    log2_upper = Fraction(23581, 34020)
    sqrt_log2_lower = Fraction(104, 125)
    low_upper = Fraction(1300, 7569) * Fraction(283, 200)
    high_upper = Fraction(5, 3) + Fraction(22, 7) / sqrt_log2_lower
    bracket_upper = low_upper + high_upper
    gates = {
        "log_200_over_13_below_25_over_9": (
            4 * log2_upper < Fraction(25, 9)
        ),
        "sqrt2_upper": Fraction(283, 200) ** 2 > 2,
        "bracket_square_below_34": bracket_upper**2 < 34,
        "k_factor_closes_length_two": Fraction(2, 17) * bracket_upper**2 < 4,
    }
    return {
        "gates": gates,
        "low_upper": str(low_upper),
        "high_upper": str(high_upper),
        "bracket_upper": str(bracket_upper),
        "bracket_square": str(bracket_upper**2),
        "bracket_square_slack_below_34": str(Fraction(34) - bracket_upper**2),
        "pass": all(gates.values()),
    }


def exact_twelve_root_quarter_critical_certificate():
    """Exact certificate for mu<=1/4 and first-merge k>=12."""
    log2_lower = Fraction(842, 1215)
    log2_upper = Fraction(23581, 34020)
    sqrt_log4_lower = Fraction(47, 40)
    sqrt_log_100_over_3_upper = Fraction(15, 8)
    low_upper = Fraction(75, 484) * Fraction(283, 200)
    high_upper = (
        sqrt_log_100_over_3_upper
        + Fraction(22, 7) / sqrt_log4_lower
    )
    bracket_upper = low_upper + high_upper
    gates = {
        "log_100_over_3_bound": (
            5 * log2_upper + Fraction(1, 24)
            < sqrt_log_100_over_3_upper**2
        ),
        "sqrt_log4_lower": 2 * log2_lower > sqrt_log4_lower**2,
        "bracket_square_below_24": bracket_upper**2 < 24,
        "k_factor_closes_length_two": Fraction(2, 12) * bracket_upper**2 < 4,
    }
    return {
        "gates": gates,
        "bracket_upper": str(bracket_upper),
        "bracket_square": str(bracket_upper**2),
        "bracket_square_slack": str(Fraction(24) - bracket_upper**2),
        "pass": all(gates.values()),
    }


def exact_ten_root_eighth_critical_certificate():
    """Exact certificate for mu<=1/8 and first-merge k>=10."""
    log2_lower = Fraction(842, 1215)
    log2_upper = Fraction(23581, 34020)
    sqrt_log8_lower = Fraction(36, 25)
    sqrt_log_800_over_11_upper = Fraction(52, 25)
    low_upper = Fraction(1100, 7921) * Fraction(283, 200)
    high_upper = (
        sqrt_log_800_over_11_upper
        + Fraction(22, 7) / sqrt_log8_lower
    )
    bracket_upper = low_upper + high_upper
    gates = {
        "log_800_over_11_bound": (
            6 * log2_upper + Fraction(3, 22)
            < sqrt_log_800_over_11_upper**2
        ),
        "sqrt_log8_lower": 3 * log2_lower > sqrt_log8_lower**2,
        "bracket_square_below_20": bracket_upper**2 < 20,
        "k_factor_closes_length_two": Fraction(2, 10) * bracket_upper**2 < 4,
    }
    return {
        "gates": gates,
        "bracket_upper": str(bracket_upper),
        "bracket_square": str(bracket_upper**2),
        "bracket_square_slack": str(Fraction(20) - bracket_upper**2),
        "pass": all(gates.values()),
    }


def exact_one_third_component_capacity_certificate():
    """Exact certificate for Corollary 4: mu<=1/2 and kappa<=1/3."""
    log2_upper = Fraction(23581, 34020)
    sqrt_log2_lower = Fraction(104, 125)
    sqrt_log40_upper = Fraction(97, 50)
    low_upper = Fraction(20, 361) * Fraction(283, 200)
    high_upper = Fraction(1, 3) * (
        sqrt_log40_upper + Fraction(22, 7) / sqrt_log2_lower
    )
    coefficient_upper = low_upper + high_upper
    gates = {
        "log40_bound": (
            5 * log2_upper + Fraction(1, 4) < sqrt_log40_upper**2
        ),
        "coefficient_below_two": coefficient_upper < 2,
    }
    return {
        "gates": gates,
        "coefficient_upper": str(coefficient_upper),
        "coefficient_slack_below_two": str(Fraction(2) - coefficient_upper),
        "pass": all(gates.values()),
    }


def exact_arity_capacity_table_certificate():
    """Exact certificate for Corollary 5's rational kappa cutoffs."""
    low_upper = Fraction(283, 3610)
    high_coefficient = Fraction(52029, 9100)
    cutoffs = {
        2: Fraction(1, 3),
        3: Fraction(2, 5),
        4: Fraction(12, 25),
        5: Fraction(1, 2),
        6: Fraction(7, 12),
        7: Fraction(16, 25),
        8: Fraction(2, 3),
        9: Fraction(7, 10),
        10: Fraction(3, 4),
        11: Fraction(4, 5),
        12: Fraction(5, 6),
        13: Fraction(7, 8),
        14: Fraction(9, 10),
        15: Fraction(33, 35),
        16: Fraction(39, 40),
    }
    margins = {
        str(k): str(Fraction(2 * k) - (low_upper + high_coefficient * q) ** 2)
        for k, q in cutoffs.items()
    }
    gates = {
        f"k_{k}_cutoff": (low_upper + high_coefficient * q) ** 2 < 2 * k
        for k, q in cutoffs.items()
    }
    gates["cutoffs_strictly_increase"] = all(
        cutoffs[k] < cutoffs[k + 1] for k in range(2, 16)
    )
    nested = {
        "quarter": {
            "A": Fraction(849, 3872),
            "B": Fraction(11975, 2632),
            "cutoffs": {
                2: Fraction(19, 50), 3: Fraction(12, 25),
                4: Fraction(4, 7), 5: Fraction(16, 25),
                6: Fraction(7, 10), 7: Fraction(3, 4),
                8: Fraction(4, 5), 9: Fraction(7, 8),
                10: Fraction(14, 15), 11: Fraction(49, 50),
            },
        },
        "eighth": {
            "A": Fraction(3113, 15842),
            "B": Fraction(13427, 3150),
            "cutoffs": {
                2: Fraction(2, 5), 3: Fraction(1, 2),
                4: Fraction(3, 5), 5: Fraction(2, 3),
                6: Fraction(3, 4), 7: Fraction(4, 5),
                8: Fraction(8, 9), 9: Fraction(18, 19),
            },
        },
    }
    nested_margins = {}
    for name, row in nested.items():
        nested_margins[name] = {}
        for k, q in row["cutoffs"].items():
            margin = Fraction(2 * k) - (row["A"] + row["B"] * q) ** 2
            gates[f"{name}_k_{k}_cutoff"] = margin > 0
            nested_margins[name][str(k)] = str(margin)
    return {
        "gates": gates,
        "cutoffs": {str(k): str(q) for k, q in cutoffs.items()},
        "squared_margins": margins,
        "nested_cutoffs": {
            name: {str(k): str(q) for k, q in row["cutoffs"].items()}
            for name, row in nested.items()
        },
        "nested_squared_margins": nested_margins,
        "pass": all(gates.values()),
    }


def exact_sixty_fourth_critical_capacity_certificate():
    """Sharpened exact lambda=64 lattice for the deep low-critical residual."""
    log2_lower = Fraction(842, 1215)
    log2_upper = Fraction(23581, 34020)
    log3_lower = Fraction(13, 12)
    sqrt_log_2048_over_3_upper = Fraction(64, 25)
    sqrt_log64_lower = Fraction(203, 100)
    low_upper = Fraction(3, 32) / Fraction(29, 32) ** 2 * Fraction(283, 200)
    high_coefficient = (
        sqrt_log_2048_over_3_upper
        + Fraction(22, 7) / sqrt_log64_lower
    )
    cutoffs = {
        2: Fraction(4, 9),
        3: Fraction(5, 9),
        4: Fraction(16, 25),
        5: Fraction(8, 11),
        6: Fraction(4, 5),
        7: Fraction(13, 15),
        8: Fraction(13, 14),
        9: Fraction(99, 100),
    }
    gates = {
        "log3_lower_from_three_positive_atanh_terms": (
            Fraction(1) + Fraction(1, 12) + Fraction(1, 80) > log3_lower
        ),
        "log_2048_over_3_upper": (
            11 * log2_upper - log3_lower
            < sqrt_log_2048_over_3_upper**2
        ),
        "log64_lower_sharpened": 6 * log2_lower > sqrt_log64_lower**2,
    }
    margins = {}
    for k, q in cutoffs.items():
        margin = Fraction(2 * k) - (low_upper + high_coefficient * q) ** 2
        gates[f"k_{k}_cutoff"] = margin > 0
        margins[str(k)] = str(margin)
    gates["k_10_closes_without_capacity_defect"] = (
        low_upper + high_coefficient
    ) ** 2 < 20
    gates["cutoffs_strictly_increase"] = all(
        cutoffs[k] < cutoffs[k + 1] for k in range(2, 9)
    )
    return {
        "parameters": {"lambda": 64, "r": "3/32"},
        "A": str(low_upper),
        "B": str(high_coefficient),
        "cutoffs": {str(k): str(q) for k, q in cutoffs.items()},
        "squared_margins": margins,
        "gates": gates,
        "pass": all(gates.values()),
    }
# --------------------------------------------------------------------------
# configuration
# --------------------------------------------------------------------------
class Cfg:
    def __init__(self, roots):
        self.r = np.asarray(roots, dtype=complex)
        self.n = len(self.r)
        cf = np.poly(self.r)
        self.c_fp = np.polyder(cf)
        self.c_fpp = np.polyder(self.c_fp)
        self.crit = np.roots(self.c_fp)
        cv = np.array([np.prod(c - self.r) for c in self.crit])
        k = int(np.argmin(np.abs(cv)))
        self.cstar = self.crit[k]
        self.mu = float(abs(cv[k]))
        self.theta0 = float(np.angle(cv[k]))
        self.rho = self.mu ** (1.0 / self.n)
        m = np.sort(np.abs(cv))
        self.critsep = float(m[1] / m[0]) if len(m) > 1 and m[0] > 0 else math.inf
        d = np.sort(np.abs(self.crit - self.cstar))
        self.critgap = float(d[1]) if len(d) > 1 else math.inf

    def f(self, z):
        return np.prod(z - self.r)

    def fp(self, z):
        return np.polyval(self.c_fp, z)

    def fpp(self, z):
        return np.polyval(self.c_fpp, z)

    def solve(self, w, z0, it=14):
        z = complex(z0)
        for _ in range(it):
            d = np.polyval(self.c_fp, z)
            if d == 0:
                break
            st = (np.prod(z - self.r) - w) / d
            z -= st
            if abs(st) < 1e-15 * max(1e-300, abs(z)):
                break
        return z


def _trace(cfg, slope, wfun, tau_max, nsteps):
    """March in the uniformising variable tau, Newton-projecting each step."""
    taus = np.linspace(0.0, tau_max, nsteps + 1)
    zs = [cfg.cstar]
    for i in range(1, len(taus)):
        t, tp = taus[i], taus[i - 1]
        if i == 1:
            pred = cfg.cstar + slope * t
        else:
            dz = (zs[-1] - zs[-2]) / (taus[i - 1] - taus[i - 2])
            pred = zs[-1] + dz * (t - tp)
        zs.append(cfg.solve(wfun(t), pred))
    return np.array(zs)


def lobe_boundary(cfg, side, nsteps=3000):
    """Boundary of the one-root lobe at level mu, as a closed polyline."""
    mu, th0 = cfg.mu, cfg.theta0
    w0 = mu * np.exp(1j * th0)
    d2 = cfg.fpp(cfg.cstar)
    # At a simple saddle the four local rays +-sqrt(+-2i w0/f'') sit at 90
    # degrees to each other; ONE lobe is a single 90-degree sector, bounded by
    # the two rays nearest its descending direction v.  Choosing the two signs
    # independently puts the halves on OPPOSITE lobes.
    v = (1 if side == 0 else -1) * np.sqrt(-2 * w0 / d2)
    u1 = np.sqrt(2j * w0 / d2)
    u2 = np.sqrt(-2j * w0 / d2)
    e1 = 1.0 if (u1 * np.conj(v)).real > 0 else -1.0
    e2 = 1.0 if (u2 * np.conj(v)).real > 0 else -1.0
    z1 = _trace(cfg, e1 * u1,
                lambda t: mu * np.exp(1j * (th0 + t * t)), math.sqrt(math.pi), nsteps)
    z2 = _trace(cfg, e2 * u2,
                lambda t: mu * np.exp(1j * (th0 - t * t)), math.sqrt(math.pi), nsteps)
    return np.concatenate([z1, z2[::-1]])


def descending_branch(cfg, side, nsteps=2500):
    """One member of the descending pair at the minimising hub."""
    mu, th0 = cfg.mu, cfg.theta0
    w0 = mu * np.exp(1j * th0)
    d2 = cfg.fpp(cfg.cstar)
    sgn = 1 if side == 0 else -1
    zs = _trace(cfg, sgn * np.sqrt(-2 * w0 / d2), lambda t: w0 * (1 - t * t), 1.0, nsteps)
    j = int(np.argmin(np.abs(cfg.r - zs[-1])))
    L = float(np.sum(np.abs(np.diff(zs)))) + abs(cfg.r[j] - zs[-1])
    audit = max(abs(cfg.f(z)) for z in zs) / mu
    return L, j, zs, audit


def component_boundary(cfg, t, nsteps=800, maxturns=16):
    """Boundary of the component of {|f|<=t} containing c*, plus k, H^1, A'."""
    c = cfg.cstar
    z0 = None
    for ang in np.linspace(0, 2 * np.pi, 13)[:-1]:
        u = np.exp(1j * ang)
        if abs(cfg.f(c + 4.0 * u)) < t:
            continue
        lo, hi = 0.0, 4.0
        for _ in range(200):
            m = 0.5 * (lo + hi)
            if abs(cfg.f(c + m * u)) < t:
                lo = m
            else:
                hi = m
        cand = c + hi * u
        if abs(abs(cfg.f(cand)) - t) < 1e-8 * t:
            z0 = cand
            break
    if z0 is None:
        return None
    phi0 = float(np.angle(cfg.f(z0)))
    z0 = cfg.solve(t * np.exp(1j * phi0), z0)
    dphi = 2 * np.pi / nsteps
    z = z0
    zs = [z]
    for i in range(1, maxturns * nsteps + 1):
        phi = phi0 + i * dphi
        w = t * np.exp(1j * phi)
        z = cfg.solve(w, z + 1j * cfg.f(z) / cfg.fp(z) * dphi)
        zs.append(z)
        if i % nsteps == 0 and abs(z - z0) < 1e-8 * max(1.0, abs(z0)):
            break
    else:
        return None
    zs = np.array(zs)
    k = int(round((len(zs) - 1) / nsteps))
    H1 = float(np.sum(np.abs(np.diff(zs))))
    seg = np.abs(np.diff(zs))
    Ap = float(np.sum(seg / np.abs(np.array([cfg.fp(v) for v in zs[:-1]]))))
    area = 0.5 * abs(float(np.sum(np.imag(np.conj(zs[:-1]) * np.diff(zs)))))
    audit = max(abs(cfg.f(v)) for v in zs) / t
    return dict(zs=zs, k=k, H1=H1, Aprime=Ap, area=area, phi0=phi0,
                dphi=dphi, audit=audit)


def constructed_path(cfg, t, comp, ntheta=6):
    """Theorem 1's path: descend from k boundary points, hop along dC_t."""
    zs, k, dphi, phi0 = comp['zs'], comp['k'], comp['dphi'], comp['phi0']
    if k < 2:
        return None
    arclen = np.concatenate([[0.0], np.cumsum(np.abs(np.diff(zs)))])
    best = math.inf
    best_audit = 0.0
    nsteps = int(round(2 * np.pi / dphi))
    for a in range(ntheta):
        off = int(round(a * nsteps / ntheta))
        idxs = [off + q * nsteps for q in range(k)]
        if idxs[-1] >= len(zs):
            continue
        ends, roots_hit, lens, aud = [], [], [], 0.0
        ok = True
        for ii in idxs:
            zb = zs[ii]
            wb = cfg.f(zb)
            taus = np.linspace(0.0, 1.0, 500)
            z = zb
            pts = [z]
            prev_s = 1.0
            for q in range(1, len(taus)):
                s = 1.0 - taus[q] ** 2
                dz = cfg.f(z) / (prev_s * cfg.fp(z)) if cfg.fp(z) != 0 else 0.0
                z = cfg.solve(wb * s, z + dz * (s - prev_s))
                pts.append(z)
                prev_s = s
            pts = np.array(pts)
            j = int(np.argmin(np.abs(cfg.r - pts[-1])))
            if abs(cfg.r[j] - pts[-1]) > 1e-6 * max(cfg.rho, 1e-12):
                ok = False
                break
            lens.append(float(np.sum(np.abs(np.diff(pts)))) + abs(cfg.r[j] - pts[-1]))
            aud = max(aud, max(abs(cfg.f(v)) for v in pts) / t)
            roots_hit.append(j)
            ends.append(ii)
        if not ok or len(set(roots_hit)) < 2:
            continue
        for q in range(k):
            i1, i2 = ends[q], ends[(q + 1) % k]
            if roots_hit[q] == roots_hit[(q + 1) % k]:
                continue
            arc = (arclen[i2] - arclen[i1]) if q < k - 1 else (arclen[-1] - arclen[i1] + arclen[i2])
            cand = lens[q] + lens[(q + 1) % k] + abs(arc)
            if cand < best:
                best, best_audit = cand, max(aud, comp['audit'])
    if not math.isfinite(best):
        return None
    return best, best_audit


# --------------------------------------------------------------------------
# arms
# --------------------------------------------------------------------------
def arm_tracer():
    cfg = Cfg([0.9, -0.9])
    P = float(np.sum(np.abs(np.diff(lobe_boundary(cfg, 0)))))
    LA, _, _, aA = descending_branch(cfg, 0)
    LB, _, _, aB = descending_branch(cfg, 1)
    return dict(
        perimeter_over_rho=P / cfg.rho,
        perimeter_target=SQRT2_VARPI,
        perimeter_err=abs(P / cfg.rho - SQRT2_VARPI),
        branch_pair_over_2rho=(LA + LB) / (2 * cfg.rho),
        branch_audit=max(aA, aB),
    )


def families(rng, n, kind):
    if kind == 'unif':
        return np.sqrt(rng.random(n)) * np.exp(2j * np.pi * rng.random(n))
    if kind == 'circle':
        return 0.999 * np.exp(2j * np.pi * rng.random(n))
    if kind == 'nearfek':
        e = 10 ** rng.uniform(-6, -0.5)
        return 0.9999 * np.exp(1j * (2 * np.pi * np.arange(n) / n + e * rng.standard_normal(n)))
    if kind == 'cluster':
        kk = int(max(2, rng.integers(2, max(3, n))))
        cen = 0.95 * np.sqrt(rng.random(kk)) * np.exp(2j * np.pi * rng.random(kk))
        return cen[rng.integers(0, kk, n)] + 10 ** rng.uniform(-3, -0.7) * (
            rng.standard_normal(n) + 1j * rng.standard_normal(n))
    x = rng.uniform(-0.99, 0.99, n)
    return x + 1j * rng.uniform(-1, 1, n) * 10 ** rng.uniform(-3, 0)


def main(trials=90, seed=20260824, lam=2.0):
    rng = np.random.default_rng(seed)
    kinds = ['unif', 'circle', 'nearfek', 'cluster', 'anis']
    rows, excluded = [], []
    worst = dict(cs=0.0, area=0.0, conjP=0.0, path=0.0)
    for i in range(trials):
        n = int(rng.integers(2, 10))
        kind = kinds[i % len(kinds)]
        try:
            cfg = Cfg(families(rng, n, kind))
        except Exception:
            excluded.append(dict(i=i, why='cfg'))
            continue
        if not np.isfinite(cfg.mu) or cfg.mu <= 1e-280:
            excluded.append(dict(i=i, why='mu'))
            continue
        if cfg.critgap < 1e-4 * max(cfg.rho, 1e-12):
            excluded.append(dict(i=i, why='degenerate_hub', critgap=cfg.critgap))
            continue
        row = dict(i=i, n=n, kind=kind, mu=cfg.mu, rho=cfg.rho, critsep=cfg.critsep)

        # conjP arm: one-root lobe perimeters at level mu
        try:
            for side in (0, 1):
                zb = lobe_boundary(cfg, side, 1200)
                lev = np.array([abs(cfg.f(v)) for v in zb]) / cfg.mu
                if abs(lev.max() - 1) > 1e-8 or abs(lev.min() - 1) > 1e-8:
                    raise RuntimeError('lobe level audit')
                P = float(np.sum(np.abs(np.diff(zb)))) / cfg.rho
                row[f'P{side}'] = P
                worst['conjP'] = max(worst['conjP'], P / SQRT2_VARPI)
        except Exception as exc:
            excluded.append(dict(i=i, why=f'lobe:{exc}'))
            continue

        # level window
        best = None
        for t in np.exp(np.linspace(math.log(cfg.mu * 1.05), math.log(lam * cfg.mu), 3)):
            comp = component_boundary(cfg, float(t))
            if comp is None or comp['k'] < 2 or comp['audit'] > 1 + 1e-8:
                continue
            val = t * comp['Aprime']
            if best is None or val < best[0]:
                best = (val, float(t), comp)
        if best is None:
            excluded.append(dict(i=i, why='no_component_level'))
            continue
        val, t, comp = best
        k = comp['k']
        row.update(t_over_mu=t / cfg.mu, k=k,
                   area_ratio=comp['area'] / (math.pi * t ** (2.0 / n)),
                   cs_ratio=comp['H1'] ** 2 / (2 * math.pi * k * val),
                   H1_over_k_rho=comp['H1'] / (k * cfg.rho))
        worst['area'] = max(worst['area'], row['area_ratio'])
        worst['cs'] = max(worst['cs'], row['cs_ratio'])

        pr = constructed_path(cfg, t, comp)
        if pr is not None:
            L, aud = pr
            row['path_over_rho'] = L / cfg.rho
            row['path_audit'] = aud
            if aud <= 1 + 1e-7:
                worst['path'] = max(worst['path'], row['path_over_rho'])
        rows.append(row)

    tr = arm_tracer()
    C = 7.1
    exact_constant = exact_seventy_one_tenths_certificate()
    exact_high_arity = exact_seventeen_root_low_critical_certificate()
    exact_quarter_arity = exact_twelve_root_quarter_critical_certificate()
    exact_eighth_arity = exact_ten_root_eighth_critical_certificate()
    exact_component_capacity = exact_one_third_component_capacity_certificate()
    exact_arity_capacity = exact_arity_capacity_table_certificate()
    exact_sixty_fourth_capacity = exact_sixty_fourth_critical_capacity_certificate()
    gates = {
        'tracer_bernoulli': tr['perimeter_err'] < 1e-5,
        'tracer_branch_pair': abs(tr['branch_pair_over_2rho'] - 1.0) < 1e-6,
        'lemma1_cauchy_schwarz_le_1': worst['cs'] <= 1.0,
        'gronwall_area_le_1': worst['area'] <= 1.0,
        'theorem1_path_le_71_over_10_rho': worst['path'] <= C,
        'theorem1_exact_constant_certificate': exact_constant['pass'],
        'corollary3_exact_high_arity_certificate': exact_high_arity['pass'],
        'corollary3_exact_quarter_arity_certificate': exact_quarter_arity['pass'],
        'corollary3_exact_eighth_arity_certificate': exact_eighth_arity['pass'],
        'corollary4_exact_component_capacity_certificate': exact_component_capacity['pass'],
        'corollary5_exact_arity_capacity_table_certificate': exact_arity_capacity['pass'],
        'corollary6_exact_sixty_fourth_critical_capacity_certificate': exact_sixty_fourth_capacity['pass'],
        'conjectureP_le_sqrt2_varpi': worst['conjP'] <= 1.0 + 1e-6,
    }
    verdict = 'pass' if all(gates.values()) else 'FAIL'
    out = dict(verdict=verdict, gates=gates, worst=worst, tracer=tr,
               rows_scored=len(rows), rows_excluded=len(excluded),
               exclusions=excluded[:20], lam=lam, constant=C,
               exact_constant_certificate=exact_constant,
               exact_high_arity_certificate=exact_high_arity,
               exact_quarter_arity_certificate=exact_quarter_arity,
               exact_eighth_arity_certificate=exact_eighth_arity,
               exact_component_capacity_certificate=exact_component_capacity,
               exact_arity_capacity_table_certificate=exact_arity_capacity,
               exact_sixty_fourth_critical_capacity_certificate=exact_sixty_fourth_capacity,
               sqrt2_varpi=SQRT2_VARPI)
    print(json.dumps(out, indent=1, default=float))
    receipt = Path('state/formal_math/erdos257_period_noncollapse/'
                   'erdos1041_constant_factor_bound_receipt.json')
    try:
        receipt.parent.mkdir(parents=True, exist_ok=True)
        receipt.write_text(json.dumps(dict(out, rows=rows), indent=1, default=float))
    except OSError:
        pass
    return 0 if verdict == 'pass' else 1


if __name__ == '__main__':
    sys.exit(main(*(int(a) for a in sys.argv[1:3])) if len(sys.argv) > 1 else main())
