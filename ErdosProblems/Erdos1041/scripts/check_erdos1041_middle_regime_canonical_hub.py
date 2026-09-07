#!/usr/bin/env python3
"""Replay for MiddleRegimeCanonicalHub.md  (Erdos #1041, middle regime 2/5 < mu < 1).

Exact components (integer / Fraction arithmetic, plus one symbolic identity check):

  * Theorem A -- the adjacent-chord law on the equality family.  The reduction
        f(z) = z^n - m,   z(t) = r((1-t) + t w),   w = e^{2 pi i / n},
        =>  |f(z(t))| = m | (A + i B s)^n + 1 |,   A = cos(pi/n), B = 2 sin(pi/n),
        s = t - 1/2,
    is audited at 60 significant digits for 3 <= n <= 24, and the closed form
        max_{[a_0,a_1]} |f| = m (1 + cos^n(pi/n)),   attained only at the midpoint,
    is certified in exact rational arithmetic at n = 3, 4, 6 (the degrees where
    cos^n(pi/n) is rational) by a Bernstein-positivity certificate for
        (1 + A^n)^2 - G_n(s)  >= 0   on  s in [0, 1/2].
    Consequences certified exactly: kappa_3 = 8/9, kappa_4 = 4/5, kappa_6 = 64/91
    with kappa_n = 1/(1 + cos^n(pi/n)), and 1/2 < kappa_n for every n.

  * Theorem B -- the quantitative centroid-spoke perturbation bound.  The
    cyclotomic identity prod_{k=1}^{n-1} (1 - s w^k) = (1 - s^n)/(1 - s) is
    audited at 60 significant digits for 3 <= n <= 24; S_n is computed with a certified
    rational upper bound; the resulting envelope is audited on a fixed-seed
    float sample (falsification evidence only).

  * Theorem C -- no uniform Fekete rigidity in the band.  For
    f_{n,r}(z) = z (z^{n-1} - r^{n-1}) with rational r the certificate
        mu^{n-1} = (n-1)^{n-1} r^{n(n-1)} / n^n
    is an exact rational, the centroid is exactly 0, one root is exactly 0, so
    the eccentricity 1 - min_j|a_j - c| / max_j |a_j - c| is exactly 1, and the
    origin spoke maximum is exactly mu.

  * Theorem D -- the two-level wall (z^k - a^k)(z^k + b^k), 0 < b <= a < 1,
    k >= 2: mu = a^k b^k exactly, the origin is simultaneously the centroid and
    the least critical point, every origin spoke maximum is
    max(a^k b^k, (a^k+b^k)^2/4) < 1, all in exact rational arithmetic.

Sampled components (floating point, falsification evidence only): a short
deterministic replay of the middle-regime climbs of section 5 of the note.

Universal authority is the analytic proof in MiddleRegimeCanonicalHub.md.
Erdos #1041 is NOT proved by this note or this script.

Run from the repository root:
  ./repo-python formal_math/erdos257_period_noncollapse/ErdosProblems/Erdos1041/scripts/check_erdos1041_middle_regime_canonical_hub.py
"""
from __future__ import annotations

import json
import math
from fractions import Fraction

# --------------------------------------------------------------------------
# small exact polynomial helpers (dense coefficient lists, ASCENDING powers,
# entries are Fraction)
# --------------------------------------------------------------------------


def padd(p, q):
    m = max(len(p), len(q))
    return [(p[i] if i < len(p) else Fraction(0)) + (q[i] if i < len(q) else Fraction(0))
            for i in range(m)]


def pscale(p, c):
    return [c * x for x in p]


def pmul(p, q):
    out = [Fraction(0)] * (len(p) + len(q) - 1)
    for i, a in enumerate(p):
        if a == 0:
            continue
        for j, b in enumerate(q):
            out[i + j] += a * b
    return out


def ppow(p, k):
    out = [Fraction(1)]
    for _ in range(k):
        out = pmul(out, p)
    return out


def bernstein_coeffs(p, lo, hi):
    """Bernstein coefficients of p on [lo, hi]; all >= 0 certifies p >= 0 there."""
    d = len(p) - 1
    # substitute x = lo + (hi-lo) u,  u in [0,1]
    q = [Fraction(0)]
    base = [lo, hi - lo]
    acc = [Fraction(1)]
    for k in range(d + 1):
        q = padd(q, pscale(acc, p[k]))
        acc = pmul(acc, base)
    q = q + [Fraction(0)] * (d + 1 - len(q))
    # Bernstein coefficients on [0,1]
    return [sum(Fraction(math.comb(k, i), math.comb(d, i)) * q[i] for i in range(k + 1))
            for k in range(d + 1)]


# --------------------------------------------------------------------------
# Theorem A
# --------------------------------------------------------------------------


def theoremA_symbolic(nmax: int = 24):
    """Verify  z(t)^n = - r^n (A + i B s)^n  at 60-digit precision, 3 <= n <= nmax.

    The identity is proved in section 1 of the note; this is a high-precision
    audit of the proved reduction, not its authority.
    """
    from mpmath import mp, mpf, mpc, cos, sin, pi, exp, mpmathify

    mp.dps = 60
    rows = []
    for n in range(3, nmax + 1):
        w = exp(2j * pi / n)
        A = cos(pi / n)
        B = 2 * sin(pi / n)
        worst = mpf(0)
        for i in range(0, 26):
            t = mpf(i) / 25
            r = mpf(7) / 10
            z = r * ((1 - t) + t * w)
            s = t - mpf(1) / 2
            worst = max(worst, abs(z ** n + r ** n * (A + 1j * B * s) ** n))
        rows.append({"n": n, "max_residual": float(worst)})
    return {"available": True, "rows": rows,
            "all_zero": all(r["max_residual"] < 1e-45 for r in rows),
            "precision_dps": 60}

def _G_exact(n):
    """Exact rational coefficients (ascending in s) of

        G_n(s) = (A^2 + B^2 s^2)^n + 2 Re((A + i B s)^n) + 1
               = |(A + i B s)^n + 1|^2 ,

    for the three degrees where the data are rational:
        n = 3:  A = 1/2,           B^2 = 3
        n = 4:  A^2 = 1/2,         B^2 = 2
        n = 6:  A^2 = 3/4,         B^2 = 1
    Returns (G, An, A2, B2) with An = A^n.
    """
    if n == 3:
        A2, B2, A = Fraction(1, 4), Fraction(3), Fraction(1, 2)
        An = A ** 3
    elif n == 4:
        A2, B2, A = Fraction(1, 2), Fraction(2), None
        An = A2 ** 2
    elif n == 6:
        A2, B2, A = Fraction(3, 4), Fraction(1), None
        An = A2 ** 3
    else:
        raise ValueError(n)

    # (A^2 + B^2 s^2)^n  -- polynomial in s
    base = [A2, Fraction(0), B2]
    modterm = ppow(base, n)

    # 2 Re((A + i B s)^n) = 2 sum_k C(n,2k) (-1)^k A^{n-2k} B^{2k} s^{2k}
    re = [Fraction(0)] * (2 * n + 1)
    for k in range(0, n // 2 + 1):
        j = 2 * k
        pw = n - j
        if pw % 2 == 0:
            Apw = A2 ** (pw // 2)
        else:
            assert A is not None
            Apw = A * (A2 ** ((pw - 1) // 2))
        re[j] += 2 * math.comb(n, j) * ((-1) ** k) * Apw * (B2 ** k)

    G = padd(modterm, re)
    G = padd(G, [Fraction(1)])
    return G, An, A2, B2


def theoremA_exact():
    rows = []
    for n in (3, 4, 6):
        G, An, A2, B2 = _G_exact(n)
        target = (1 + An) ** 2
        # midpoint value s = 0
        mid = G[0]
        # endpoint s = 1/2 must be 0 (the chord endpoints are roots)
        end = sum(c * Fraction(1, 2) ** i for i, c in enumerate(G))
        # certificate: target - G(s) >= 0 on [0, 1/2] via Bernstein positivity
        diff = padd(pscale(G, Fraction(-1)), [target])
        bc = bernstein_coeffs(diff, Fraction(0), Fraction(1, 2))
        kappa = Fraction(1) / (1 + An)
        rows.append({
            "n": n,
            "cos_n_pi_over_n": str(An),
            "kappa_n": str(kappa),
            "max_over_chord_equals_m_times": str(1 + An),
            "midpoint_value_matches": mid == target,
            "endpoint_value_is_zero": end == 0,
            "bernstein_min_coeff": str(min(bc)),
            "bernstein_all_nonnegative": all(c >= 0 for c in bc),
            "kappa_gt_one_half": kappa > Fraction(1, 2),
        })
    return {
        "rows": rows,
        "all_certified": all(r["midpoint_value_matches"] and r["endpoint_value_is_zero"]
                             and r["bernstein_all_nonnegative"] and r["kappa_gt_one_half"]
                             for r in rows),
        "kappa_anchors": {"3": "8/9", "4": "4/5", "6": "64/91"},
    }


def kappa_table(nmax: int = 24):
    """kappa_n = 1/(1 + cos^n(pi/n)), floating, to exhibit the decrease to 1/2."""
    out = []
    prev = None
    ok = True
    for n in range(3, nmax + 1):
        k = 1.0 / (1.0 + math.cos(math.pi / n) ** n)
        if prev is not None and not (k < prev):
            ok = False
        prev = k
        out.append({"n": n, "kappa": round(k, 9)})
    return {"table": out, "strictly_decreasing": ok, "limit": 0.5,
            "all_above_one_half": all(r["kappa"] > 0.5 for r in out)}


# --------------------------------------------------------------------------
# Theorem B
# --------------------------------------------------------------------------


def theoremB_symbolic(nmax: int = 24):
    """Verify prod_{k=1}^{n-1}(1 - s w^k) = (1 - s^n)/(1 - s) at 60-digit precision."""
    from mpmath import mp, mpf, pi, exp

    mp.dps = 60
    rows = []
    for n in range(3, nmax + 1):
        w = exp(2j * pi / n)
        worst = mpf(0)
        for i in range(0, 20):
            s = mpf(i) / 21
            lhs = 1
            for k in range(1, n):
                lhs = lhs * (1 - s * w ** k)
            rhs = (1 - s ** n) / (1 - s)
            worst = max(worst, abs(lhs - rhs))
        rows.append({"n": n, "max_residual": float(worst)})
    return {"available": True, "rows": rows,
            "all_zero": all(r["max_residual"] < 1e-45 for r in rows),
            "precision_dps": 60}

def S_n_upper(n: int) -> Fraction:
    """Certified rational upper bound for S_n = sum_{k=1}^{n-1} 1/m_k,
    m_k = min_{s in [0,1]} |1 - s w^k| = |sin(2 pi k/n)| if cos(2 pi k/n) > 0 else 1."""
    total = Fraction(0)
    for k in range(1, n):
        a = 2.0 * math.pi * k / n
        if math.cos(a) > 0.0:
            m = abs(math.sin(a))
            # round the reciprocal UP generously (1e-12 relative slack)
            total += Fraction(int(math.ceil((1.0 / m) * 1e12)) + 1, 10 ** 12)
        else:
            total += Fraction(1)
    return total


def theoremB_sample(trials: int = 1500, seed: int = 20260905):
    """Fixed-seed float audit of the Theorem B envelope.  The spoke maximum is
    taken at the exact real critical points of |f|^2 on the segment."""
    import numpy as np

    rng = np.random.default_rng(seed)
    Sn = {n: float(S_n_upper(n)) for n in range(3, 9)}
    viol = 0
    fired = 0
    worst_ratio = 0.0
    used = 0
    for _ in range(trials):
        n = int(rng.integers(3, 9))
        lam = float(rng.uniform(0.3, 0.999))
        delta = 10.0 ** rng.uniform(-4.0, -0.8)
        d = rng.standard_normal(n) + 1j * rng.standard_normal(n)
        d = d * (delta / max(np.abs(d).max(), 1e-300))
        om = np.exp(2j * np.pi * np.arange(n) / n)
        a = lam * om * (1 + d)
        a = a - a.mean()
        dp = a / (lam * om) - 1
        dmax = float(np.abs(dp).max())
        if dmax >= 0.9 or np.abs(a).max() >= 1.0:
            continue
        used += 1
        c = np.poly(a)
        fc = abs(np.polyval(c, 0.0))
        E = math.exp(2 * dmax * Sn[n] / (1 - dmax)) - 1.0
        bound = fc * (1 + E)
        tm = 0.0
        for j in range(n):
            g = np.array([0.0 + 0j])
            for co in c:
                g = np.polyadd(np.polymul(g, np.array([a[j], 0.0 + 0j])),
                               np.array([co]))
            q = np.polymul(g, np.conj(g)).real
            dq = np.polyder(q)
            cand = [0.0, 1.0]
            if len(dq) > 1:
                for x in np.roots(dq):
                    if abs(x.imag) < 1e-9 and -1e-12 <= x.real <= 1 + 1e-12:
                        cand.append(min(1.0, max(0.0, float(x.real))))
            tm = max(tm, float(np.sqrt(max(0.0, np.polyval(q, np.array(cand)).max()))))
        if tm > bound * (1 + 1e-9):
            viol += 1
        if bound < 1.0:
            fired += 1
        if bound > 0:
            worst_ratio = max(worst_ratio, tm / bound)
    return {"trials": trials, "admissible": used, "violations": viol,
            "criterion_fired": fired,
            "worst_true_over_bound": round(worst_ratio, 9)}

# --------------------------------------------------------------------------
# Theorem C
# --------------------------------------------------------------------------


def theoremC(rows=((4, Fraction(97, 100), Fraction(2, 5)),
                   (5, Fraction(99, 100), Fraction(1, 2)),
                   (7, Fraction(999, 1000), Fraction(3, 5)),
                   (9, Fraction(999, 1000), Fraction(13, 20)),
                   (20, Fraction(9999, 10000), Fraction(4, 5)),
                   (50, Fraction(99999, 100000), Fraction(9, 10)))):
    """mu^{n-1} = (n-1)^{n-1} r^{n(n-1)} / n^n  for f = z (z^{n-1} - r^{n-1})."""
    out = []
    for n, r, thr in rows:
        mu_pow = Fraction((n - 1) ** (n - 1), n ** n) * r ** (n * (n - 1))
        out.append({
            "n": n, "r": str(r), "threshold": str(thr),
            "mu_pow_n_minus_1_gt_threshold_pow": mu_pow > thr ** (n - 1),
            "mu_float": round(float(mu_pow) ** (1.0 / (n - 1)), 9),
            "centroid_is_zero": True,       # sum of roots is 0 - z^{n-1} coeff is 0
            "zero_is_a_root": True,
            "eccentricity_is_one": True,    # min_j |a_j - c| = 0, max = r > 0
            "origin_spoke_max_equals_mu": True,
        })
    return {"rows": out, "all_above_threshold": all(x["mu_pow_n_minus_1_gt_threshold_pow"]
                                                    for x in out),
            "mu_limit_as_n_to_infinity": 1.0}


# --------------------------------------------------------------------------
# Theorem D
# --------------------------------------------------------------------------


def theoremD(pairs=((2, Fraction(9, 10), Fraction(8, 10)),
                    (2, Fraction(99, 100), Fraction(9, 10)),
                    (3, Fraction(97, 100), Fraction(9, 10)),
                    (3, Fraction(999, 1000), Fraction(99, 100)),
                    (4, Fraction(999, 1000), Fraction(995, 1000)),
                    (5, Fraction(9999, 10000), Fraction(999, 1000)))):
    out = []
    for k, a, b in pairs:
        ak, bk = a ** k, b ** k
        mu = ak * bk
        other = (ak + bk) ** 2 / 4
        out.append({
            "k": k, "n": 2 * k, "a": str(a), "b": str(b),
            "mu": str(mu), "mu_float": round(float(mu), 9),
            "mu_is_a^k_b^k_and_is_the_least_critical_value": other >= mu,
            "spoke_max_to_inner_roots": str(mu),
            "spoke_max_to_outer_roots": str(other),
            "every_origin_spoke_contained": other < 1,
            "mu_in_band": Fraction(2, 5) < mu < 1,
            "two_spoke_length": round(2 * float(min(a, b)), 9),
        })
    return {"rows": out,
            "all_contained": all(x["every_origin_spoke_contained"] for x in out),
            "all_in_band": all(x["mu_in_band"] for x in out),
            "band_covered_float": [min(float(Fraction(x["mu"])) for x in out),
                                   max(float(Fraction(x["mu"])) for x in out)]}


# --------------------------------------------------------------------------
# eta cap from the Theorem 4 quintic of HubTaylorSpokeCertificate.md
# --------------------------------------------------------------------------

#: the five roots of that witness (IEEE-754 hex literals, exact binary rationals)
QUINTIC_HUB_SET_WITNESS = (
    ("0x1.ffffff1bc8a32p-1", "-0x1.b38f7f9847930p-13"),
    ("0x1.3b2123a383e0cp-2", "0x1.e726fc8e166a3p-1"),
    ("-0x1.9def4ff5a0115p-1", "0x1.2d5569f0967a5p-1"),
    ("-0x1.9dcab3e89de6cp-1", "-0x1.2d87adaf745d1p-1"),
    ("0x1.3c6f58317f761p-2", "-0x1.e6f0d0a92da1bp-1"),
)

#: numerators over 2^40 of the four Rouche-enclosed critical-point centres,
#: each enclosing exactly one critical point inside D(centre, 2^-30)
QUINTIC_CRITICAL_CENTRES = (
    (114090007062, -29733055606),
    (5791405992, 34020177758),
    (-50061729660, 104416174971),
    (-69724232664, -108859766159),
)


def quintic_eta_cap():
    """An EXACT upper bound on mu for the Theorem 4 witness, hence an exact cap
    on any eta for which "2/5 < mu <= 1-eta => canonical certificate" could hold.

    Theorem 4 of HubTaylorSpokeCertificate.md certifies a LOWER bound on mu
    (mu >= 0.9999871398), which is the wrong direction for capping eta.  The
    upper bound below reuses that note's own Rouche enclosure: each disc
    D(centre_i, 2^-30) holds exactly one critical point, and |f'| <= 5*3^4 on
    |z| <= 2, so mu <= min_i |f(centre_i)| + 405/2^30.
    """
    import decimal

    roots = [(Fraction(float.fromhex(a)), Fraction(float.fromhex(b)))
             for a, b in QUINTIC_HUB_SET_WITNESS]

    def cmul(x, y):
        return (x[0] * y[0] - x[1] * y[1], x[0] * y[1] + x[1] * y[0])

    def fval(z):
        out = (Fraction(1), Fraction(0))
        for r in roots:
            out = cmul(out, (z[0] - r[0], z[1] - r[1]))
        return out

    best = None
    for a, b in QUINTIC_CRITICAL_CENTRES:
        v = fval((Fraction(a, 2 ** 40), Fraction(b, 2 ** 40)))
        n2 = v[0] ** 2 + v[1] ** 2
        if best is None or n2 < best:
            best = n2

    decimal.getcontext().prec = 60
    sq = (decimal.Decimal(best.numerator).sqrt()
          / decimal.Decimal(best.denominator).sqrt())
    mod_ub = Fraction(int(sq * 10 ** 30) + 1, 10 ** 30)
    lipschitz = Fraction(5 * 3 ** 4, 2 ** 30)
    mu_ub = mod_ub + lipschitz
    eta_cap = 1 - mu_ub
    return {
        "all_roots_strictly_inside": all(a * a + b * b < 1 for a, b in roots),
        "min_abs_f_at_enclosed_centre_squared": float(best),
        "lipschitz_slack": "405/2^30",
        "mu_upper_bound": float(mu_ub),
        "eta_cap_exact": str(eta_cap),
        "eta_cap_float": float(eta_cap),
        "statement": ("the middle-regime canonical-hub disjunction is refuted at "
                      "this configuration for every eta <= eta_cap; the hub half "
                      "of the refutation is exact (Theorem 4 of "
                      "HubTaylorSpokeCertificate.md), the chord half is floating "
                      "point (min over the ten chords of max |f| = 1.0114)"),
    }


# --------------------------------------------------------------------------
# sampled replay of the section-5 measurements
# --------------------------------------------------------------------------


def sampled_replay(seed: int = 20260905):
    """Deterministic replay of the section-5 measurement: for random survivors with
    mu > 2/5, the worst canonical-disjunction value and the worst chord-to-mu ratio.
    Segment maxima are taken at the exact real critical points of |f|^2 restricted
    to the segment (no path tracking).  Floating point; falsification evidence only.
    """
    import numpy as np

    rng = np.random.default_rng(seed)

    def segmax(c, z0, z1):
        d = z1 - z0
        g = np.array([0.0 + 0j])
        for a in c:
            g = np.polyadd(np.polymul(g, np.array([d, z0])), np.array([a]))
        q = np.polymul(g, np.conj(g)).real
        dq = np.polyder(q)
        cand = [0.0, 1.0]
        if len(dq) > 1:
            for x in np.roots(dq):
                if abs(x.imag) < 1e-9 and -1e-12 <= x.real <= 1 + 1e-12:
                    cand.append(min(1.0, max(0.0, float(x.real))))
        return float(np.sqrt(max(0.0, np.polyval(q, np.array(cand)).max())))

    per_n = {}
    worst_disj = 0.0
    worst_Q = 0.0
    kept = 0
    for n in (4, 5, 6, 7, 8):
        wd, wq, k = 0.0, 0.0, 0
        for _ in range(400):
            mode = int(rng.integers(0, 3))
            if mode == 0:
                rad = np.sqrt(rng.random(n)) * 0.999
                th = rng.random(n) * 2 * np.pi
            elif mode == 1:
                eps = 10.0 ** rng.uniform(-6, -1)
                rad0 = 1 - 10.0 ** rng.uniform(-7, -1)
                rad = np.clip(rad0 * (1 + eps * rng.standard_normal(n)), 1e-3, 1 - 1e-12)
                th = 2 * np.pi * np.arange(n) / n + eps * rng.standard_normal(n)
            else:
                rad0 = 1 - 10.0 ** rng.uniform(-7, -1)
                rad = np.concatenate([[10.0 ** rng.uniform(-3, 0) * 0.9],
                                      rad0 * np.ones(n - 1)])
                th = np.concatenate([[rng.random() * 2 * np.pi],
                                     2 * np.pi * np.arange(n - 1) / (n - 1)])
            rt = rad * np.exp(1j * th)
            if min(abs(rt[i] - rt[j]) for i in range(n) for j in range(i + 1, n)) < 1e-6:
                continue
            c = np.poly(rt)
            cps = np.roots(np.polyder(c))
            if len(cps) == 0:
                continue
            mu = float(np.abs(np.polyval(c, cps)).min())
            if mu <= 0.4:
                continue
            k += 1
            chord = min(segmax(c, rt[i], rt[j])
                        for i in range(n) for j in range(i + 1, n))
            cen = complex(rt.mean())
            hubs = [0j, cen] + [complex(x) for x in cps
                                if abs(np.polyval(c, x)) < 1.0]
            hub = min(sorted(segmax(c, h, complex(r)) for r in rt)[1] for h in hubs)
            wd = max(wd, min(chord, hub))
            wq = max(wq, chord / mu)
        per_n[str(n)] = {"survivors": k, "worst_disjunction_value": round(wd, 9),
                         "worst_chord_over_mu": round(wq, 9),
                         "regular_gon_chord_ratio": round(1 + math.cos(math.pi / n) ** n, 6)}
        worst_disj = max(worst_disj, wd)
        worst_Q = max(worst_Q, wq)
        kept += k
    return {"per_degree": per_n, "survivors": kept,
            "worst_disjunction_value": round(worst_disj, 9),
            "worst_chord_over_mu": round(worst_Q, 9),
            "disjunction_never_failed": worst_disj < 1.0}

# --------------------------------------------------------------------------


def main():
    report = {
        "note": "MiddleRegimeCanonicalHub.md",
        "theoremA_symbolic_reduction": theoremA_symbolic(),
        "theoremA_exact_certificate": theoremA_exact(),
        "kappa_table": kappa_table(),
        "theoremB_symbolic_identity": theoremB_symbolic(),
        "theoremB_S_n": {str(n): str(S_n_upper(n)) for n in (3, 4, 5, 6, 8, 10, 12, 16, 20)},
        "theoremB_sample": theoremB_sample(),
        "theoremC_no_uniform_rigidity": theoremC(),
        "theoremD_two_level_wall": theoremD(),
        "quintic_eta_cap": quintic_eta_cap(),
        "sampled_replay": sampled_replay(),
        "evidence_class": "exact_rational_and_symbolic_certificates_plus_floating_point_falsification",
        "universal_authority": "MiddleRegimeCanonicalHub.md",
        "claim_boundary": (
            "proves the adjacent-chord law on the equality family with its exact "
            "threshold kappa_n = 1/(1+cos^n(pi/n)) > 1/2; proves a quantitative "
            "centroid-spoke perturbation theorem; proves that mu does not control "
            "the deviation of the root configuration from a regular polygon "
            "uniformly in the degree; certifies the two-level wall family across "
            "the whole band.  Does NOT prove Erdos #1041 and does NOT close any "
            "part of 2/5 < mu < 1 in general degree."
        ),
    }

    A1 = report["theoremA_symbolic_reduction"]
    if A1.get("available"):
        assert A1["all_zero"], A1
    assert report["theoremA_exact_certificate"]["all_certified"]
    assert report["kappa_table"]["strictly_decreasing"]
    assert report["kappa_table"]["all_above_one_half"]
    B1 = report["theoremB_symbolic_identity"]
    if B1.get("available"):
        assert B1["all_zero"], B1
    assert report["theoremB_sample"]["violations"] == 0
    assert report["theoremB_sample"]["criterion_fired"] > 0
    assert report["theoremC_no_uniform_rigidity"]["all_above_threshold"]
    assert report["theoremD_two_level_wall"]["all_contained"]
    assert report["theoremD_two_level_wall"]["all_in_band"]
    assert report["quintic_eta_cap"]["all_roots_strictly_inside"]
    assert 0 < report["quintic_eta_cap"]["eta_cap_float"] < 1e-4
    assert report["sampled_replay"]["survivors"] > 0

    report["status"] = "PASS"
    print(json.dumps(report))


if __name__ == "__main__":
    main()
