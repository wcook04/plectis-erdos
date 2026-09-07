#!/usr/bin/env python3
"""Verifier for ConcyclicSpokeCalculus.md (Erdos #1041, concyclic zeros).

Checks, in order:

  T1  spoke normal form      |g(t w_j)|^2 = prod_k [ (1-t)^2 + t |w_j-w_k|^2 ]
  T2  orbit balance          sum_j log|g(t w_j)| = - sum_m |s_m|^2 t^m / m
  T3  sharp radial law       (i) ceiling (1-t)(1+t)^{n-1}
                             (ii) max 2^n (n-1)^{n-1}/n^n
                             (iii) monotone for t >= (n-2)/n, sharp
                             (iv) arm-free radius s_n^*
  T4  no-go                  exact rational witnesses with at most one contained
                             full spoke and no contained root chord
  NC  negative control       the adversarial searcher must break a neighbouring
                             FALSE statement at the same budget

T1, T2 and T4 are decided in exact rational arithmetic (fractions.Fraction) at
Gaussian-rational zeros ((1-p^2)+2pi)/(1+p^2); no floating point enters those
verdicts.  Every maximum on a segment or spoke in the float arm comes from the
exact critical points of a real polynomial, never from a sample.

Usage:  ./repo-python formal_math/erdos257_period_noncollapse/ErdosProblems/Erdos1041/scripts/check_erdos1041_concyclic_spoke_calculus.py [--quick]
"""
from __future__ import annotations
import argparse, json, math, os, sys
from fractions import Fraction as F

import numpy as np

REPO = os.path.abspath(os.path.join(os.path.dirname(__file__), *[os.pardir]*5))
RECEIPT = os.path.join(REPO, 'state', 'formal_math', 'erdos257_period_noncollapse',
                       'erdos1041_concyclic_spoke_calculus_receipt.json')

# ---------------------------------------------------------------- exact arm

def wpt(p):
    """Gaussian-rational point on the unit circle."""
    p = F(p); d = 1 + p * p
    return ((F(1) - p * p) / d, (2 * p) / d)

def val2(z, W):
    """|g(z)|^2 for z=(x,y) and W a list of exact circle points."""
    x, y = z; acc = F(1)
    for (a, b) in W:
        acc *= (x - a) * (x - a) + (y - b) * (y - b)
    return acc

def exact_T1(nmax=7, steps=12):
    bad = 0; total = 0
    for n in range(2, nmax + 1):
        W = [wpt(F(k + 1, k + 3)) for k in range(n)]
        for j in range(n):
            cx, cy = W[j]
            for i in range(steps + 1):
                t = F(i, steps)
                lhs = val2((t * cx, t * cy), W)
                rhs = F(1)
                for (a, b) in W:
                    d2 = (cx - a) ** 2 + (cy - b) ** 2
                    rhs *= (1 - t) ** 2 + t * d2
                total += 1
                if lhs != rhs:
                    bad += 1
    return bad, total

def exact_T2(nmax=7, steps=12):
    """prod_j |g(t w_j)|^2 == prod_{j,k} (1 + t^2 - 2 t cos(phi_j-phi_k)), and <= 1."""
    bad = 0; le1 = 0; total = 0
    for n in range(2, nmax + 1):
        W = [wpt(F(k + 1, k + 3)) for k in range(n)]
        for i in range(steps + 1):
            t = F(i, steps)
            lhs = F(1)
            for j in range(n):
                cx, cy = W[j]
                lhs *= val2((t * cx, t * cy), W)
            rhs = F(1)
            for j in range(n):
                for k in range(n):
                    c = W[j][0] * W[k][0] + W[j][1] * W[k][1]
                    rhs *= 1 + t * t - 2 * t * c
            total += 1
            if lhs != rhs:
                bad += 1
            if lhs <= 1:
                le1 += 1
    return bad, le1, total

WITNESSES = {
    3: ['72/1831', '1424/977', '-1761/1424'],
    5: ['107/129', '165/64', '-5309/1883', '-1164/1651', '-145/1873'],
    6: ['65/1281', '379/683', '2095/1331', '-53395/1323', '-601/339', '-955/1489'],
}

def exact_T4(ps, M=600):
    """Return (n_contained_spokes, all_chords_exceed, spoke_certs, chord_certs)."""
    W = [wpt(F(p)) for p in ps]; n = len(W)
    spoke = []
    for j in range(n):
        cx, cy = W[j]; best = F(0); bt = F(0)
        for i in range(M + 1):
            t = F(i, M)
            v = val2((t * cx, t * cy), W)
            if v > best:
                best, bt = v, t
        spoke.append((best, bt))
    contained = sum(1 for v, _ in spoke if v <= 1)
    chords = {}
    all_exceed = True
    for a in range(n):
        for b in range(a + 1, n):
            ax, ay = W[a]; bx, by = W[b]; best = F(0); bt = F(0)
            for i in range(M + 1):
                s = F(i, M)
                v = val2((ax + s * (bx - ax), ay + s * (by - ay)), W)
                if v > best:
                    best, bt = v, s
            chords[(a, b)] = (best, bt)
            if best <= 1:
                all_exceed = False
    return contained, all_exceed, spoke, chords

# ---------------------------------------------------------------- float arm

def _polymax01(poly):
    dc = poly[1:] * np.arange(1, len(poly))
    ts = [0.0, 1.0]
    if np.any(dc != 0):
        r = np.roots(dc[::-1]); r = r[np.abs(r.imag) < 1e-10].real
        ts += [float(t) for t in r if 0.0 <= t <= 1.0]
    ts = np.clip(np.asarray(ts), 0.0, 1.0)
    v = np.polyval(poly[::-1], ts)
    i = int(v.argmax())
    return float(v[i]), float(ts[i])

def spoke_poly(ph, j):
    poly = np.array([1.0])
    for ck in np.cos(ph[j] - ph):
        poly = np.convolve(poly, np.array([1.0, -2.0 * ck, 1.0]))
    return poly

def seg_poly(p, q, W):
    d = q - p; poly = np.array([1.0])
    for w in W:
        a = p - w
        poly = np.convolve(poly, np.array([abs(a) ** 2, 2.0 * (a.conjugate() * d).real, abs(d) ** 2]))
    return poly

def Cprime(ph):
    ph = np.sort(np.asarray(ph, float) % (2 * np.pi)); n = len(ph); W = np.exp(1j * ph)
    sm = np.sort([_polymax01(spoke_poly(ph, j))[0] for j in range(n)])
    ch = min(_polymax01(seg_poly(W[a], W[b], W))[0] for a in range(n) for b in range(a + 1, n))
    return float(np.sqrt(min(sm[1], ch)))

def worst_chord(ph):
    """objective of the neighbouring FALSE statement 'every root chord is contained'."""
    ph = np.sort(np.asarray(ph, float) % (2 * np.pi)); n = len(ph); W = np.exp(1j * ph)
    return float(np.sqrt(max(_polymax01(seg_poly(W[a], W[b], W))[0]
                             for a in range(n) for b in range(a + 1, n))))

def climb(obj, n, rng, iters, seed_ph=None):
    ph = np.sort(rng.uniform(0, 2 * np.pi, n)) if seed_ph is None else np.array(seed_ph, float)
    best = obj(ph); step = 0.35
    for it in range(iters):
        cand = np.sort((ph + rng.normal(0, step, n)) % (2 * np.pi))
        if np.min(np.diff(np.r_[cand, cand[0] + 2 * np.pi])) < 1e-7:
            continue
        v = obj(cand)
        if v > best:
            best, ph = v, cand
        if it % 60 == 59:
            step *= 0.65
    return best, ph

def arm_free_radius(n):
    if n == 2:
        return 0.0
    lo, hi = (n - 2) / n, 1.0 - 1e-15
    f = lambda s: (1 - s) * (1 + s) ** (n - 1) - 1.0
    for _ in range(200):
        mid = (lo + hi) / 2
        if f(mid) > 0: lo = mid
        else: hi = mid
    return (lo + hi) / 2

# ---------------------------------------------------------------- main

def _dump(R):
    os.makedirs(os.path.dirname(RECEIPT), exist_ok=True)
    with open(RECEIPT, 'w') as fh:
        json.dump(R, fh, indent=1, sort_keys=True)


def main() -> int:
    ap = argparse.ArgumentParser()
    ap.add_argument('--quick', action='store_true')
    args = ap.parse_args()
    quick = args.quick
    rng = np.random.default_rng(20260824)
    R: dict = {'schema': 'erdos1041_concyclic_spoke_calculus_receipt_v1',
               'note': 'formal_math/erdos257_period_noncollapse/ErdosProblems/Erdos1041/ConcyclicSpokeCalculus.md'}
    fails: list[str] = []

    nmax = 5 if quick else 6
    print('[1/6] exact T1 ...', flush=True)
    bad, tot = exact_T1(nmax)
    R['T1_exact'] = {'mismatches': bad, 'checks': tot, 'n_range': [2, nmax]}
    if bad: fails.append('T1 exact mismatch')

    _dump(R)
    print('[2/6] exact T2 ...', flush=True)
    bad, le1, tot = exact_T2(nmax)
    R['T2_exact'] = {'mismatches': bad, 'product_le_one': le1, 'checks': tot}
    if bad or le1 != tot: fails.append('T2 exact mismatch or product > 1')

    _dump(R)
    print('[3/6] T2 power series ...', flush=True)
    worst = 0.0
    for n in range(2, 9):
        ph = np.sort(rng.uniform(0, 2 * np.pi, n)); W = np.exp(1j * ph)
        for t in (0.1, 0.3, 0.5, 0.7, 0.9, 0.97):
            lhs = sum(float(np.log(abs(np.prod(t * W[j] - W)))) for j in range(n))
            rhs = -sum((abs(np.sum(W ** m)) ** 2) * t ** m / m for m in range(1, 4000))
            worst = max(worst, abs(lhs - rhs))
    R['T2_power_series_max_abs_error'] = worst
    if worst > 1e-9: fails.append('T2 power series disagreement')

    _dump(R)
    print('[4/6] T3 sweep ...', flush=True)
    # T3  (derivative sweep vectorised over t and k; ceiling on a smaller sample)
    trials = 200 if quick else 700
    ceil_trials = 40 if quick else 120
    viol = 0; ceil_ratio = 0.0; sharp = []
    for n in range(2, 13):
        tn = (n - 2) / n
        ceil = 2 ** n * (n - 1) ** (n - 1) / n ** n
        tgrid = np.linspace(tn, 0.9995, 60)[:, None, None]
        for it in range(trials):
            ph = np.sort(rng.uniform(0, 2 * np.pi, n))
            C = np.cos(ph[:, None] - ph[None, :])[None, :, :]
            D = ((tgrid - C) / (1 - 2 * tgrid * C + tgrid ** 2)).sum(axis=2)
            viol += int((D > 1e-9).sum())
            if it < ceil_trials:
                for j in range(n):
                    m2, _ = _polymax01(spoke_poly(ph, j))
                    ceil_ratio = max(ceil_ratio, math.sqrt(m2) / ceil)
        eps = 1e-6
        php = np.array([0.0] + [np.pi + eps * (i + 1) for i in range(n - 1)])
        tt = np.linspace(0.0, 0.999, 20001)
        v = np.array([sum(np.log(abs(t - np.exp(1j * p))) for p in php) for t in tt])
        sharp.append({'n': n, 'argmax': float(tt[int(v.argmax())]), 'predicted': tn})
    R['T3_monotonicity_violations_above_threshold'] = viol
    R['T3_ceiling_max_ratio'] = ceil_ratio
    R['T3_sharpness'] = sharp
    R['T3_arm_free_radius'] = {str(n): arm_free_radius(n) for n in range(2, 13)}
    if viol: fails.append('T3(iii) monotonicity violated above (n-2)/n')
    if ceil_ratio > 1 + 1e-12: fails.append('T3(ii) ceiling exceeded')
    if max(abs(s['argmax'] - s['predicted']) for s in sharp) > 1e-4:
        fails.append('T3(iii) sharpness argmax mismatch')

    _dump(R)
    print('[5/6] T4 exact witnesses ...', flush=True)
    R['T4_witnesses'] = {}
    for n, ps in WITNESSES.items():
        contained, all_exceed, spoke, chords = exact_T4(ps, M=200 if quick else 600)
        wc = min(chords.values(), key=lambda kv: kv[0])
        R['T4_witnesses'][str(n)] = {
            'p': ps,
            'contained_full_spokes': contained,
            'all_root_chords_exceed_one': bool(all_exceed),
            'spoke_certificates': [{'value_sq': float(v), 'value_sq_exact': str(v), 't': str(t)}
                                   for v, t in spoke],
            'weakest_chord_certificate_sq': float(wc[0]),
        }
        if contained > 1 or not all_exceed:
            fails.append(f'T4 witness n={n} does not certify the no-go')

    _dump(R)
    print('[6/6] adversarial + negative control ...', flush=True)
    iters = 120 if quick else 220
    sup = {}
    for n in range(3, 8 if quick else 9):
        reg = np.array([2 * np.pi * j / n for j in range(n)])
        rec = -1.0
        seeds = [None, np.sort((reg + rng.normal(0, 0.05, n)) % (2 * np.pi))]
        if n in WITNESSES:                       # start from the certified witness
            wph = np.sort(np.array([2.0 * math.atan(float(F(x))) % (2 * np.pi)
                                    for x in WITNESSES[n]]))
            sup[str(n) + '_witness_Cprime'] = Cprime(wph)
            seeds.append(wph)
        for sd in seeds:
            v, _ = climb(Cprime, n, rng, iters, sd)
            rec = max(rec, v)
        sup[str(n)] = rec
    R['adversarial_sup_Cprime'] = sup
    nc = {}
    for n in range(3, 8):
        v, _ = climb(worst_chord, n, rng, iters)
        nc[str(n)] = v
    R['negative_control_false_statement_reached'] = nc
    # the control must clear the same budget 1 by a margin far larger than the
    # ~1% by which C' is exceeded; 1.15 is the observed n=3 floor of the FALSE
    # statement's own supremum, so a weaker searcher would fall below it.
    R['negative_control_separation_ratio'] = {
        k: (nc[k] - 1.0) / max(sup.get(k, 1.0) - 1.0, 1e-12) for k in nc}
    if min(nc.values()) < 1.15:
        fails.append('negative control did not break the false statement')

    R['regular_ngon_Cprime'] = {str(n): Cprime(np.array([2 * np.pi * j / n for j in range(n)]))
                                for n in range(3, 9)}
    R['verdict'] = 'PASS' if not fails else 'FAIL'
    R['failures'] = fails
    _dump(R)
    print(json.dumps({k: R[k] for k in
                      ('verdict', 'failures', 'T1_exact', 'T2_exact',
                       'T2_power_series_max_abs_error',
                       'T3_monotonicity_violations_above_threshold',
                       'T3_ceiling_max_ratio', 'adversarial_sup_Cprime',
                       'negative_control_separation_ratio',
                       'negative_control_false_statement_reached')}, indent=1))
    print(f'receipt -> {RECEIPT}')
    return 0 if not fails else 1

if __name__ == '__main__':
    raise SystemExit(main())
