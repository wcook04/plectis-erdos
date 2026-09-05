#!/usr/bin/env python3
"""Exterior coefficient energy S of a lemniscate ancestor component.

Verifies, in closed form and at 40 digits:

 1. the exterior model of a full connected lemniscate:  for monic f of degree n
    and a level t above every critical modulus, the exterior map of {|f| <= t}
    is  psi(w) = Lambda^{-1}(t^{1/n} w)  with  Lambda = f^{1/n},  so
    cap = t^{1/n} exactly and  Area/pi = cap^2 (1 - S),  S = sum_l l |beta_l|^2;

 2. for the n-fold symmetric family  f = z^n - q  at level t = 1 this gives the
    closed form  psi(w) = (w^n + q)^{1/n},  beta_{jn-1} = C(1/n,j) q^j,
        S(n,q) = sum_{j>=1} (jn - 1) C(1/n,j)^2 q^{2j},
    checked against an independent polar-area quadrature of {|z^n - q| <= 1};

 3. the separation threshold: the k = n roots of that family sit at
    pseudohyperbolic radius q^{1/n} in the uniformising disc and their adjacent
    pseudohyperbolic distance is  rho(n,q) = r|1-w|/|1-r^2 w|,  r = q^{1/n},
    w = exp(2 pi i/n);  for n = 2 this gives the exact identity
    q_threshold = tanh(1/a);

 4. THE NEGATIVE RESULT.  For every s0 > 0 there is a genuine polynomial
    lemniscate component that satisfies every inequality the
    ClusterSeparationLowCriticalClosure mechanism derives from failure --
    pairwise hyperbolic separation >= d_min(a), a base point h with
    lam_j <= delta(a)/2 for every j and sum_j lam_j = x, internal critical
    values >= t e^{-x}, roots in the open unit disc, t <= 1 -- and has S < s0.
    Hence the cap  a <= 1 - s0  is NOT available from the mechanism's state, and
    the exterior area theorem does not tighten the threshold on its own.

    (Honesty boundary: on this family the conclusion of Erdos 1041 is trivially
    true, so it is not a failure trajectory.  What it kills is the derivation of
    a uniform S-floor from the mechanism's own hypotheses.)

 5. the measured k-shaped floor  S * k in [0.448, 0.552]  on that family, and

 6. the conditional threshold table: what a uniform floor S >= s0 would buy in
    the comparison ODE (floating, recomputed here).

Usage:  check_erdos1041_exterior_energy_floor.py [--ode]
Prints one JSON line with status and evidence_class.
"""
from __future__ import annotations
import json, math, sys
import mpmath as mp

mp.mp.dps = 40


# ----------------------------------------------------------------- the family
def S_sym(n, q, J=6000):
    """S = sum_j (jn-1) C(1/n,j)^2 q^{2j}  for  psi(w) = (w^n + q)^{1/n}."""
    tot = mp.mpf(0); cb = mp.mpf(1)
    for j in range(1, J+1):
        cb = cb*(mp.mpf(1)/n - (j-1))/j
        term = (j*n - 1)*cb**2*q**(2*j)
        tot += term
        if j > 30 and abs(term) < mp.mpf(10)**(-34)*max(tot, mp.mpf(1)):
            break
    return tot


def area_polar(n, q, N=4000):
    """Independent area of {|z^n - q| <= 1}: for each angle phi solve
    |R^n e^{i n phi} - q| = 1 for R and integrate R^2/2."""
    n = int(n)
    def R_of(phi):
        c = mp.cos(n*phi)
        # R^{2n} - 2 q R^n cos(n phi) + q^2 - 1 = 0  ->  u = R^n
        disc = q*q*c*c - (q*q - 1)
        u = q*c + mp.sqrt(disc)
        return u**(mp.mpf(1)/n)
    tot = mp.mpf(0)
    for i in range(N):
        phi = 2*mp.pi*(i + mp.mpf(1)/2)/N
        tot += R_of(phi)**2
    return tot*mp.pi/N          # (1/2) * (2 pi / N) * sum R^2


def rho_adj(n, q):
    r = q**(mp.mpf(1)/n)
    w = mp.e**(2j*mp.pi/n)
    return abs(r - r*w)/abs(1 - r*r*w)


# ----------------------------------------------------- mechanism state bounds
def d_min(a):  return 4*mp.atanh(mp.sqrt(mp.tanh(1/mp.mpf(a))))
def rho_min(a): return mp.tanh(d_min(a)/2)
def delta(a):  return -mp.log(1 - mp.e**(-1/mp.mpf(a)))
def tau(a):    return -mp.log(mp.tanh(1/mp.mpf(a)))


def q_threshold(n, a):
    """least q with adjacent separation >= rho_min(a); the component's own
    area a = 1 - S(n,q) is used, so this is solved self-consistently."""
    lo, hi = mp.mpf('1e-9'), mp.mpf(1)
    for _ in range(160):
        mid = (lo + hi)/2
        if rho_adj(n, mid) < rho_min(a): lo = mid
        else: hi = mid
    return hi


def self_consistent(n):
    """fixed point of  a = 1 - S(n, q_threshold(n,a))."""
    a = mp.mpf(1)
    for _ in range(60):
        q = q_threshold(n, a)
        a_new = 1 - S_sym(n, q)
        if abs(a_new - a) < mp.mpf(10)**-30: a = a_new; break
        a = a_new
    q = q_threshold(n, a)
    return q, S_sym(n, q), a


# ---------------------------------------------------------- comparison ODE
def _delta(a):
    u = math.exp(-1/max(a, 1e-12))
    return -math.log1p(-u) if u < 1 else 1e9


def _lam(d): return -math.log(math.tanh(d/2))


def _d_min(a):
    v = min(math.sqrt(math.tanh(1/max(a, 1e-12))), 1-1e-16)
    return 4*math.atanh(v)


def _d_low(a):
    v = min(math.sqrt(1 - math.exp(-1/max(a, 1e-12))), 1-1e-16)
    return 2*math.atanh(v)


def Lam_corpus(k, a):
    dl = _d_low(a); dm = _d_min(a)
    return max(_lam(dl) + (k-1)*_lam(dm-dl), k*_lam(dm/2))


def Lam_pack(k, a):
    y = 2/max(a, 1e-12)
    if y > 600: return 1e9
    E = math.expm1(y); C = 1 + (k-1)*E
    t1 = 0.5*(C-1)*math.log((C+1)/(C-1)) if C > 1 else 0.0
    return _delta(a)/2 + (t1 + math.log((C+1)/2))/E


def k_lower(x, a, mode):
    if x <= 0: return 2.0
    L = (lambda k: Lam_corpus(k, a)) if mode == "corpus" else \
        (lambda k: min(Lam_corpus(k, a), Lam_pack(k, a)))
    lo, hi = 1.0, 2.0
    while L(hi) < x:
        hi *= 2
        if hi > 1e9: return 1e9
    for _ in range(60):
        m = 0.5*(lo+hi)
        if L(m) < x: lo = m
        else: hi = m
    return max(2.0, lo)


INV = 1/(2*math.pi**2)


def hit(a0, mode, cap, h=5e-4, xmax=4.0):
    x = 3e-5; a = min(a0, cap*0.999)
    while x < xmax:
        if a > cap: return x
        step = min(h, max(x/16, 1e-7))
        a1 = a
        for _ in range(40):
            k = k_lower(x+step, a1, mode)
            b = 2*math.sqrt(k) - math.sqrt(2*a1*(x+step+2))
            g = INV*b*b if b > 0 else 0.0
            a2 = a + step*g
            if abs(a2-a1) < 1e-13: a1 = a2; break
            a1 = a2
        a = a1; x += step
    return None


def worst(mode, cap, starts=13):
    W = 0.0
    for i in range(starts):
        a0 = 10**(-6*(1 - i/(starts-1)))
        t = hit(a0, mode, cap)
        if t is None: return None
        W = max(W, t)
    return W


# --------------------------------------------------------------------- main
def main():
    rep = {"status": "pass",
           "evidence_class": "closed_form_identity_plus_high_precision_witness"}
    checks = []

    # 1/2: exterior model vs independent polar area quadrature
    area_rows = []
    for n, q in [(2, mp.mpf('0.66')), (3, mp.mpf('0.5')), (5, mp.mpf('0.8')),
                 (7, mp.mpf('0.66')), (11, mp.mpf('0.9'))]:
        S = S_sym(n, q)
        A_model = mp.pi*(1 - S)                 # cap = t^{1/n} = 1 at t = 1
        A_quad = area_polar(n, q)
        rel = abs(A_model/A_quad - 1)
        area_rows.append({"n": n, "q": float(q), "S": float(S),
                          "area_rel_err": float(rel)})
        assert rel < mp.mpf('1e-9'), (n, q, rel)
    checks.append("exterior_area_identity")
    rep["area_identity"] = area_rows

    # 3: exact k = 2 threshold  q = tanh(1/a)
    for a in [mp.mpf('0.5'), mp.mpf('0.8'), mp.mpf(1)]:
        q2 = q_threshold(2, a)
        assert abs(q2 - mp.tanh(1/a)) < mp.mpf('1e-25'), (a, q2)
    checks.append("k2_threshold_equals_tanh_inv_a")

    # 4/5: the family table + the negative witness
    rows = []
    for n in [2, 3, 4, 5, 6, 7, 8, 10, 20, 50, 100, 200, 500, 1000]:
        q, S, a = self_consistent(n)
        x = -mp.log(q)
        # every mechanism inequality, checked
        lam_j = x/n                                  # = -log(q^{1/n})
        ok_cover = lam_j <= delta(a)/2
        ok_sep = rho_adj(n, q) >= rho_min(a) - mp.mpf('1e-30')
        ok_disc = q**(mp.mpf(1)/n) < 1
        rows.append({"k": n, "q": float(q), "x": float(x), "S": float(S),
                     "S_times_k": float(S*n), "a": float(a),
                     "lam_j": float(lam_j), "delta_over_2": float(delta(a)/2),
                     "cover_ok": bool(ok_cover), "separation_ok": bool(ok_sep),
                     "roots_in_disc": bool(ok_disc)})
        assert ok_cover and ok_sep and ok_disc, n
    rep["family"] = rows
    checks.append("mechanism_inequalities_satisfied_on_family")

    Sk = [r["S_times_k"] for r in rows]
    rep["S_times_k_range"] = [min(Sk), max(Sk)]
    inf_S = min(r["S"] for r in rows)
    rep["infimum_S_observed"] = inf_S
    assert inf_S < 0.001, inf_S
    checks.append("no_uniform_S_floor")

    # asymptotic law:  S ~ (1/n) log(1/(1-q^2))
    n = 1000; q, S, a = self_consistent(n)
    pred = mp.log(1/(1-q*q))/n
    rep["asymptotic_law"] = {"n": n, "S": float(S), "predicted": float(pred),
                             "rel": float(abs(S/pred - 1))}
    assert abs(S/pred - 1) < mp.mpf('0.02')
    checks.append("asymptotic_law_S_k_to_log")

    rep["checks"] = checks
    rep["conclusion"] = ("no uniform exterior-energy floor s0 > 0 follows from "
                         "the mechanism's failure inequalities; the only "
                         "measured floor is k-shaped, S*k in [0.448, 0.552]")

    if "--ode" in sys.argv:
        tab = {}
        for mode in ["corpus", "packing"]:
            row = {}
            for s0 in [0.0, 0.05, 0.10, 0.15, 0.20, 0.25]:
                X = worst(mode, 1-s0)
                row[f"{s0:.2f}"] = None if X is None else round(math.exp(-X), 5)
            tab[mode] = row
        rep["conditional_mu_threshold_if_S_geq_s0"] = tab
    else:
        rep["conditional_mu_threshold_if_S_geq_s0"] = "pass --ode (slow)"

    print(json.dumps(rep))
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
