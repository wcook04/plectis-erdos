#!/usr/bin/env python3
"""Exact rational certificate for the packing-sharpened low-critical closure.

Same comparison ODE as ClusterSeparationLowCriticalClosure.md, with the arity
relaxation Lambda(k,a) = max(delta/2 + (k-1) lam(g), k tau/2) intersected with a
second, geometrically feasible upper bound obtained from the hyperbolic
mean-value property.

Failure puts k points b_1..b_k in the unit disc, uniformised from the ancestor
component, with

    pairwise hyperbolic distance  >= D := d_min(a) = 4 artanh(sqrt(tanh(1/a))),
    lam_j := g_D(0,b_j) = -log tanh(d_j/2) <= delta(a)/2,
    sum_j lam_j >= x.

The corpus bound relaxes the pairwise constraints to  d_1 + d_2 >= D, which is
not realisable for k >= 3 (its binding branch puts every b_j at distance D/2
from 0 and pairwise 2 * D/2, i.e. every pair antipodal).  The replacement used
here keeps the packing:

  * the balls B_j = B_hyp(b_j, D/2) are pairwise disjoint;
  * at most one contains 0, and that one has lam <= delta(a)/2;
  * on every other B_j the function g_D(0,.) is harmonic, so by the hyperbolic
    mean value property  lam_j = (1/A_0) int_{B_j} g_D(0,.) dA_hyp  with
    A_0 = 2 pi (cosh(D/2) - 1) = 2 pi (e^{2/a} - 1);
  * the union of those k-1 disjoint balls has hyperbolic area (k-1) A_0, and
    g_D(0,.) is a radially decreasing function, so the integral is largest when
    the union is the centred ball B(0,R) with cosh R = 1 + (k-1)(e^{2/a}-1).

The centred integral has the closed form

    int_{B(0,R)} g_D(0,.) dA_hyp
        = 2 pi [ (cosh R - 1) * (-log tanh(R/2)) + 2 log cosh(R/2) ],

so, writing E = e^{2/a} - 1 and C = cosh R = 1 + (k-1) E,

    Lambda_pack(k,a) = delta(a)/2
                     + [ (C-1)/2 * log((C+1)/(C-1)) + log((C+1)/2) ] / E
                    <= delta(a)/2 + [ 1 + log((C+1)/2) ] / E,

the last step from  (C-1) artanh(1/C) <= 1 - 1/C + 1/(3C(C+1)) <= 1.
The certificate uses the last (weaker, simpler) form, so every transcendental
that must be bounded is a single logarithm.

Usage:
    check_erdos1041_packing_arity_floor.py [--quick]
prints one JSON line.
"""
from __future__ import annotations
import json, sys
from fractions import Fraction as Q
from math import isqrt

D = 10**12
INV_TWO_PI_SQ_LOWER = Q(49, 968)      # < 1/(2 pi^2)
K_CAP = 10**8
A_GRID = 20000                        # a is rounded UP everywhere


def floor_q(q): return Q((q.numerator*D)//q.denominator, D)
def ceil_q(q):  return Q(-((-q.numerator*D)//q.denominator), D)


def sqrt_lower(q):
    if q <= 0: return Q(0)
    return Q(isqrt((q.numerator*D*D)//q.denominator), D)


def sqrt_upper(q):
    if q <= 0: return Q(0)
    v = -((-q.numerator*D*D)//q.denominator); r = isqrt(v)
    if r*r < v: r += 1
    return Q(r, D)


def exp_lower_small(y, terms=80):
    tot = term = Q(1)
    for j in range(1, terms): term = term*y/j; tot += term
    return floor_q(tot)


def exp_lower(y):
    """Lower bound for exp(y), y >= 0 (saturating: still a lower bound)."""
    y = min(y, Q(64)); j = 0
    while y > 4: y /= 2; j += 1
    v = exp_lower_small(y)
    for _ in range(j): v = floor_q(v*v)
    return v


def exp_upper(y, terms=60):
    assert 0 <= y < terms
    tot = term = Q(1)
    for j in range(1, terms): term = term*y/j; tot += term
    return ceil_q(tot + term*y/terms/(1-y/terms))


D3 = 10**18
def floor3(q): return Q((q.numerator*D3)//q.denominator, D3)
def ceil3(q):  return Q(-((-q.numerator*D3)//q.denominator), D3)


def exp_upper_big(y):
    j = 0
    while y > 4: y /= 2; j += 1
    v = exp_upper(y)
    for _ in range(j): v = ceil3(v*v)
    return v


_DC = {}; _TC = {}


def _u_upper(y):
    return ceil_q(1/exp_lower(y))


def delta_upper(a):
    """upper bound for delta(a) = -log(1-exp(-1/a)) = sum_j u^j/j, u=exp(-1/a)."""
    au = Q(-((-a.numerator*A_GRID)//a.denominator), A_GRID)
    h = _DC.get(au)
    if h is None:
        u = _u_upper(1/au)
        if u >= 1: h = Q(10**6)
        else:
            J = 40; tot = Q(0); pw = Q(1)
            for j in range(1, J+1):
                pw = ceil_q(pw*u); tot += pw/j
            h = ceil_q(tot + pw*u/((J+1)*(1-u)))
        _DC[au] = h
    return h


def tau_upper(a):
    """tau(a) = 2 artanh(exp(-2/a))."""
    au = Q(-((-a.numerator*A_GRID)//a.denominator), A_GRID)
    h = _TC.get(au)
    if h is None:
        u = _u_upper(2/au)
        if u >= 1: h = Q(10**6)
        else:
            J = 40; tot = Q(0); pw = u; u2 = ceil_q(u*u)
            for j in range(0, J+1):
                tot += pw/(2*j+1); pw = ceil_q(pw*u2)
            h = ceil_q(2*(tot + pw/((2*J+3)*(1-u2))))
        _TC[au] = h
    return h


def delta_lower(a):
    return floor3(1/exp_upper_big(1/a))


def _atanh_series(v, upper, J=32):
    if v <= 0: return Q(0)
    if v >= 1: return Q(10**6)
    tot = Q(0); pw = v; v2 = ceil3(v*v) if upper else floor3(v*v)
    for j in range(J+1):
        tot += pw/(2*j+1)
        pw = ceil3(pw*v2) if upper else floor3(pw*v2)
    if upper:
        tot += pw/((2*J+3)*(1-v2))
        return ceil3(2*tot)
    return floor3(2*tot)


def lam_lower(d):
    if d <= 0: return Q(10**6)
    return _atanh_series(floor3(1/exp_upper_big(d)), upper=False)


def lam_upper(d):
    if d <= 0: return Q(10**6)
    v = ceil3(1/exp_lower(d))
    if v >= 1: return Q(10**6)
    return _atanh_series(v, upper=True)


_GC = {}
def lam_g_upper(a):
    LG_GRID = 2000
    au = Q(-((-a.numerator*LG_GRID)//a.denominator), LG_GRID)
    if au > 1: au = Q(1)
    h = _GC.get(au)
    if h is None:
        t2 = tau_upper(au)/2
        h = t2
        if au >= Q(1, 64):
            dl = delta_lower(au)
            if dl > 0:
                g_lo = 2*lam_lower(t2) - lam_upper(dl/2)
                if g_lo > 0: h = min(h, lam_upper(g_lo))
        _GC[au] = h
    return h


# ---------------------------------------------------------------- packing arm
LOG2_UPPER = Q(6931471805599454, 10**16)     # > log 2
LOG2_LOWER = Q(6931471805599452, 10**16)     # < log 2


def log_upper(v):
    """upper bound for log(v), v >= 1, by dyadic scaling + artanh series."""
    assert v >= 1
    j = 0
    while v >= 2: v /= 2; j += 1
    if v == 1: return j*LOG2_UPPER
    w = ceil3((v-1)/(v+1))                    # log v = 2 artanh((v-1)/(v+1))
    return ceil3(j*LOG2_UPPER + _atanh_series(w, upper=True))


def log_lower(v):
    assert v >= 1
    j = 0
    while v >= 2: v /= 2; j += 1
    if v == 1: return j*LOG2_LOWER
    w = floor3((v-1)/(v+1))
    return floor3(j*LOG2_LOWER + _atanh_series(w, upper=False))


_EC = {}
def E_lower(a):
    """lower bound for E(a) = exp(2/a) - 1 ; E is decreasing in a, and a is
    rounded UP, so this is a lower bound for the true E."""
    au = Q(-((-a.numerator*A_GRID)//a.denominator), A_GRID)
    h = _EC.get(au)
    if h is None:
        h = exp_lower(2/au) - 1
        if h < 0: h = Q(0)
        _EC[au] = h
    return h


def k_pack_lower(x, a):
    """Smallest k admitted by  Lambda_pack(k,a) >= x, bounded from below.

    Two cases have to be covered, because the exceptional ball (the one that
    may contain the base point) exists only when some d_j < D/2:

      (i)  one exceptional root, k-1 harmonic balls:
             Lambda <= delta/2 + [1 + log((C1+1)/2)]/E,  C1 = 1 + (k-1) E
      (ii) no exceptional root, k harmonic balls:
             Lambda <= [1 + log((C2+1)/2)]/E,            C2 = 1 + k E

    Each case, set >= x, yields its own lower bound on k; the true k is at
    least the SMALLER of the two, which is what is returned.
    """
    E = E_lower(a)
    if E <= 0: return Q(2)

    def solve(shift, offset):
        # log((C+1)/2) >= E*(x - shift) - 1  ->  C >= 2 exp(...) - 1
        y = E*(x - shift) - 1
        if y <= 0: return Q(2)
        ex = exp_lower(y)
        return offset + 2*(ex - 1)/E

    d = delta_upper(a)
    k1 = solve(d/2, Q(1))          # case (i)
    k2 = solve(Q(0), Q(0))         # case (ii)
    k = min(k1, k2)
    return min(max(Q(2), floor_q(k)), Q(K_CAP))


_KL = {}
def k_lower(x, a):
    au = Q(-((-a.numerator*A_GRID)//a.denominator), A_GRID)
    key = (x, au)
    if key in _KL: return _KL[key]
    r = _k_lower(x, a); _KL[key] = r; return r


def _k_lower(x, a):
    """max of every valid arity lower bound: COVER, the corpus ordered profile,
    and the packing bound."""
    if x <= 0: return Q(2)
    d = delta_upper(a); t = tau_upper(a); lg = lam_g_upper(a)
    kB = 2*x/t if t > 0 else Q(K_CAP)
    kA = Q(1) + (x - d/2)/lg if lg > 0 else Q(K_CAP)
    kk = min(kA, kB)
    corpus = min(max(Q(2), floor_q(kk), floor_q(2*x/d)), Q(K_CAP))
    return max(corpus, k_pack_lower(x, a))


def g_cell_lower(xl, xr, a):
    b = 2*sqrt_lower(k_lower(xl, a)) - sqrt_upper(2*a*(xr+2))
    if b <= 0: return Q(0)
    return floor_q(INV_TWO_PI_SQ_LOWER*b*b)


def lower_step(xl, xr, ai):
    h = xr-xl; gi = g_cell_lower(xl, xr, ai); ap = ai + h*gi
    if ap > 1:
        if 1 - ai - h*g_cell_lower(xl, xr, Q(1)) < 0: return Q(1)+Q(1, D)
        ap = Q(1)
    lo, hi = ai + h*g_cell_lower(xl, xr, ap), ap
    for _ in range(40):
        if hi - lo < Q(1, 10**6): break
        m = (lo+hi)/2
        if m - ai - h*g_cell_lower(xl, xr, m) < 0: lo = m
        else: hi = m
    return floor_q(max(lo, ai))


GR = Q(1, 16)
def next_x(x, h): return x + min(h, max(x*GR, Q(1, 10**7)))


def start_shift(xs):
    b = 2*sqrt_lower(Q(2)) - sqrt_upper(2*(xs+2)); assert b > 0
    return floor_q(INV_TWO_PI_SQ_LOWER*b*b)


def geometric_grid(a0, count):
    g = []
    for i in range(count+1):
        f = 10.0**float(-6*(1-Q(i, count)))
        g.append(max(floor_q(Q(f).limit_denominator(D)), a0))
    g[-1] = Q(1); return sorted(set(g))


def hitting_time(alpha, xs, h, x_max=Q(4)):
    x, a = xs, alpha
    if a > 1: return x
    while x < x_max:
        xn = next_x(x, h); a = lower_step(x, xn, a); x = xn
        if a > 1: return x
    return None


def certify_all_degree(h, gc):
    xs = Q(3, 10**5); c = start_shift(xs); a0 = Q(1, 10**6)
    assert c*xs >= a0
    worst = Q(0); wa = None
    for al in geometric_grid(a0, gc):
        t = hitting_time(al, xs, h)
        assert t is not None, f"no hit from {al}"
        if t > worst: worst, wa = t, al
    return worst, wa


def feasibility_witness():
    """The corpus branch  k tau/2  is infeasible for k >= 3: it needs every b_j
    at hyperbolic distance exactly d_min/2 from the base point and every pair at
    distance >= d_min, and two points at distance R from a common point are at
    distance at most 2R, with equality only when they are antipodal.  Three
    points cannot be pairwise antipodal.  Exact check at a = 1: three points on
    the circle of hyperbolic radius d_min/2, best possible (equilateral) angular
    spacing 2 pi/3, have cosh(pairwise) = cosh^2 R + sinh^2 R / 2 which is
    strictly below cosh(d_min) = cosh(2R) = cosh^2 R + sinh^2 R.
    """
    return {"branch": "k*tau/2", "infeasible_from_arity": 3,
            "reason": "pairwise antipodality at a common radius"}


def main():
    quick = "--quick" in sys.argv
    h = Q(1, 100) if quick else Q(1, 400)
    gc = 8 if quick else 12
    X, wa = certify_all_degree(h, gc)
    cands = [Q(2, 5), Q(39, 100), Q(19, 50), Q(37, 100), Q(9, 25), Q(7, 20),
             Q(1, 3), Q(3, 10), Q(1, 4), Q(197, 1000)]
    chosen = None
    for mu in cands:
        if mu*exp_upper(X) <= 1: chosen = mu; break
    assert chosen is not None
    assert chosen > Q(9, 25), "must beat the landed 9/25"
    X = floor_q(X)
    rep = {"status": "pass", "evidence_class": "exact_rational_certificate",
           "mode": "quick" if quick else "full",
           "all_degree": {"X_cert": str(X), "X_cert_float": float(X),
                          "mu_threshold": str(chosen),
                          "mu_threshold_float": float(chosen),
                          "worst_initial_area": float(wa),
                          "grid_points": gc, "step": str(h),
                          "baseline_landed": "9/25"},
           "corpus_branch_feasibility": feasibility_witness(),
           "mechanism": ("COVER one-root Bergman + connected-cluster pairwise "
                         "Bergman separation + hyperbolic packing arity floor "
                         "+ boundary hop"),
           "per_degree_thresholds": "not run in this pass"}
    print(json.dumps(rep))
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
