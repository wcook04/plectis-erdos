#!/usr/bin/env python3
# SPDX-FileCopyrightText: 2026 Will Cook
# SPDX-License-Identifier: Apache-2.0
"""Exact rational certificate for the low-critical path theorem.

Proof: research_corpus/Erdos1041/LowCriticalPathCertificate.md.
Run from this repository with Python 3. NumPy and SciPy accelerate the
proposal stage; all accepted bounds use fractions.Fraction arithmetic.
Use --quick for 51/100, no flag for 13/25, --geometry-audit for the
circle-slice tests, and --comparison-audit for the area-step regression.
"""
from __future__ import annotations
import json, sys, heapq
from fractions import Fraction as Q
from math import isqrt

D = 10**12
D3 = 10**18
INV_TWO_PI_SQ_LOWER = Q(49, 968)      # < 1/(2 pi^2)
K_CAP = 10**8
A_GRID = 20000                        # a is rounded UP everywhere

PI_LOWER = Q(3141592653589793, 10**15)
PI_UPPER = Q(3141592653589794, 10**15)


def floor_q(q): return Q((q.numerator*D)//q.denominator, D)
def ceil_q(q):  return Q(-((-q.numerator*D)//q.denominator), D)
def floor3(q):  return Q((q.numerator*D3)//q.denominator, D3)
def ceil3(q):   return Q(-((-q.numerator*D3)//q.denominator), D3)

D9 = 10**9
def fl9(q): return Q((q.numerator*D9)//q.denominator, D9)
def ce9(q): return Q(-((-q.numerator*D9)//q.denominator), D9)


def sqrt_lower(q):
    if q <= 0: return Q(0)
    return Q(isqrt((q.numerator*D*D)//q.denominator), D)


def sqrt_upper(q):
    if q <= 0: return Q(0)
    v = -((-q.numerator*D*D)//q.denominator); r = isqrt(v)
    if r*r < v: r += 1
    return Q(r, D)


def exp_lower_small(y, terms=80):
    """Lower bound for exp(y), 0 <= y <= 4.  Every term is rounded DOWN, so the
    partial sum stays below the true series."""
    tot = term = Q(1)
    for j in range(1, terms):
        term = floor3(term*y/j)
        if term <= 0: break
        tot = floor3(tot + term)
    return floor_q(tot)


_EXPL = {}
def exp_lower(y):
    """Lower bound for exp(y), y >= 0 (saturating: still a lower bound)."""
    hit = _EXPL.get(y)
    if hit is not None: return hit
    y0 = y
    y = min(y, Q(64)); j = 0
    while y > 4: y /= 2; j += 1
    v = exp_lower_small(y)
    for _ in range(j): v = floor_q(v*v)
    if len(_EXPL) < 400000: _EXPL[y0] = v
    return v


def exp_upper(y, terms=60):
    """Upper bound for exp(y), 0 <= y < terms.  Every term is rounded UP, so the
    partial sum and the geometric tail both dominate the true series."""
    assert 0 <= y < terms
    tot = term = Q(1)
    for j in range(1, terms):
        term = ceil3(term*y/j); tot = ceil3(tot + term)
    return ceil_q(tot + term*y/terms/(1-y/terms))


_EXPU = {}
def exp_upper_big(y):
    hit = _EXPU.get(y)
    if hit is not None: return hit
    y0 = y; j = 0
    while y > 4: y /= 2; j += 1
    v = exp_upper(y)
    for _ in range(j): v = ceil3(v*v)
    if len(_EXPU) < 400000: _EXPU[y0] = v
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
        tot = ceil3(tot + pw/(2*j+1)) if upper else floor3(tot + pw/(2*j+1))
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


# ---------------------------------------------------------------- logs
LOG2_UPPER = Q(6931471805599454, 10**16)     # > log 2
LOG2_LOWER = Q(6931471805599452, 10**16)     # < log 2


def log_upper(v):
    assert v >= 1
    j = 0
    while v >= 2: v /= 2; j += 1
    if v == 1: return j*LOG2_UPPER
    w = ceil3((v-1)/(v+1))
    return ceil3(j*LOG2_UPPER + _atanh_series(w, upper=True))


def log_lower(v):
    assert v >= 1
    j = 0
    while v >= 2: v /= 2; j += 1
    if v == 1: return j*LOG2_LOWER
    w = floor3((v-1)/(v+1))
    return floor3(j*LOG2_LOWER + _atanh_series(w, upper=False))


# ---------------------------------------------------------------- packing arm
_EC = {}
def E_lower(a):
    au = Q(-((-a.numerator*A_GRID)//a.denominator), A_GRID)
    h = _EC.get(au)
    if h is None:
        h = exp_lower(2/au) - 1
        if h < 0: h = Q(0)
        _EC[au] = h
    return h


def k_pack_lower(x, a):
    E = E_lower(a)
    if E <= 0: return Q(2)

    def solve(shift, offset):
        y = E*(x - shift) - 1
        if y <= 0: return Q(2)
        return offset + 2*(exp_lower(y) - 1)/E

    d = delta_upper(a)
    k = min(solve(d/2, Q(1)), solve(Q(0), Q(0)))
    return min(max(Q(2), k), Q(K_CAP))


# ------------------------------------------------------- hyperbolic primitives
def exp_neg_lower(y):  return floor3(1/exp_upper_big(y)) if y > 0 else Q(1)
def exp_neg_upper(y):  return ceil3(1/exp_lower(y)) if y > 0 else Q(1)


_TRIG = {}
def trig(y):
    """(cosh upper, sinh upper, sinh lower) at y > 0, cached."""
    v = _TRIG.get(y)
    if v is None:
        eu = exp_upper_big(y); el = exp_lower(y)
        nu = ceil3(1/el); nl = floor3(1/eu)
        sl = floor3((el - nu)/2)
        v = (ceil3((eu + nu)/2), ceil3((eu - nl)/2), sl if sl > 0 else Q(0))
        _TRIG[y] = v
    return v


def cosh_upper(y):
    y = abs(y)
    if y == 0: return Q(1)
    return trig(y)[0]


def sinh_upper(y):
    return trig(y)[1]


def cosh_diff_upper(td, tr):
    """upper bound for cosh(d-r) from the cached triples at d and r,
    via cosh(d-r) = cosh d cosh r - sinh d sinh r."""
    return ceil3(td[0]*tr[0] - td[2]*tr[2])


# arcsin, via the everywhere-positive series  sum_n C(2n,n)/(4^n (2n+1)) z^(2n+1)
_ASIN_N = 90
_ASIN_LO = []
_ASIN_HI = []
_c = Q(1)
for _n in range(_ASIN_N + 1):
    _t = _c/(2*_n+1)
    _ASIN_LO.append(floor3(_t)); _ASIN_HI.append(ceil3(_t))
    _c = _c*Q(2*_n+1, 2*_n+2)


def _asin_series_lower(z):
    tot = Q(0); pw = z; z2 = floor3(z*z)
    for n in range(_ASIN_N+1):
        tot = floor3(tot + _ASIN_LO[n]*pw)
        pw = floor3(pw*z2)
        if pw == 0: break
    return floor3(tot)


def _asin_series_upper(z):
    tot = Q(0); pw = z; z2 = ceil3(z*z)
    if z2 >= 1: return PI_UPPER/2
    for n in range(_ASIN_N+1):
        tot = ceil3(tot + _ASIN_HI[n]*pw)
        pw = ceil3(pw*z2)
    return ceil3(tot + pw/((2*_ASIN_N+3)*(1-z2)))


def asin_lower(z):
    """lower bound for arcsin(z), 0 <= z <= 1."""
    if z <= 0: return Q(0)
    if z >= 1: return floor3(PI_LOWER/2)
    if z <= Q(4, 5): return _asin_series_lower(z)
    w = sqrt_upper(1 - z*z)
    if w >= 1: return Q(0)
    return floor3(PI_LOWER/2 - _asin_series_upper(w))


def w_lower_from_om(om):
    """lower bound for arccos(1-om) = 2 arcsin(sqrt(om/2)),  om in [0,2]."""
    if om <= 0: return Q(0)
    if om >= 2: return floor3(PI_LOWER)
    return floor3(2*asin_lower(sqrt_lower(om/2)))


class Geom:
    """certified geometry at a fixed a (all bounds in the safe direction)."""
    def __init__(self, a):
        self.a = a
        self.chD2_lo = exp_lower(2/a)                 # cosh(D/2) = e^(2/a)
        chu = exp_upper(2/a)
        self.hD_upper = log_upper(chu + sqrt_upper(chu*chu - 1))   # >= D/2
        self.d_low_lo = lam_lower(delta_upper(a)/2)   # <= d_low(a)
        self._w = {}

    def w_lower(self, d, r):
        key = (d, r)
        v = self._w.get(key)
        if v is None:
            td = trig(d); tr = trig(r)
            num = self.chD2_lo - cosh_diff_upper(td, tr)
            if num <= 0:
                v = Q(0)
            else:
                om = floor3(num/(td[1]*tr[1]))
                v = w_lower_from_om(om)
            self._w[key] = v
        return v


def U_upper(g, rs, sig, dmax, n0=48, budget=900):
    """certified upper bound for sup_{d >= d_low} [ lam(d) - sum sigma_i w(d,r_i) ].

    lam is decreasing, and om(.,r) attains its minimum on any interval at an
    endpoint (c = 1 - om is unimodal in d with an interior minimum), so on
    [u,v] the bracket is at most  lam_upper(u) - sum_i sigma_i min(w_lo(u,r_i),
    w_lo(v,r_i)).  Beyond dmax >= r_max + D/2 every w vanishes and the bracket
    is at most lam_upper(dmax).  Intervals are refined worst-first.
    """
    lo = g.d_low_lo
    tail = lam_upper(dmax)

    def cell(u, v):
        s = Q(0)
        for r, sg in zip(rs, sig):
            if sg == 0: continue
            s += sg*min(g.w_lower(u, r), g.w_lower(v, r))
        return lam_upper(u) - s

    heap = []; final = []
    h = (dmax - lo)/n0
    for i in range(n0):
        u = fl9(lo + i*h); v = ce9(u + h)
        heapq.heappush(heap, (-cell(u, v), u, v))
    spent = 0
    while heap and spent < budget:
        neg, u, v = heap[0]
        if -neg <= tail: break
        m = fl9((u+v)/2)
        if m <= u or m >= v:
            final.append(-neg); heapq.heappop(heap); continue
        heapq.heappop(heap)
        heapq.heappush(heap, (-cell(u, m), u, m))
        heapq.heappush(heap, (-cell(m, v), m, v))
        spent += 1
    best = tail
    for neg, u, v in heap:
        if -neg > best: best = -neg
    for b in final:
        if b > best: best = b
    return ceil3(best)


# ------------------------------------------------------- dual proposer (floats)
def _float_geom(a):
    import math
    e = math.exp(-1/a)
    delta = -math.log1p(-e)
    d_low = 2*math.atanh(math.exp(-delta/2))
    chD2 = math.exp(2/a)
    hD = math.acosh(chD2)
    return delta, d_low, hD, chD2


def _fw(d, r, chD2):
    import math
    if d <= 0 or r <= 0: return 0.0
    om = (chD2 - math.cosh(d-r))/(math.sinh(d)*math.sinh(r))
    if om <= 0: return 0.0
    if om >= 2: return math.pi
    return math.acos(1-om)


def propose(a, k, p, nd=400):
    """Propose (rs, sigma) minimising k*U + pi*S.  Floating; validity of the
    certificate does not depend on this being optimal."""
    import math
    delta, d_low, hD, chD2 = _float_geom(a)
    lo0 = max(1e-3, d_low - hD)
    best = None
    try:
        import numpy as np
        from scipy.optimize import linprog
        have = True
    except Exception:
        have = False
    for r_lo in (lo0, lo0+0.35, lo0+0.7):
        for tt in (0.4, 0.8, 1.3, 2.0, 3.0, 4.5):
            r_hi = d_low + tt
            if r_hi <= r_lo + 0.05: continue
            rs = [r_lo + (r_hi-r_lo)*i/(p-1) for i in range(p)]
            dmax = r_hi + hD + 1e-9
            ds = [d_low + (dmax-d_low)*i/(nd-1) for i in range(nd)]
            if have:
                W = np.array([[_fw(d, r, chD2) for r in rs] for d in ds])
                lams = np.array([-math.log(math.tanh(d/2)) for d in ds])
                W = np.vstack([W, np.zeros(p)])
                lams = np.append(lams, -math.log(math.tanh(dmax/2)))
                res = linprog(-lams, A_ub=W.T, b_ub=np.full(p, math.pi),
                              A_eq=np.ones((1, nd+1)), b_eq=[k],
                              bounds=[(0, None)]*(nd+1), method="highs")
                if res.status != 0: continue
                sig = [max(0.0, float(s)) for s in -res.ineqlin.marginals]
                val = -res.fun
            else:
                # uniform-density fallback, density by golden search
                def value(A):
                    hstep = (r_hi-r_lo)/p
                    sg = [A*hstep]*p
                    U = -math.log(math.tanh(dmax/2))
                    for d in ds:
                        v = -math.log(math.tanh(d/2))
                        v -= sum(s*_fw(d, r, chD2) for s, r in zip(sg, rs))
                        if v > U: U = v
                    return k*U + math.pi*sum(sg), sg
                lo, hi = 1e-4, 4.0
                for _ in range(40):
                    m1 = lo + (hi-lo)*0.382; m2 = lo + (hi-lo)*0.618
                    if value(m1)[0] < value(m2)[0]: hi = m2
                    else: lo = m1
                val, sig = value((lo+hi)/2)
            if best is None or val < best[0]:
                best = (val, rs, sig, r_hi)
    return best


_TABLE = {}          # a_grid_value -> list of (S, U) certified pairs
_AGRID = []


def build_table(a_values, klist, p, n0, budget, dgrid=400):
    global _AGRID
    _AGRID = sorted(a_values)
    for av in _AGRID:
        g = Geom(av)
        rows = []
        for k in klist:
            got = propose(float(av), k, p, nd=dgrid)
            if got is None: continue
            _, rs_f, sig_f, r_hi = got
            rs = [Q(int(round(r*10**6)), 10**6) for r in rs_f]
            sig = [Q(int(round(s*10**9)), 10**9) for s in sig_f]
            keep = [(r, s) for r, s in zip(rs, sig) if s > 0]
            if not keep: continue
            rs = [r for r, _ in keep]; sig = [s for _, s in keep]
            dmax = ceil3(max(rs) + g.hD_upper) + Q(1, 10**6)
            U = U_upper(g, rs, sig, dmax, n0=n0, budget=budget)
            S = sum(sig)
            if U <= 0: continue
            rows.append((S, U))
        _TABLE[av] = rows


def k_circ_lower(x, a):
    a = Q(-((-a.numerator*A_GRID)//a.denominator), A_GRID)   # snap a UP
    if not _AGRID or a > _AGRID[-1]: return Q(2)
    av = None
    for v in _AGRID:
        if v >= a: av = v; break
    if av is None: return Q(2)
    best = Q(2)
    for S, U in _TABLE[av]:
        num = x - PI_UPPER*S
        if num <= 0: continue
        kk = num/U
        if kk > best: best = kk
    return min(best, Q(K_CAP))


# ------------------------------------------------------------------- assembly
def ceil_int(q):
    n = -((-q.numerator)//q.denominator)
    return Q(n)


_KL = {}
def k_lower(x, a):
    au = Q(-((-a.numerator*A_GRID)//a.denominator), A_GRID)
    key = (x, au)
    if key in _KL: return _KL[key]
    r = _k_lower(x, a); _KL[key] = r; return r


def _k_lower(x, a):
    if x <= 0: return Q(2)
    d = delta_upper(a); t = tau_upper(a); lg = lam_g_upper(a)
    kB = 2*x/t if t > 0 else Q(K_CAP)
    kA = Q(1) + (x - d/2)/lg if lg > 0 else Q(K_CAP)
    kk = min(kA, kB)
    corpus = min(max(Q(2), ceil_int(min(kk, Q(K_CAP))),
                     ceil_int(min(2*x/d, Q(K_CAP)))), Q(K_CAP))
    out = max(corpus, ceil_int(k_pack_lower(x, a)), ceil_int(k_circ_lower(x, a)))
    return min(out, Q(K_CAP))


def g_cell_lower(xl, xr, a):
    b = 2*sqrt_lower(k_lower(xl, a)) - sqrt_upper(2*a*(xr+2))
    if b <= 0: return Q(0)
    return floor_q(INV_TWO_PI_SQ_LOWER*b*b)


def lower_step(xl, xr, ai):
    h = xr-xl; gi = g_cell_lower(xl, xr, ai); ap = ai + h*gi
    if ap > 1:
        if 1 - ai - h*g_cell_lower(xl, xr, Q(1)) < 0: return Q(1)+Q(1, D)
        ap = Q(1)
    # A computed lower oracle need not be monotone across independently
    # optimized area cells. Only a proved lower endpoint may initialize lo.
    # If the actual end area <= m, all intermediate areas <= m; the
    # geometry at m then gives end >= ai+h*g_cell_lower(xl,xr,m).
    lo, hi = ai, ap
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
    # gc is retained for callers of earlier certificate versions. Every
    # trajectory starts above a0; lower_step propagates a lower bound, so
    # larger initial values need no separate replay.
    xs = Q(3, 10**5); c = start_shift(xs); a0 = Q(1, 10**6)
    assert c*xs >= a0
    t = hitting_time(a0, xs, h)
    assert t is not None, f"no hit from universal lower start {a0}"
    return t, a0


def comparison_regression():
    """A valid lower oracle may increase while its true envelope decreases.

    The envelope 100 on [0,1/5) and 0 thereafter permits a trajectory
    saturating at 1/5. The old initialization jumped to 100 because it used
    the lower oracle at its unproved predictor as an initial lower bound.
    """
    global g_cell_lower
    original = g_cell_lower
    def oracle(xl, xr, a):
        if a == 0: return Q(1, 10)
        return Q(100) if a < Q(1, 5) else Q(0)
    try:
        g_cell_lower = oracle
        bound = lower_step(Q(0), Q(1), Q(0))
        assert 0 <= bound <= Q(1, 5)
        old_predictor = Q(1, 10)
        old_initial_lower = oracle(Q(0), Q(1), old_predictor)
        assert old_initial_lower > Q(1, 5)
    finally:
        g_cell_lower = original
    return {"status": "pass", "nonmonotone_oracle_lower_bound": str(bound),
            "admissible_trajectory_endpoint": "1/5",
            "old_initialization_would_return": str(old_initial_lower)}


def audit():
    """independent float re-checks of the two identities the lemma rests on."""
    import math, random
    random.seed(20260905)
    worst_arc = 0.0; worst_shadow = 0.0
    for _ in range(300):
        a = random.uniform(0.3, 1.0)
        Dm = 4*math.atanh(math.sqrt(math.tanh(1/a)))
        d = random.uniform(0.2, Dm/2 + 6)
        r = random.uniform(0.2, d + Dm/2)
        # arc half-width from the law of cosines, two ways
        c = (math.cosh(d)*math.cosh(r) - math.cosh(Dm/2))/(math.sinh(d)*math.sinh(r))
        if -1 < c < 1:
            phi = math.acos(c)
            lhs = math.cosh(d)*math.cosh(r) - math.sinh(d)*math.sinh(r)*math.cos(phi)
            worst_arc = max(worst_arc, abs(lhs - math.cosh(Dm/2)))
        # Piecewise supremum, including balls containing the observer.
        best = 0.0
        for i in range(1, 6000):
            rr = (d + Dm/2)*i/6000
            cc = (math.cosh(d)*math.cosh(rr) - math.cosh(Dm/2))/(math.sinh(d)*math.sinh(rr))
            if -1 < cc < 1: best = max(best, math.acos(cc))
            elif cc <= -1: best = math.pi
        alpha = (math.pi if d < Dm/2 else
                 math.asin(min(1.0, math.sinh(Dm/2)/math.sinh(d))))
        worst_shadow = max(worst_shadow, best - alpha)
    # Exact full-circle regression: d+r=5/2 < H=acosh(exp(2)).
    # This is precisely the case omitted by the former shadow audit.
    g = Geom(Q(1))
    assert cosh_upper(Q(5, 2)) < g.chD2_lo
    assert g.w_lower(Q(9, 4), Q(1, 4)) > PI_UPPER/2
    assert worst_shadow <= 1e-8
    return {"observer_containing_circle_exact_check": "pass",
            "law_of_cosines_residual": worst_arc,
            "sup_r_w_minus_shadow_halfwidth": worst_shadow}


def primitive_constant_audit():
    """Certify the rational pi/log(2) brackets used by all other bounds.

    Machin: pi=16 atan(1/5)-4 atan(1/239), with alternating-series tails.
    log(2)=2 sum_{j>=0} (1/3)^(2j+1)/(2j+1), with a geometric tail.
    """
    def atan_bounds(z):
        n = 40
        v = sum((-1)**j*z**(2*j+1)/Q(2*j+1) for j in range(n))
        return v, v+z**(2*n+1)/Q(2*n+1)
    a,b = atan_bounds(Q(1,5)); c,d = atan_bounds(Q(1,239))
    pl,pu = 16*a-4*d, 16*b-4*c
    assert PI_LOWER < pl <= pu < PI_UPPER
    z=Q(1,3); n=40
    ll=2*sum(z**(2*j+1)/Q(2*j+1) for j in range(n))
    lu=ll+2*z**(2*n+1)/(Q(2*n+1)*(1-z*z))
    assert LOG2_LOWER < ll <= lu < LOG2_UPPER
    assert INV_TWO_PI_SQ_LOWER < 1/(2*PI_UPPER**2)
    return {"status":"pass", "pi":"Machin alternating series",
            "log_two":"positive atanh series", "terms":n}


def main():
    primitive_constant_audit()
    if "--comparison-audit" in sys.argv:
        print(json.dumps(comparison_regression()))
        return 0
    if "--geometry-audit" in sys.argv:
        print(json.dumps({"status": "pass", "evidence_class":
                          "exact_boundary_regression_plus_float_geometry_checks",
                          "audit": audit()}))
        return 0
    quick = "--quick" in sys.argv
    h = Q(1, 100) if quick else Q(1, 400)
    gc = 8 if quick else 12
    if quick:
        avs = [Q(i, 100) for i in (18, 22, 27, 33, 40, 48, 57, 68, 80, 90, 100)]
        klist = [4, 8, 16, 32]; p = 10; n0 = 40; budget = 500
    else:
        avs = [Q(i, 200) for i in (34, 40, 46, 53, 60, 68, 76, 85, 94, 104,
                                   114, 125, 136, 148, 160, 173, 186, 200)]
        klist = [3, 5, 8, 12, 20, 32, 60]; p = 14; n0 = 56; budget = 1100
    build_table(avs, klist, p, n0, budget)
    X, wa = certify_all_degree(h, gc)
    X = ceil_q(X)  # Report an upper hitting-time bound and test this bound.
    cands = [Q(11, 20), Q(27, 50), Q(53, 100), Q(13, 25), Q(51, 100), Q(1, 2),
             Q(49, 100), Q(12, 25), Q(47, 100), Q(23, 50), Q(9, 20), Q(11, 25),
             Q(43, 100), Q(21, 50), Q(41, 100), Q(2, 5), Q(39, 100), Q(19, 50),
             Q(37, 100), Q(9, 25)]
    chosen = None
    for mu in cands:
        if mu*exp_upper(X) <= 1: chosen = mu; break
    assert chosen is not None
    assert chosen > Q(2, 5), "must beat the landed 2/5"
    rep = {"status": "pass", "evidence_class": "exact_rational_certificate",
           "mode": "quick" if quick else "full",
           "all_degree": {"X_cert": str(X), "X_cert_float": float(X),
                          "mu_threshold": str(chosen),
                          "mu_threshold_float": float(chosen),
                          "worst_initial_area": float(wa),
                          "grid_points": 1, "initial_area_lower": "1/1000000",
                          "comparison": "single_universal_lower_start", "step": str(h),
                          "baseline_landed": "2/5"},
           "circle_slice": {"a_grid": [str(v) for v in avs],
                            "k_list": klist, "radii_per_dual": p,
                            "duals_certified": sum(len(v) for v in _TABLE.values()),
                            "duals_at_a_1": [[float(S), float(U)]
                                             for S, U in _TABLE.get(Q(1), [])],
                            "proposer": "scipy_lp_or_uniform_fallback"},
           "mechanism": ("COVER one-root Bergman + connected-cluster pairwise "
                         "Bergman separation + circle-slice angular packing "
                         "arity floor + boundary hop"),
           "per_degree_thresholds": "not run in this pass"}
    if "--audit" in sys.argv:
        rep["audit"] = audit()
    print(json.dumps(rep))
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
