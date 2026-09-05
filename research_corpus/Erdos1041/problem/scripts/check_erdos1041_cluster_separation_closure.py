#!/usr/bin/env python3
"""Exact rational certificate for the cluster-sharpened low-critical closure.

Same comparison ODE as LowCriticalPotentialClosure.md, with the COVER arity floor
replaced by  k >= max(2, 2x/delta(a), 1 + (2x - delta(a))/tau(a)),
tau(a) = -log tanh(1/a) = 2 artanh(exp(-2/a)).
"""
from __future__ import annotations
import json, sys
from fractions import Fraction as Q
from math import isqrt

D = 10**12
INV_TWO_PI_SQ_LOWER = Q(49, 968)
K_CAP = 10**8
A_GRID = 20000   # a is rounded UP; delta, tau, lam(g) all increase in a

def floor_q(q): return Q((q.numerator*D)//q.denominator, D)
def ceil_q(q):  return Q(-((-q.numerator*D)//q.denominator), D)
def sqrt_lower(q):
    if q<=0: return Q(0)
    return Q(isqrt((q.numerator*D*D)//q.denominator), D)
def sqrt_upper(q):
    if q<=0: return Q(0)
    v=-((-q.numerator*D*D)//q.denominator); r=isqrt(v)
    if r*r<v: r+=1
    return Q(r,D)
def exp_lower_small(y, terms=80):
    tot=term=Q(1)
    for j in range(1,terms): term=term*y/j; tot+=term
    return floor_q(tot)
def exp_lower(y):
    y=min(y,Q(64)); j=0
    while y>4: y/=2; j+=1
    v=exp_lower_small(y)
    for _ in range(j): v=floor_q(v*v)
    return v
def exp_upper(y, terms=60):
    assert 0<=y<terms
    tot=term=Q(1)
    for j in range(1,terms): term=term*y/j; tot+=term
    return ceil_q(tot+term*y/terms/(1-y/terms))

_DC={}; _TC={}
def _u_upper(y):
    """upper bound for exp(-y), y>0"""
    e=exp_lower(y)
    return ceil_q(1/e)
def delta_upper(a):
    au=Q(-((-a.numerator*A_GRID)//a.denominator), A_GRID)
    h=_DC.get(au)
    if h is None:
        u=_u_upper(1/au)
        if u>=1: h=Q(10**6)
        else:
            J=40; tot=Q(0); pw=Q(1)
            for j in range(1,J+1):
                pw=ceil_q(pw*u); tot+=pw/j
            h=ceil_q(tot+pw*u/((J+1)*(1-u)))
        _DC[au]=h
    return h
def tau_upper(a):
    """tau(a) = 2 artanh(exp(-2/a)) = 2 sum_{j>=0} u^(2j+1)/(2j+1), u=exp(-2/a)."""
    au=Q(-((-a.numerator*A_GRID)//a.denominator), A_GRID)
    h=_TC.get(au)
    if h is None:
        u=_u_upper(2/au)
        if u>=1: h=Q(10**6)
        else:
            J=40; tot=Q(0); pw=u; u2=ceil_q(u*u)
            for j in range(0,J+1):
                tot+=pw/(2*j+1)
                pw=ceil_q(pw*u2)
            tail=pw/((2*J+3)*(1-u2))
            h=ceil_q(2*(tot+tail))
        _TC[au]=h
    return h


D3 = 10**18
def floor3(q): return Q((q.numerator*D3)//q.denominator, D3)
def ceil3(q):  return Q(-((-q.numerator*D3)//q.denominator), D3)

def exp_upper_big(y):
    """Upper bound for exp(y), y >= 0, by halving then squaring (squares of
    upper bounds are upper bounds)."""
    j = 0
    while y > 4: y /= 2; j += 1
    v = exp_upper(y)
    for _ in range(j): v = ceil3(v*v)
    return v

def delta_lower(a):
    """delta(a) = sum_j u^j/j >= u = exp(-1/a)."""
    return floor3(1/exp_upper_big(1/a))

def _atanh_series(v, upper, J=32):
    """2 artanh(v) = 2 sum_j v^(2j+1)/(2j+1), 0 <= v < 1."""
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
    """lower bound for lam(d) = 2 artanh(exp(-d)); needs exp(-d) from below."""
    if d <= 0: return Q(10**6)
    return _atanh_series(floor3(1/exp_upper_big(d)), upper=False)

def lam_upper(d):
    """upper bound for lam(d); needs exp(-d) from above."""
    if d <= 0: return Q(10**6)
    v = ceil3(1/exp_lower(d))
    if v >= 1: return Q(10**6)
    return _atanh_series(v, upper=True)

_GC = {}
def lam_g_upper(a):
    """Upper bound for lam(g), g = d_min - d_low = 2 lam(tau/2) - lam(delta/2).
    Always at most tau/2 (since g >= d_min/2)."""
    LG_GRID = 2000
    au = Q(-((-a.numerator*LG_GRID)//a.denominator), LG_GRID)
    if au > 1: au = Q(1)
    h = _GC.get(au)
    if h is None:
        t2 = tau_upper(au)/2
        crude = t2
        h = crude
        if au >= Q(1,64):
            dl = delta_lower(au)
            if dl > 0:
                g_lo = 2*lam_lower(t2) - lam_upper(dl/2)
                if g_lo > 0:
                    h = min(crude, lam_upper(g_lo))
        _GC[au] = h
    return h

_KL={}
def k_lower(x,a):
    au=Q(-((-a.numerator*A_GRID)//a.denominator),A_GRID)
    key=(x,au)
    if key in _KL: return _KL[key]
    r=_k_lower(x,a); _KL[key]=r; return r

def _k_lower(x,a):
    """Sharp ordered arity floor.

    Lambda(k,a) = max( delta/2 + (k-1) lam(g),  k tau/2 )  and failure needs
    Lambda(k,a) >= x, so k >= min(k_A, k_B).  Any valid LOWER bound on each of
    k_A, k_B gives a valid lower bound on k.
    """
    if x<=0: return Q(2)
    d=delta_upper(a); t=tau_upper(a); lg=lam_g_upper(a)
    kB = 2*x/t if t>0 else Q(K_CAP)
    kA = Q(1)+(x-d/2)/lg if lg>0 else Q(K_CAP)
    kk = min(kA, kB)
    return min(max(Q(2), floor_q(kk), floor_q(2*x/d)), Q(K_CAP))

def g_cell_lower(xl,xr,a):
    b=2*sqrt_lower(k_lower(xl,a))-sqrt_upper(2*a*(xr+2))
    if b<=0: return Q(0)
    return floor_q(INV_TWO_PI_SQ_LOWER*b*b)

def lower_step(xl,xr,ai):
    h=xr-xl; gi=g_cell_lower(xl,xr,ai); ap=ai+h*gi
    if ap>1:
        if 1-ai-h*g_cell_lower(xl,xr,Q(1))<0: return Q(1)+Q(1,D)
        ap=Q(1)
    lo,hi=ai+h*g_cell_lower(xl,xr,ap),ap
    for _ in range(40):
        if hi-lo<Q(1,10**6): break
        m=(lo+hi)/2
        if m-ai-h*g_cell_lower(xl,xr,m)<0: lo=m
        else: hi=m
    return floor_q(max(lo,ai))

GR=Q(1,16)
def next_x(x,h): return x+min(h,max(x*GR,Q(1,10**7)))
def start_shift(xs):
    b=2*sqrt_lower(Q(2))-sqrt_upper(2*(xs+2)); assert b>0
    return floor_q(INV_TWO_PI_SQ_LOWER*b*b)
def geometric_grid(a0,count):
    g=[]
    for i in range(count+1):
        f=10.0**float(-6*(1-Q(i,count)))
        g.append(max(floor_q(Q(f).limit_denominator(D)),a0))
    g[-1]=Q(1); return sorted(set(g))

def hitting_time(alpha,xs,h,cap_test,floor_fn=None,x_max=Q(4)):
    x,a=xs,alpha
    if floor_fn is not None: a=max(a,floor_fn(x))
    if cap_test(x,a): return x
    while x<x_max:
        xn=next_x(x,h); a=lower_step(x,xn,a)
        if floor_fn is not None: a=max(a,floor_fn(xn))
        x=xn
        if cap_test(x,a): return x
    return None

_AF={}
def a_floor_from_arity(x,n):
    key=(x,n)
    if key in _AF: return _AF[key]
    r=_a_floor_from_arity(x,n); _AF[key]=r; return r

def _a_floor_from_arity(x,n):
    """Any a with Lambda(n,a) = delta/2 + (n-1) tau/2 < x is contradictory."""
    tgt=2*x
    LamU=lambda aa: max(delta_upper(aa)+2*(n-1)*lam_g_upper(aa), n*tau_upper(aa))
    if LamU(Q(1))<tgt: return Q(1)
    lo,hi=Q(1,10**6),Q(1)
    if not LamU(lo)<tgt: return Q(0)
    for _ in range(40):
        m=(lo+hi)/2
        if LamU(m)<tgt: lo=m
        else: hi=m
    return floor_q(lo)

def certify_all_degree(h,gc):
    xs=Q(3,10**5); c=start_shift(xs); a0=Q(1,10**6)
    assert c*xs>=a0
    worst=Q(0); wa=None
    for al in geometric_grid(a0,gc):
        t=hitting_time(al,xs,h,lambda x,a: a>1)
        assert t is not None, f"no hit from {al}"
        if t>worst: worst,wa=t,al
    return worst,wa

def certify_degree(n,mu,h,gc):
    xs=Q(3,10**5); a0=Q(1,10**6)
    cap=lambda x,a: a**n > mu**2*exp_upper(2*x)
    ff=lambda x: a_floor_from_arity(x,n)
    for al in geometric_grid(a0,gc):
        t=hitting_time(al,xs,h,cap,ff,Q(6))
        if t is None: return False
        if not mu*exp_upper(t)<1: return False
    return True

def main():
    quick="--quick" in sys.argv
    h=Q(1,100) if quick else Q(1,400)
    gc=8 if quick else 12
    X,wa=certify_all_degree(h,gc)
    rep={"status":"pass","evidence_class":"exact_rational_certificate",
         "mode":"quick" if quick else "full"}
    cands=[Q(9,25),Q(7,20),Q(17,50),Q(1,3),Q(33,100),Q(8,25),Q(31,100),Q(3,10),Q(7,25),Q(1,4),Q(197,1000)]
    chosen=None
    for mu in cands:
        if mu*exp_upper(X)<=1: chosen=mu; break
    assert chosen is not None
    assert chosen>Q(197,1000), "must beat the landed 197/1000"
    X=floor_q(X)
    rep["all_degree"]={"X_cert":str(X),"X_cert_float":float(X),
                       "mu_threshold":str(chosen),"mu_threshold_float":float(chosen),
                       "worst_initial_area":float(wa),"grid_points":gc,"step":str(h),
                       "baseline_landed":"197/1000"}
    if "--per-degree" not in sys.argv:
        rep["per_degree_thresholds"]="skipped (pass --per-degree; slow)"
        rep["mechanism"]="COVER one-root Bergman + connected-cluster pairwise Bergman separation (sharp ordered profile) + boundary hop"
        print(json.dumps(rep)); return 0
    dc={4:[Q(13,20),Q(3,5),Q(11,20),Q(1,2),Q(9,20),Q(2,5),Q(9,25)],
        5:[Q(11,20),Q(1,2),Q(9,20),Q(2,5),Q(9,25)],
        6:[Q(1,2),Q(9,20),Q(2,5),Q(9,25)],
        7:[Q(9,20),Q(2,5),Q(9,25)]}
    rows={}
    for n,cs in dc.items():
        ch=None
        for mu in cs:
            if certify_degree(n,mu,h,gc): ch=mu; break
        assert ch is not None and ch>=chosen, f"degree {n} failed"
        rows[n]=str(ch)
    rep["per_degree_thresholds"]=rows
    rep["mechanism"]="COVER one-root Bergman + connected-cluster pairwise Bergman separation + boundary hop"
    print(json.dumps(rep))
    return 0

if __name__=="__main__":
    raise SystemExit(main())
