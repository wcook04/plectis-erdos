#!/usr/bin/env python3
"""Exact identities and separately labelled numerical regression checks.

Usage: python check_r6.py [--numerical] [--output receipt.json]
Exact mode needs only Python's standard library. Numerical mode additionally
needs numpy. No numerical test certifies an infinite asymptotic theorem.
"""
from __future__ import annotations
import argparse, itertools, json, math, time
from fractions import Fraction as F
from pathlib import Path

INTERVALS = [(F(1,14),F(1,12)),(F(1,7),F(1,6)),(F(3,14),F(1,4)),
 (F(2,7),F(1,3)),(F(5,14),F(2,5)),(F(3,7),F(7,15)),
 (F(1,2),F(8,15)),(F(4,7),F(3,5)),(F(9,14),F(2,3)),
 (F(5,7),F(11,15)),(F(11,14),F(4,5)),(F(6,7),F(13,15)),(F(13,14),F(14,15))]

def log_interval(z:F,terms:int=48)->tuple[F,F]:
    """log z by the atanh series, exact rational endpoints, z>0."""
    if z<=0: raise ValueError('log argument must be positive')
    t=(z-1)/(z+1)
    if t<0:
        lo,hi=log_interval(1/z,terms);return -hi,-lo
    s=2*sum((t**(2*k+1)/F(2*k+1) for k in range(terms)),F(0))
    err=2*t**(2*terms+1)/(F(2*terms+1)*(1-t*t))
    return s,s+err

def atan_interval(t:F,terms:int=48)->tuple[F,F]:
    s=sum(((-1)**k*t**(2*k+1)/F(2*k+1) for k in range(terms)),F(0))
    nxt=(-1)**terms*t**(2*terms+1)/F(2*terms+1)
    return min(s,s+nxt),max(s,s+nxt)

def rational_region_certificate()->dict:
    K=512
    J=sum((1/(F(k)+u)**2-1/(F(k)+v)**2
           for u,v in INTERVALS for k in range(K)),F(0))
    # Positive decreasing summand f: int_K^infty f <= sum_{k>=K} f
    # <= f(K)+int_K^infty f.
    tail_lo=sum((1/(K+u)-1/(K+v) for u,v in INTERVALS),F(0))
    tail_hi=tail_lo+sum((1/(K+u)**2-1/(K+v)**2 for u,v in INTERVALS),F(0))
    alo,ahi=atan_interval(F(1,5));blo,bhi=atan_interval(F(1,239))
    plo,phi=16*alo-4*bhi,16*ahi-4*blo
    assert 0<plo<phi and J+tail_hi<225
    c1=F(1091,2)
    thlo=(266-3*(225-J-tail_lo)/plo**2)/c1
    thhi=(266-3*(225-J-tail_hi)/phi**2)/c1
    l2lo,l2hi=log_interval(F(2));lratlo,lrathi=log_interval(F(31,32))
    l31lo,l31hi=5*l2lo+lratlo,5*l2hi+lrathi
    l4lo,l4hi=2*l2lo,2*l2hi
    numerator_lo,numerator_hi=l31lo-l4hi,l31hi-l4lo
    denominator_lo,denominator_hi=thlo*l31lo-l4hi,thhi*l31hi-l4lo
    assert denominator_lo>0
    mulo,muhi=numerator_lo/denominator_hi,numerator_hi/denominator_lo
    assert F(3004269,10000)<mulo<=muhi<F(3004270,10000)
    assert muhi<301
    J16=sum((1/(F(k)+u)**2-1/(F(k)+v)**2
             for u,v in INTERVALS for k in range(16)),F(0))
    assert plo>F(314159,100000)
    assert (266-3*(225-J16)/F(314159,100000)**2)/c1>F(40568,100000)
    assert l4hi/l31lo<F(4036982,10**7)
    assert (1-F(4036982,10**7))/(F(40568,100000)-F(4036982,10**7))==F(2981509,9909)<301
    return {'tail_cutoff':K,'exact_assertion':'300.4269 < exponent bound < 300.4270 < 301',
            'display_only_theta_interval':[float(thlo),float(thhi)],
            'display_only_exponent_interval':[float(mulo),float(muhi)],
            'method':'all assertions evaluated with fractions.Fraction; floats only for display'}

def det(a:list[list[F]])->F:
    n=len(a);a=[row[:] for row in a];ans=F(1)
    for i in range(n):
        j=next((j for j in range(i,n) if a[j][i]),None)
        if j is None:return F(0)
        if j!=i:a[i],a[j]=a[j],a[i];ans=-ans
        pivot=a[i][i];ans*=pivot
        for j in range(i+1,n):
            v=a[j][i]/pivot
            for k in range(i+1,n):a[j][k]-=v*a[i][k]
            a[j][i]=0
    return ans

def finite_schur_identity()->dict:
    cases=0
    for q in [F(1,4),F(1,2),F(2,3)]:
      for N in range(1,5):
        L=N+3;a=[F((k+1)**3+2*k+1) for k in range(L)]
        moments=[sum((a[k]*q**((r+1)*k) for k in range(L)),F(0)) for r in range(2*N-1)]
        lhs=det([[moments[i+j] for j in range(N)] for i in range(N)])
        B=N*(N-1)*(2*N-1)//6
        vd=math.prod((1-q**d)**(2*(N-d)) for d in range(1,N))
        ground=q**B*math.prod(a[:N])*vd
        base=det([[q**(i*(N-j-1)) for j in range(N)] for i in range(N)])
        total=F(0)
        for ks in itertools.combinations(range(L),N):
            lam=[ks[N-j-1]-(N-j-1) for j in range(N)]
            schur=det([[q**(i*(lam[j]+N-j-1)) for j in range(N)] for i in range(N)])/base
            tilt=math.prod(a[N-j-1+lam[j]]/a[N-j-1] for j in range(N))
            total+=q**sum(lam)*schur**2*tilt
        assert lhs==ground*total
        cases+=1
    return {'exact_cases':cases,'support':'finite; exact rational Cauchy-Binet/Schur equality'}

def lacunary_identities()->dict:
    cases=0
    for n in range(5):
        d=4**n;Q=9**d
        P=sum(2**(4**j)*9**(d-4**j) for j in range(n+1))
        Q1=9**(4*d)
        P1=sum(2**(4**j)*9**(4*d-4**j) for j in range(n+2))
        assert math.gcd(P,Q)==1 and 0<P<Q
        assert Q1==Q**4 and P1==P*Q**3+2**(4*d)
        assert P1*Q-P*Q1==Q*2**(4*d)
        # Exact finite partial tail has the asserted 2-adic valuation.
        tail=sum((F(2,9)**(4**j) for j in range(n+1,n+4)),F(0))*Q
        num=abs(tail.numerator);valuation=(num & -num).bit_length()-1
        assert valuation==4*d and tail.denominator%2==1
        cases+=1
    return {'exact_cases':cases,'identity':'P_(n+1) Q_n - P_n Q_(n+1) = Q_n 2^(4^(n+1))'}

def partitions(n:int,cap:int|None=None):
    if not n:yield ();return
    for k in range(min(n,n if cap is None else cap),0,-1):
        for rest in partitions(n-k,k):yield(k,)+rest

def numerical()->dict:
    import numpy as np
    q=.25;K=1050
    gamma=np.zeros(K+1);fac=1.
    for t in range(K+1):
        if t:fac*=1-q**t
        J=K-t;m=np.arange(1,J+1,dtype=float)
        L=(3+2*q**(t*m))/(1-q**m)
        even=np.arange(2,J+1,2);h=even/2
        L[even-1]-=2*q**(t*h)/(1-q**h)
        g=np.empty(J+1);g[0]=1.
        for k in range(1,J+1):g[k]=np.dot(L[:k],g[k-1::-1])/k
        gamma[t:]+=g/fac
    P=math.prod(1-q**j for j in range(1,200));a=gamma*P**4
    S=sum(q**j/(1-q**j) for j in range(1,200))
    T=sum(j*q**j/(1-q**j) for j in range(1,200))
    D2=21*S*S+3*S+3*T
    polar=[]
    for k in [50,100,200,400,800,1000]:
        t=k+1;c=t*t*(t+1)/2
        polar.append([k,t*t*(a[k]/c-1+8*S/t)])
    items=[]
    for n in range(29):
      for lam in partitions(n):
        cols=[sum(x>=j for x in lam) for j in range(1,lam[0]+1)] if lam else []
        hookprod=1.
        for i,row in enumerate(lam):
          for j in range(row):hookprod*=1-q**(row-j+cols[j]-i-1)
        w=q**(sum(lam)+2*sum(i*x for i,x in enumerate(lam)))/hookprod**2
        items.append((lam,w))
    Mac=math.prod((1-q**j)**(-j) for j in range(1,200))
    values={};exc=[]
    for N in [20,40,80,160,320,640]:
      Z=0.
      for lam,w in items:
        if len(lam)>N:continue
        ratio=1.;content=1.
        for j,l in enumerate(lam,1):
          ratio*=a[N-j+l]/a[N-j]
          for c in range(1,l+1):content*=1-q**(N+c-j)
        Z+=w*ratio*content**2
      gp=sum(math.log(a[k]/((k+1)**2*(k+2)/2)) for k in range(N))+8*S*math.log(N)
      vdc=sum(2*(N-d)*math.log1p(-q**d) for d in range(1,N))-2*N*math.log(P)-2*math.log(Mac)
      values[N]=gp+math.log(Z/Mac)+vdc
      exc.append([N,N*(Z/Mac-1)])
    correction=[[N,2*N*(values[N]-values[2*N])] for N in [20,40,80,160,320]]
    return {'evidence':'floating-point regression only; no certified infinite-tail or rounding bounds',
      'q':q,'weight_coefficients_through':K,'partition_size_cutoff':28,'partitions':len(items),
      'polar_target':D2,'polar_samples':polar,
      'excitation_target':3*T,'excitation_samples':exc,
      'full_correction_target':11*S*S-7*S,'full_correction_samples':correction}

def main():
    parser=argparse.ArgumentParser();parser.add_argument('--numerical',action='store_true')
    parser.add_argument('--output',type=Path);args=parser.parse_args();start=time.time()
    results={'rational_base_measure':rational_region_certificate(),
             'finite_schur':finite_schur_identity(),'lacunary':lacunary_identities()}
    if args.numerical:results['numerical']=numerical()
    results['elapsed_seconds']=time.time()-start
    txt=json.dumps(results,indent=2)
    if args.output:args.output.write_text(txt+'\n')
    print(txt)
if __name__=='__main__':main()
