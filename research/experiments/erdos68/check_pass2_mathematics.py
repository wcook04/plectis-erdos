#!/usr/bin/env python3
# SPDX-FileCopyrightText: 2026 Will Cook
# SPDX-License-Identifier: Apache-2.0
"""Exact pass-two witnesses and finite regression tests. Python 3.10+, stdlib only.

No finite regression test proves the averaged critical-root target, short-block
nonvanishing selection, a stronger lcm bound, or irrationality of the series.
"""
from __future__ import annotations
import argparse, hashlib, json, math, platform, time
from pathlib import Path

Poly = list[int]  # coefficients in increasing degree

def prime(n: int) -> bool:
    return n >= 2 and all(n % d for d in range(2, math.isqrt(n)+1))

def trim(a: Poly) -> Poly:
    while len(a)>1 and a[-1]==0: a.pop()
    return a

def mul(a: Poly, b: Poly, q: int) -> Poly:
    out=[0]*(len(a)+len(b)-1)
    for i,x in enumerate(a):
        for j,y in enumerate(b): out[i+j]=(out[i+j]+x*y)%q
    return trim(out)

def derivative(a: Poly,q: int) -> Poly:
    return trim([(i*a[i])%q for i in range(1,len(a))] or [0])

def value(a: Poly,x: int,q: int) -> int:
    y=0
    for c in reversed(a): y=(y*x+c)%q
    return y

def remainder(a: Poly,b: Poly,q: int) -> Poly:
    if b==[0]: raise ZeroDivisionError('zero polynomial divisor')
    a=trim(a.copy());inv=pow(b[-1],-1,q)
    while a!=[0] and len(a)>=len(b):
        k=len(a)-len(b);c=a[-1]*inv%q
        for j in range(len(b)): a[k+j]=(a[k+j]-c*b[j])%q
        trim(a)
    return a

def gcd(a: Poly,b: Poly,q: int) -> Poly:
    while b!=[0]: a,b=b,remainder(a,b,q)
    if a==[0]: return a
    u=pow(a[-1],-1,q)
    return [(x*u)%q for x in a]

def rising(h: int,q: int) -> Poly:
    out=[1]
    for j in range(1,h+1):out=mul(out,[j%q,1],q)
    return out

def direct_pair(x: int,h: int,q: int) -> tuple[int,int]:
    f,df=1,0
    for j in range(1,h+1):
        df=(df*(x+j)+f)%q;f=f*(x+j)%q
    return f,df

def critical_witness() -> dict:
    q,h=12487,12
    assert prime(q)
    F=rising(h,q);Fm=F.copy();Fm[0]=(Fm[0]-1)%q
    G=gcd(Fm,derivative(F,q),q)
    assert G==[5139,13,1]
    roots=[x for x in range(q) if value(G,x,q)==0]
    assert roots==[4626,7848]
    assert all(direct_pair(x,h,q)==(1,0) for x in roots)
    centre=(-(h+1)*pow(2,-1,q))%q
    assert centre not in roots
    fact,har=1,0;observed={};wanted={x for r in roots for x in [r,r+h]}
    for n in range(1,q):
        fact=fact*n%q;har=(har+pow(n,-1,q))%q
        if n in wanted:observed[str(n)]={'factorial':fact,'harmonic':har}
    assert observed=={'4626':{'factorial':442,'harmonic':11117},'4638':{'factorial':442,'harmonic':11117},'7848':{'factorial':6300,'harmonic':11117},'7860':{'factorial':6300,'harmonic':11117}}
    assert {(2*x+h+1)**2%q for x in roots}=={4587}
    return dict(prime=q,primality_method='trial division through floor(sqrt(q))',gap=h,
                monic_gcd_coefficients_ascending=G,roots=roots,central_point=centre,
                compressed_square=4587,factorial_harmonic_values=observed,
                conclusion='r_q(12)=2, but neither root is a factorial-value-1 joint hit')

def symmetry_tests() -> dict:
    identities=counts=0
    for q in range(3,151,2):
        if not prime(q):continue
        squares={x*x%q for x in range(1,q)}
        for s in range(1,min(8,(q-1)//2)+1):
            h=2*s;G=[1]
            for j in range(1,s+1): G=mul(G,[-(2*j-1)**2%q,1],q)
            G[0]=(G[0]-pow(4,s,q))%q
            dG=derivative(G,q);left=0
            for x in range(q):
                z=(2*x+h+1)%q;y=z*z%q;f,df=direct_pair(x,h,q)
                assert (f-1)%q==pow(pow(4,s,q),-1,q)*value(G,y,q)%q
                assert df==4*pow(pow(4,s,q),-1,q)*z*value(dG,y,q)%q
                left+=f==1 and df==0;identities+=2
            right=int(value(G,0,q)==0)+2*sum(value(G,y,q)==value(dG,y,q)==0 for y in squares)
            assert left==right;counts+=1
    return dict(prime_limit_exclusive=151,max_even_gap=16,pointwise_polynomial_identities=identities,root_count_identities=counts)

def moment_tests() -> dict:
    # An extended finite check of the proved finite-horizon result, not its proof.
    maxD=12;Hmax=max(d*(2*max(p for p in range(2,d+1) if prime(p))-1) for d in range(2,maxD+1))
    limit=2*Hmax;facts=[math.factorial(n) for n in range(limit+1)];u=[0]*(limit+1);u[2]=2
    for n in range(3,limit+1):u[n]=-sum((facts[n]//facts[d]**(n//d))*u[d] for d in range(2,n) if n%d==0)
    rows=[]
    for D in range(2,maxD+1):
        ell=max(p for p in range(2,D+1) if prime(p));assert 2*ell>D
        H=D*(2*ell-1);g=math.gcd(*u[D+1:H+1]);assert g>0 and H<2*D*D
        assert math.gcd(*u[D+1:limit+1])==g
        rows.append(dict(D=D,ell=ell,H=H,gcd=g))
    assert u[6]==-180 and u[8]==-4200
    a,L=-55,115;g=next(r['gcd'] for r in rows if r['D']==4)
    assert g==60 and L*g//math.gcd(g,a)==1380
    assert 12*a+253*u[6]-11*u[8]==0
    assert L*abs(u[6])//math.gcd(abs(u[6]),a)==4140
    for n in range(3,101):assert math.gcd(facts[n-1]-1,facts[n]-1)==1
    return dict(depths_checked=rows,extended_coefficient_limit=limit,
                D4_minimum_moment=1380,D4_support_through_6_minimum=4140,
                D4_support_equation_coefficients=[12,253,-11],
                consecutive_coprimality_test_range=[3,100],
                scope='Finite regression checks only; general proofs are in the manuscripts')

def valuation_identity_tests() -> dict:
    tests=0
    # At one prime with arbitrary nonnegative exponents, the truncated-layer identity is exact.
    from itertools import product
    for n in range(1,7):
        for v in product(range(5),repeat=n):
            e=max(v);T=[sum(a>=j for a in v) for j in range(1,e+1)]
            excess=sum(max(t-2,0) for t in T)
            assert sum(v)-excess==sum(min(t,2) for t in T)<=2*e;tests+=1
    return dict(exponent_vectors_tested=tests,max_vector_length=6,max_exponent=4)

def main() -> None:
    ap=argparse.ArgumentParser(description=__doc__);ap.add_argument('--output',type=Path,required=True);args=ap.parse_args();start=time.monotonic()
    out=dict(schema='erdos68_pass2_exact_mathematics_v1',review_date='2026-09-16',python=platform.python_version(),
             critical_witness=critical_witness(),even_gap_symmetry=symmetry_tests(),moment_ideal_regressions=moment_tests(),
             weighted_collision_identity=valuation_identity_tests(),
             not_proved=['A near-linear averaged critical-root bound','Uniform unequal-product selection for the remaining gap range','An E2 saving or an lcm exponent of 5/3','Irrationality of the factorial-denominator series'],
             implementation_sha256=hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),elapsed_seconds=round(time.monotonic()-start,3))
    args.output.parent.mkdir(parents=True,exist_ok=True);args.output.write_text(json.dumps(out,indent=2)+'\n');print(json.dumps(out,indent=2))
if __name__=='__main__':main()
