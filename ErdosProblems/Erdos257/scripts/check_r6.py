#!/usr/bin/env python3
"""Exact finite checks for the r6 proofs. No numerical test certifies a theorem.
Python 3.10+; standard library only. Outputs JSON and returns nonzero on failure.
"""
from __future__ import annotations
from fractions import Fraction as F
from itertools import combinations
from math import gcd, lcm, prod
from pathlib import Path
import json

def subsets(xs):
    xs=tuple(xs)
    for k in range(len(xs)+1):
        yield from combinations(xs,k)

def atom(a: int, n: int, b: int=2) -> F:
    if a<1 or n<0 or b<2: raise ValueError('a >= 1, n >= 0, b >= 2 required')
    return F(b**(n%a)-1,b**a-1)

def disp(xs, n: int, b: int=2) -> F:
    return sum((atom(a,n,b) for a in xs),F())

def harmonic(xs) -> F:
    return sum((F(1,a) for a in xs),F())

def divisors(n):
    return [d for d in range(1,n+1) if n%d==0]

def primes_upto(n):
    a=[True]*(n+1); a[:2]=[False,False]
    for p in range(2,int(n**0.5)+1):
        if a[p]:
            a[p*p:n+1:p]=[False]*(((n-p*p)//p)+1)
    return [p for p in range(2,n+1) if a[p]]

def vp(n,p):
    k=0
    while n%p==0:
        n//=p;k+=1
    return k

def main():
    counts={}
    # Tail bound including the full finite tail, hence every finite subset.
    c=0
    for n in range(1,21):
        for gap in range(0,13):
            r=n+gap
            for length in range(1,21):
                xs=range(r+1,r+length+1)
                value=disp(xs,n)
                assert value==(2**n-1)*sum((F(1,2**a-1) for a in xs),F())
                assert value<=F(2**(n+1),2**r)
                c+=1
    counts['tail_identity_and_bound']=c
    # Quantitative amplification bound for arbitrary disjoint finite split.
    c=0
    for aa in subsets(range(1,9)):
        aa=set(aa)
        for n in range(1,13):
            bb={a for a in aa if a%2==0}
            residual=aa-bb
            assert disp(aa,n)<=disp(bb,n)+(2**n-1)*sum((F(1,2**a-1) for a in residual),F())
            c+=1
    counts['residual_mass_budget']=c
    # Exact gcd orbit means at every tested integer base, not just binary.
    c=0
    for b in range(2,7):
        for d in range(1,26):
            for q in range(1,21):
                g=gcd(q,d);length=d//g
                mean=sum((F(b**((q*m)%d),b**d-1) for m in range(1,length+1)),F())/length
                assert mean==F(g,d*(b**g-1))
                c+=1
    counts['all_base_gcd_means']=c
    # Finite atom averaging domination used in the editorial proof.
    c=0
    for b in range(2,6):
        for d in range(1,14):
            for q in range(1,9):
                for x in range(1,8):
                    avg=sum((F(b**((q*m)%d),b**d-1) for m in range(1,x+1)),F())/x
                    assert avg<=F(q+2,d)
                    c+=1
    counts['finite_average_domination']=c
    # Erasure: exact multiplicative pointwise inequality; exact incidence mean.
    c=0
    for ff in subsets([2,3,4,6,10]):
        period=lcm(*ff) if ff else 1
        for dd in subsets(ff):
            dd=set(dd);rem=set(ff)-dd
            count_total=0
            for n in range(1,period+1):
                u=sum(n%a==0 for a in dd)
                v=sum(n%a==0 for a in rem)
                assert 1+u+v<=(1+u)*(1+v)
                count_total+=u
                c+=1
            assert F(count_total,period)==harmonic(dd)
    counts['pointwise_erasure_and_incidence']=c
    # Exact CRT expectation on disjoint centre-valuation events.
    frames_test=[]
    c=0
    for q,blocks in [(2,[[3],[5],[7]]),(3,[[2,5],[7],[11]])]:
        frames=[{q**k*d for d in divisors(prod(ps))} for k,ps in enumerate(blocks,1)]
        ff=set().union(*frames);period=lcm(*ff)
        records=[]
        for k in range(1,len(blocks)):
            event=[n for n in range(1,period+1) if vp(n,q)==k]
            assert F(len(event),period)==F(q-1,q**(k+1))
            totalz=0
            for n in event:
                z=sum(n%p==0 for p in blocks[k-1])
                incidence=sum(n%a==0 for a in ff)
                assert incidence>=2**z
                totalz+=z;c+=1
            assert F(totalz,len(event))==harmonic(blocks[k-1])
            records.append({'k':k,'density':str(F(len(event),period)),
                            'conditional_mean':str(F(totalz,len(event)))})
        frames_test.append({'centre':q,'period':period,'checks':records})
    counts['crt_valuation_events']=c
    # A literal first stage of the prime partition: mass > 1, exact annihilation,
    # and a uniform certificate for every later continuation above the cutoff.
    active={2,3,5}; n=30;k=1;r=n+k+3
    assert harmonic(active)>=1
    assert all(n%p==0 for p in active)
    assert disp(active,n)==0
    assert F(2**(n+1),2**r)==F(1,8)==F(1,2**(k+2))
    other=set(primes_upto(r))-active
    certificate={'active_prefix':sorted(active),'active_harmonic_mass':str(harmonic(active)),
                 'return_time':n,'protected_cutoff':r,'uniform_future_displacement_bound':'1/8',
                 'other_colour_prefix':sorted(other)}
    # Boundary checks for the prime-core argument are finite algebra only.
    assert F(4,3)*sum((F(1,2**a) for a in range(2,70)),F())<F(2,3)
    for a in range(2,100): assert F(1,2**a-1)<=F(4,3)*F(1,2**a)
    out={'status':'all exact finite assertions passed','counts':counts,
         'crt_examples':frames_test,'prime_partition_first_stage':certificate,
         'boundary':'No full infinite prime-block construction was enumerated. No Lean/Comparator build was run.'}
    target=Path(__file__).with_name('results.json')
    target.write_text(json.dumps(out,indent=2)+'\n')
    print(json.dumps(out,indent=2))
if __name__=='__main__': main()
