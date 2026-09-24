#!/usr/bin/env python3
# SPDX-FileCopyrightText: 2026 Will Cook
# SPDX-License-Identifier: Apache-2.0
"""Exact regeneration of actual dyadic digits and finite tail enclosures.

The generator certifies every logarithmic floor by rational lower/upper bounds,
then evaluates pair-count sums using integer floor_sum. It aborts if any lower
and upper answer differ. No floating-point comparison is a proof predicate.
This Python computation is NOT a Lean proof of the generated digit list.
"""
from __future__ import annotations
import argparse
import hashlib
import json
import math
from fractions import Fraction
from pathlib import Path
import sys
import time

sys.set_int_max_str_digits(1_000_000)
PRIMES = (2, 3, 5)
BITS = 256
T = 1 << BITS


def ln_interval(x: Fraction, n: int = 210) -> tuple[Fraction, Fraction]:
    if x < 1:
        l, u = ln_interval(1/x, n)
        return -u, -l
    t = (x-1)/(x+1)
    t2 = t*t
    z = t
    total = Fraction(0)
    for k in range(n):
        total += 2*z/(2*k+1)
        z *= t2
    remainder = 2*z/((2*n+1)*(1-t2))
    return total, total+remainder


def log_bounds() -> dict[tuple[int,int], tuple[int,int]]:
    bounds = {2: ln_interval(Fraction(2)), 3: ln_interval(Fraction(3))}
    lo, hi = ln_interval(Fraction(5,4))
    bounds[5] = (2*bounds[2][0]+lo, 2*bounds[2][1]+hi)
    answer = {}
    for p in PRIMES:
        for q in PRIMES:
            lower = bounds[p][0]/bounds[q][1]
            upper = bounds[p][1]/bounds[q][0]
            answer[p,q] = (int(lower*T), -((-upper*T).numerator//(-upper*T).denominator))
            assert Fraction(answer[p,q][0],T) <= lower <= upper <= Fraction(answer[p,q][1],T)
    return answer


def floor_sum(n: int, m: int, a: int, b: int) -> int:
    """sum_{i=0}^{n-1} floor((a*i+b)/m), also for signed a,b."""
    if n < 0 or m <= 0:
        raise ValueError((n,m,a,b))
    qa,a = divmod(a,m)
    qb,b = divmod(b,m)
    answer = qa*n*(n-1)//2 + qb*n
    while True:
        if a >= m:
            answer += n*(n-1)*(a//m)//2
            a %= m
        if b >= m:
            answer += n*(b//m)
            b %= m
        y = a*n+b
        if y < m:
            return answer
        n = y//m
        b = y%m
        m,a = a,m


def certified_floor(e: int, p: int, q: int, bounds: dict) -> int:
    if p == q:
        return e
    lo,hi = bounds[p,q]
    l, u = e*lo//T, e*hi//T
    if l != u:
        raise ArithmeticError(('log floor not decided',e,p,q,l,u))
    return l


def pair_width(e: int, p: int, bounds: dict) -> int:
    q,r = [s for s in PRIMES if s != p]
    I = certified_floor(e,p,q,bounds)
    al,au = bounds[p,r]
    bl,bu = bounds[q,r]
    lower = I+1+floor_sum(I+1,T,-bu,e*al)
    upper = I+1+floor_sum(I+1,T,-bl,e*au)
    if lower != upper:
        raise ArithmeticError(('pair count not decided',e,p,lower,upper))
    return lower


def build_blocks(max_a: int) -> tuple[list[dict[str,int]],dict]:
    bounds = log_bounds()
    end_exp = {p: certified_floor(max_a+1,2,p,bounds)+1 for p in PRIMES}
    widths, cumulative = {}, {}
    for p in PRIMES:
        w = [0]+[pair_width(e,p,bounds) for e in range(1,end_exp[p]+1)]
        c = [0]
        for v in w[1:]:
            c.append(c[-1]+v)
        widths[p],cumulative[p] = w,c
    # No real-log or float sorting: the internal prime powers are actual integers.
    pow3=[1]
    pow5=[1]
    for _ in range(end_exp[3]): pow3.append(3*pow3[-1])
    for _ in range(end_exp[5]): pow5.append(5*pow5[-1])
    blocks=[]
    for a in range(1,max_a+1):
        e3=certified_floor(a,2,3,bounds)
        e5=certified_floor(a,2,5,bounds)
        f3=certified_floor(a+1,2,3,bounds)
        f5=certified_floor(a+1,2,5,bounds)
        internal=[]
        if f3>e3: internal.append((pow3[f3],3,f3))
        if f5>e5: internal.append((pow5[f5],5,f5))
        internal.sort()
        b=2
        for _,p,_ in internal: b*=p
        assert b in (2,6,10,30)
        m=widths[2][a+1]
        suffix=1
        for _,p,e in reversed(internal):
            strip=cumulative[p][e]-cumulative[2][a]
            assert strip>=0
            m+=(p-1)*suffix*strip
            suffix*=p
        assert m>0
        blocks.append(dict(a=a,b=b,m=m,e3=e3,e5=e5,
                           endpoint_jump_index=a+1+f3+f5))
    meta=dict(log_interval_terms=210,dyadic_precision_bits=BITS,
              ratio_bounds={f'{p}/{q}':list(bounds[p,q]) for p,q in bounds},
              widths_evaluated=sum(end_exp.values()),
              largest_width=max(max(v) for v in widths.values()),
              all_floor_lower_upper_answers_equal=True)
    return blocks,meta


def compose(blocks: list[dict], start: int, length: int) -> tuple[int,int]:
    W,F=1,0
    for b in blocks[start-1:start-1+length]:
        W*=b['b']
        F=b['b']*F+b['m']
    return W,F


def qcap(a: int, e3: int, e5: int) -> Fraction:
    n=a+e3+e5
    return Fraction(n*n+8*n+18,9)


def common_cf(lo: Fraction, hi: Fraction, limit: int=100_000) -> tuple[list[int],dict]:
    """Common prefix for all points in the CLOSED input rational interval."""
    if not lo<hi: raise ValueError('strict interval needed')
    digits=[]
    pn2,pn1,qn2,qn1=0,1,1,0
    for _ in range(limit):
        a,b=lo.numerator//lo.denominator,hi.numerator//hi.denominator
        if a!=b: break
        digits.append(a)
        pn2,pn1=pn1,a*pn1+pn2
        qn2,qn1=qn1,a*qn1+qn2
        lo,hi=lo-a,hi-a
        if lo==0 or hi==0: break
        lo,hi=1/hi,1/lo
    return digits,dict(last_p=str(pn1),last_q=str(qn1),previous_p=str(pn2),previous_q=str(qn2))


def cf_farey_cell(digits: list[int]) -> tuple[Fraction,Fraction]:
    """The two rational endpoints of the cylinder with this finite prefix."""
    pm2,pm1,qm2,qm1=0,1,1,0
    for a in digits:
        pm2,pm1=pm1,a*pm1+pm2
        qm2,qm1=qm1,a*qm1+qm2
    ends=[Fraction(pm1,qm1),Fraction(pm1+pm2,qm1+qm2)]
    return min(ends),max(ends)


def direct_block(a: int) -> tuple[int,int]:
    """Independent brute source enumeration, used only at small a."""
    lower,upper=1<<a,1<<(a+1)
    def ilog(b,x):
        n=0
        while b**(n+1)<=x: n+=1
        return n
    def H(x): return math.prod(p**ilog(p,x) for p in PRIMES)
    shell=[]
    for i in range(a+1):
        for j in range(ilog(3,upper)+1):
            for k in range(ilog(5,upper)+1):
                x=(1<<i)*3**j*5**k
                if lower<=x<upper: shell.append(x)
    endpoint=H(upper)
    m=sum(Fraction(endpoint,2*H(x)) for x in shell)
    assert m.denominator==1
    return endpoint//H(lower),int(m)


def main() -> None:
    ap=argparse.ArgumentParser()
    ap.add_argument('--max-a',type=int,default=15500)
    ap.add_argument('--out',type=Path,default=Path('regenerated'))
    args=ap.parse_args()
    args.out.mkdir(parents=True,exist_ok=True)
    start=time.perf_counter()
    blocks,meta=build_blocks(args.max_a)
    tgen=time.perf_counter()-start
    for a in range(1,31):
        assert (blocks[a-1]['b'],blocks[a-1]['m'])==direct_block(a)
    W,F=compose(blocks,1,args.max_a)
    end=args.max_a+1
    bounds=log_bounds()
    e3=certified_floor(end,2,3,bounds)
    e5=certified_floor(end,2,5,bounds)
    K=qcap(end,e3,e5)
    lower=Fraction(F,W)
    upper=Fraction(F,W)+K/W
    digits,conv=common_cf(lower,upper)
    (args.out/'dyadic_blocks.json').write_text(json.dumps(dict(schema='actual-235-blocks/1',
        claim_ceiling='exact_Python_regeneration_not_Lean_checked',meta=meta,blocks=blocks),separators=(',',':'))+'\n')
    (args.out/'cf_common_prefix.json').write_text(json.dumps(dict(digits=digits,**conv),separators=(',',':'))+'\n')
    certificates={}
    for count in sorted(set([min(len(digits),13109),len(digits)])):
        if count<1: continue
        left,right=cf_farey_cell(digits[:count])
        assert left<lower<upper<right
        det=right.numerator*left.denominator-left.numerator*right.denominator
        assert det==1
        min_den=left.denominator+right.denominator
        certificates[str(count)]=dict(
            left_numerator=str(left.numerator),left_denominator=str(left.denominator),
            right_numerator=str(right.numerator),right_denominator=str(right.denominator),
            determinant=det,minimum_denominator_in_open_cell=str(min_den),
            excludes_denominators_through_2_pow_22482=(1<<22482)<min_den,
            cf_max=max(digits[:count]),cf_sum=sum(digits[:count]),
            min_den_bit_length=min_den.bit_length())
    report=dict(parameters=dict(max_a=args.max_a),generator_seconds=tgen,
      total_seconds=time.perf_counter()-start,blocks_count=len(blocks),
      W_bits=W.bit_length(),F_bits=F.bit_length(),
      actual_target='X_1 = S-1 (half-normalised actual tail)',
      lower_numerator=str(lower.numerator),lower_denominator=str(lower.denominator),
      upper_numerator=str(upper.numerator),upper_denominator=str(upper.denominator),
      endpoint_cap_numerator=str(K.numerator),endpoint_cap_denominator=str(K.denominator),
      common_prefix_length=len(digits),first_20=digits[:20],certificates=certificates,
      direct_source_blocks_checked=30,
      unresolved_Lean_step='identify each regenerated block with literal actual forcing; transfer finite rational enclosure to actual tail',
      meta=meta)
    (args.out/'tail_certificate.json').write_text(json.dumps(report,indent=2)+'\n')
    public={k:v for k,v in report.items() if k not in ['lower_numerator','lower_denominator','upper_numerator','upper_denominator','meta','certificates']}
    public['certificates']={k:{a:b for a,b in v.items() if not a.endswith(('numerator','denominator')) and a!='minimum_denominator_in_open_cell'} for k,v in certificates.items()}
    print(json.dumps(public,indent=2))

if __name__=='__main__': main()
