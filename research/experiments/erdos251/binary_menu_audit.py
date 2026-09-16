# SPDX-FileCopyrightText: 2026 Will Cook
# SPDX-License-Identifier: Apache-2.0
"""Exact finite central-menu experiments for the prescribed binary family.

All scheduling floors are certified using rational bounds for sqrt and exp.
All weights, subsums, central-band endpoints and tests use integers/Fractions.
This is finite evidence only: no asymptotic interior theorem is asserted.
"""
from __future__ import annotations
from fractions import Fraction as F
from functools import lru_cache
from math import isqrt, lcm, prod, ceil
from pathlib import Path
import argparse, hashlib, json

@lru_cache(maxsize=None)
def exp_bounds(x: F, terms: int=80) -> tuple[F,F]:
    if x < 0 or terms+2 <= x:
        raise ValueError('Need x>=0 and terms+2>x')
    term=F(1); total=term
    for n in range(1,terms+1):
        term=term*x/n; total+=term
    nxt=term*x/(terms+1)
    return total, total+nxt/(1-x/F(terms+2))

@lru_cache(maxsize=None)
def site(j: int, c: F) -> int:
    if j<0 or c<=0: raise ValueError('j>=0 and c>0 required')
    x=F(j)/c
    for precision in (20,40):
        d=10**precision; k=isqrt((x.numerator*d*d)//x.denominator)
        lo=F(k,d); hi=F(k+1,d)
        if lo*lo==x: hi=lo
        elo,_=exp_bounds(lo); _,ehi=exp_bounds(hi)
        a=elo.numerator//elo.denominator
        b=ehi.numerator//ehi.denominator
        if a==b: return a
    raise ArithmeticError(f'Could not certify floor exp sqrt(j/c): {j}, {c}')

@lru_cache(maxsize=None)
def height(s: int) -> int:
    if s<1: raise ValueError('s>=1 required')
    k=1
    while True:
        lo,hi=exp_bounds(F(k))
        if s+1 < lo: return k
        if s+1 <= hi:
            raise ArithmeticError('Height comparison unresolved')
        k+=1

@lru_cache(maxsize=None)
def block(c: F,k: int) -> tuple[tuple[int,int,int],...]:
    # ceil(log(s+1))=k implies s<e^k and hence j/c<k^2,
    # apart from the harmless floor edge; the generous bound below is certified
    # afterwards by checking the first excluded index and monotonicity.
    j0=ceil(9*c)
    top=ceil(c*(k+1)**2)+4
    rows=[]
    for j in range(j0,top+1):
        s=site(j,c)
        if height(s)==k:
            denominator=prod(s+t for t in range(1,k))*(s+k+1)
            rows.append((j,s,denominator))
    if height(site(top,c))<=k: raise ArithmeticError('Insufficient enumeration horizon')
    return tuple(rows)

def serial(q: F) -> dict:
    return {'numerator':str(q.numerator),'denominator':str(q.denominator)}

def experiment(c: F,k: int,max_terms: int=18) -> dict:
    rows=block(c,k); following=block(c,k+1)
    if not rows or len(rows)>max_terms: raise ValueError('Block outside enumeration limit')
    if len({s for _,s,_ in rows})!=len(rows): raise ArithmeticError('Repeated sites')
    ds=[d for _,_,d in rows]; common=lcm(*ds)
    weights=[common//d for d in ds]
    sums=[0]
    for w in weights:
        sums += [v+w for v in sums]
    sums=sorted(set(sums)); width=sum(weights)
    central=[v for v in sums if width<=4*v<=3*width]
    if len(central)<2: raise ArithmeticError('Central menu degenerates')
    diameter=central[-1]-central[0]
    largest=max(b-a for a,b in zip(central,central[1:]))
    next_width=sum((F(1,d) for _,_,d in following),F(0))
    ratio=F(largest,common)/next_width
    digest=hashlib.sha256(('\n'.join(map(str,sums))+'\n').encode()).hexdigest()
    return {'c':str(c),'height':k,'first_index':rows[0][0],'last_index':rows[-1][0],
            'sites':[s for _,s,_ in rows], 'reciprocal_denominators':[str(d) for d in ds],
            'term_count':len(rows),'formal_choices':1<<len(rows),
            'distinct_subsums':len(sums),'central_points':len(central),
            'common_denominator':str(common),'block_width_numerator':str(width),
            'central_diameter_numerator':str(diameter),'central_max_gap_numerator':str(largest),
            'next_block_width':serial(next_width),'central_gap_over_next_width':serial(ratio),
            'central_diameter_at_least_quarter_width':4*diameter>=width,
            'central_gap_at_most_quarter_next_width':ratio<=F(1,4),
            'sorted_subsums_sha256':digest}

def audit() -> dict:
    # For c<=2, u>=3 gives e^u/(2cu)>=e^3/12>1. Therefore the
    # unrounded sites increase by more than one for j>=ceil(9c), proving
    # that every later integer site is distinct, not just the sampled ones.
    if exp_bounds(F(3))[0]<=12: raise ArithmeticError('Distinct-site premise failed')
    rows=[experiment(c,k) for c in (F(1),F(3,2),F(2)) for k in (4,5)]
    # Pure unit checks for exact cancellation and floor certificates.
    for k in range(1,7):
        for s in (2,5,20):
            lhs=F(1,prod(s+t for t in range(1,k+1)))-F(1,prod(s+t for t in range(1,k+2)))
            rhs=F(1,prod(s+t for t in range(1,k))*(s+k+1))
            if lhs!=rhs: raise ArithmeticError('Unit-fraction identity failed')
    return {'schema':'erdos251_binary_menu_audit_v1','date':'2026-09-16',
            'arithmetic':'Exact integers and rational intervals; no floating-point schedule decisions',
            'central_band':'[W_k/4,3W_k/4]', 'term_limit':18,
            'hypothesis_tested':'diameter(Y_k)>=W_k/4 and gap(Y_k)<=W_(k+1)/4',
            'scope':'Six finite blocks only; this does not establish eventual inequalities, interior or its absence.',
            'experiments':rows,'reproducibility':'Deterministic output; elapsed time excluded.'}

if __name__=='__main__':
    ap=argparse.ArgumentParser(description=__doc__)
    ap.add_argument('--output',type=Path,default=Path('binary_menu_results.json'))
    args=ap.parse_args(); result=audit()
    args.output.parent.mkdir(parents=True,exist_ok=True)
    args.output.write_text(json.dumps(result,indent=2)+'\n')
    for r in result['experiments']:
        rat=r['central_gap_over_next_width']
        ratio=F(int(rat['numerator']),int(rat['denominator']))
        print(r['c'],r['height'],r['term_count'],r['distinct_subsums'],
              'gap/next width (display approximation only):',f'{float(ratio):.6g}',
              'quarter-width test:',r['central_gap_at_most_quarter_next_width'])
