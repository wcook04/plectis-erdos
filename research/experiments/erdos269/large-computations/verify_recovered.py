#!/usr/bin/env python3
# SPDX-FileCopyrightText: 2026 Will Cook
# SPDX-License-Identifier: Apache-2.0
"""Independently replay the recovered numerical witnesses; no Lean-status promotion.

Fast path: verifies the stored lattice witness rather than repeating the LLL
search. The proof predicates use integers/Fraction only. Timings use floats.
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
sys.dont_write_bytecode = True
sys.set_int_max_str_digits(1_000_000)
from regenerate_269 import build_blocks, compose, direct_block, common_cf, cf_farey_cell, floor_sum

class Checks:
    def __init__(self) -> None:
        self.groups: dict[str,int] = {}
    def check(self, group: str, condition: bool, detail: object='') -> None:
        if not condition:
            raise AssertionError((group,detail))
        self.groups[group] = self.groups.get(group,0)+1

def ilog(b: int, x: int) -> int:
    a=0
    while b**(a+1) <= x: a+=1
    return a

def main() -> None:
    ap=argparse.ArgumentParser()
    ap.add_argument('--data',type=Path,default=Path(__file__).parent/'regenerated')
    ap.add_argument('--output',type=Path)
    args=ap.parse_args(); Ck=Checks(); t0=time.perf_counter()
    raw=json.loads((args.data/'dyadic_blocks.json').read_text())
    blocks,meta=build_blocks(15500)
    Ck.check('block_regeneration',meta==raw['meta'],'metadata')
    Ck.check('block_regeneration',len(blocks)==len(raw['blocks'])==15500,'length')
    for a,(b,c) in enumerate(zip(blocks,raw['blocks']),1):
        Ck.check('block_regeneration',b==c,a)
    for a in range(1,31):
        Ck.check('independent_source_shells',(blocks[a-1]['b'],blocks[a-1]['m'])==direct_block(a),a)
    for n in range(8):
        for m in range(1,9):
            for a in range(-3,11):
                for b in range(-3,10):
                    Ck.check('signed_floor_sum', floor_sum(n,m,a,b)==sum((a*i+b)//m for i in range(n)),(n,m,a,b))
    W,F=compose(blocks,1,15500)
    cap=Fraction(340480534,3)
    lo,hi=Fraction(F,W),Fraction(F,W)+cap/W
    tr=json.loads((args.data/'tail_certificate.json').read_text())
    Ck.check('tail_interval',lo==Fraction(int(tr['lower_numerator']),int(tr['lower_denominator'])))
    Ck.check('tail_interval',hi==Fraction(int(tr['upper_numerator']),int(tr['upper_denominator'])))
    Ck.check('tail_interval',W.bit_length()==F.bit_length()==46500)
    Ck.check('tail_interval',3**9780<=2**15501<3**9781)
    Ck.check('tail_interval',5**6675<=2**15501<5**6676)
    n=15501+9780+6675
    Ck.check('tail_interval',Fraction(n*n+8*n+18,9)==cap)
    digits,convergents=common_cf(lo,hi)
    cf=json.loads((args.data/'cf_common_prefix.json').read_text())
    Ck.check('continued_fraction',len(digits)==13540)
    Ck.check('continued_fraction',digits==cf['digits'])
    for key,val in convergents.items(): Ck.check('continued_fraction',cf[key]==val,key)
    ds=digits[:13109]
    Ck.check('continued_fraction',len(ds)==13109 and ds[0]==0 and all(x>0 for x in ds[1:]))
    Ck.check('continued_fraction',max(ds)==129114 and sum(ds)==306923)
    left,right=cf_farey_cell(ds)
    Ck.check('continued_fraction',left<lo<hi<right)
    Ck.check('continued_fraction',right.numerator*left.denominator-left.numerator*right.denominator==1)
    Ck.check('continued_fraction',(1<<22482)<left.denominator+right.denominator)
    pp,p,qp,q=0,1,1,0
    for a in ds: pp,p,qp,q=p,a*p+pp,q,a*q+qp
    Ck.check('continued_fraction',Fraction(p,q)==left and Fraction(p+pp,q+qp)==right)
    b=json.loads((args.data/'block_certificate.json').read_text())
    P,m0=int(b['P']),int(b['m0']); Bmax=int(b['Bmax']); k=64
    C,D=b['basis'],b['right_inverse_scaled']; Fs=list(map(int,b['forcing']));ws=b['weights']
    Ck.check('lattice_shape',len(C)==len(D)==len(Fs)==len(ws)==len(b['starts'])==64)
    Ck.check('lattice_shape',all(len(row)==64 for row in C+D))
    Ck.check('lattice_shape',P==2**128*3**81*5**56 and P==2*m0 and m0>0)
    Ck.check('lattice_shape',b['starts'][0]==10005 and all(a>=10005 for a in b['starts']))
    Ck.check('lattice_shape',3**6312<=2**10005<3**6313 and 5**4308<=2**10005<5**4309)
    for j,a in enumerate(b['starts']):
        Ck.check('actual_window_composition',compose(blocks,a,128)==(P,Fs[j]),a)
        Ck.check('actual_window_composition',ws[j]==(a+128)**2+6*(a+128)+11,a)
    for i in range(k):
        Ck.check('lattice_row_membership',sum(C[i][j]*Fs[j] for j in range(k))%m0==0,i)
        Ck.check('lattice_budget',sum(abs(C[i][j])*ws[j] for j in range(k))==b['budgets'][i],i)
    for X,Y in ((D,C),(C,D)):
        for i in range(k):
            for j in range(k):
                Ck.check('scaled_inverse',sum(X[i][t]*Y[t][j] for t in range(k))==(m0 if i==j else 0),(i,j))
    Ck.check('lattice_exclusion',max(b['budgets'])==b['max_budget']==184560461211)
    Ck.check('lattice_exclusion',Bmax==(P-1)//b['max_budget']==int(b['published_Bmax']))
    Ck.check('lattice_exclusion',Bmax*b['max_budget']<P<=(Bmax+1)*b['max_budget'])
    for p in (2,3,5,7):
        for q in (2,3,5,7):
            if p==q: continue
            def H(x: int) -> int: return p**ilog(p,x)*q**ilog(q,x)
            for i in range(10):
                for j in range(10):
                    x=p**i*q**j
                    Ck.check('two_prime_actual_kernel',H(x)==(p**i*q**ilog(q,p**i))*(q**j*p**ilog(p,q**j)),(p,q,i,j))
            smooth=sorted({p**i*q**j for i in range(13) for j in range(13) if p**i*q**j<=5000})
            running=1
            for x in smooth:
                running=math.lcm(running,x)
                Ck.check('two_prime_running_lcm',running==H(x),(p,q,x))
    for a in range(101):
        n=a+ilog(3,2**a)+ilog(5,2**a)
        Ck.check('rank_cap_algebra',Fraction(n*n+8*n+18,9)<=3*(a+1)**2,a)
        Ck.check('rank_cap_algebra',2*Fraction(n*n+8*n+18,9)<=a*a+6*a+11,a)
    out={
        'schema':'erdos269-r8-executed-exact-checks/1', 'passed':True,
        'Lean_compilation':False, 'finite_predicates_checked':sum(Ck.groups.values()),
        'groups':Ck.groups, 'seconds':time.perf_counter()-t0,
        'cf_common_prefix_length':len(digits), 'published_cf_length':len(ds),
        'published_block_Bmax':str(Bmax),
        'limits':['No Lean elaboration, kernel reduction, or axiom audit was performed.',
          'Python-to-Lean identification of the generated actual forcing data is not proved here.',
          'The finite CF list is not yet identified with Mathlib continued fractions of the actual tail.'],
        'input_sha256':{p.name:hashlib.sha256(p.read_bytes()).hexdigest() for p in sorted(args.data.glob('*.json'))}}
    text=json.dumps(out,indent=2)+'\n'
    if args.output: args.output.write_text(text)
    print(text,end='')

if __name__=='__main__':main()
