#!/usr/bin/env python3
# SPDX-FileCopyrightText: 2026 Will Cook
# SPDX-License-Identifier: Apache-2.0
"""Independent, integer-only verifier for pass-2 witnesses; standard library.
Does not import the producer, its floor tables, or check_structures.
Resource caps prevent an accidental unbounded run on malformed JSON.
"""
from __future__ import annotations
from pathlib import Path
from math import gcd
import argparse,json
class CertificateError(ValueError): pass

def need(condition: bool,message: str) -> None:
    if not condition:raise CertificateError(message)
def integer(x: object,lo: int,hi: int,name: str) -> int:
    need(type(x) is int and lo<=x<=hi,'invalid '+name)
    return x

def power_floor(x: int,p: int) -> tuple[int,int]:
    e,q=0,1
    while q*p<=x:e+=1;q*=p
    return e,q

def exact_shells(n: int) -> tuple[list[int],list[int],list[int]]:
    """Different enumeration order: one shell at a time, one odd pair each."""
    P=[];indices=[]
    for a in range(n+1):
        e3,p3=power_floor(1<<a,3);e5,p5=power_floor(1<<a,5)
        P.append((1<<a)*p3*p5);indices.append(a+e3+e5)
    m=[]
    for a in range(n):
        total=0;odd3=1;bound=1<<(a+1)
        while odd3<bound:
            odd=odd3
            while odd<bound:
                value=odd
                while value<(1<<a):value*=2
                _,q3=power_floor(value,3);_,q5=power_floor(value,5)
                height=(1<<a)*q3*q5
                q,rem=divmod(P[a+1],2*height)
                need(rem==0 and q in (1,3,5,15),'shell weight')
                total+=q;odd*=5
            odd3*=3
        m.append(total)
    return P,m,indices

def verify(data: dict) -> dict:
    need(data.get('schema')=='erdos269_pass2_certificates_v1','schema')
    c=data['no_crossing_cubic']
    need((c['a'],c['r'],c['coefficients'])==(0,35,[1,-3,3,-1]),'cubic fixture')
    need(len(c['rows'])==4,'row count')
    totals=[]
    for nu,row in enumerate(c['rows']):
        u=35*nu;need(row['u']==u,'shift index')
        for p in (3,5):
            e=integer(row[f'floor{p}_u'],0,150,'exponent')
            ep=integer(row[f'floor{p}_u_plus_1'],0,150,'exponent')
            need(p**e<=2**u<p**(e+1),'floor at u')
            need(p**ep<=2**(u+1)<p**(ep+1),'floor at u+1')
            need(e==ep==nu*c['rows'][1][f'floor{p}_u'],'uniform no-crossing interval')
        counts=row['row_counts'];need(1<=len(counts)<=100,'row vector size')
        bound=1<<(u+1)
        for j,num in enumerate(counts):
            k=integer(num,1,100,'row length')
            need(3**j*5**(k-1)<bound<=3**j*5**k,'row endpoint inequality')
        need(3**len(counts)>=bound,'omitted row')
        need(sum(counts)==row['total']==row['m'],'triangle total')
        totals.append(sum(counts))
    need(15*sum(x*y for x,y in zip(c['coefficients'],totals))==c['D']==45,'cubic value')
    g=data['window_grid']
    Bmax=integer(g['B_max'],1,1000,'B bound');lo=integer(g['start_min'],1,300,'start lower')
    hi=integer(g['start_max'],lo,300,'start upper');hm=integer(g['max_length'],1,50,'length bound')
    need(g['coprime_to']==30,'coprimality domain')
    P,m,ns=exact_shells(hi+hm)
    keys=set();lengths=[]
    for row in g['witnesses']:
        B=integer(row['B'],1,Bmax,'B');ell=integer(row['start'],lo,hi,'start');h=integer(row['length'],1,hm,'length')
        need(gcd(B,30)==1 and (B,ell) not in keys,'duplicate or out-of-domain witness')
        keys.add((B,ell));W,F=1,0
        for k in range(1,h+1):
            a=ell+k-1;b=P[a+1]//P[a];W*=b;F=b*F+m[a]
            n=ns[ell+k];K=B*(n*n+8*n+18)//9;R=1+((-B*F-1)%W)
            need((R>K)==(k==h),'not first escaping length')
        need((W,F,R,K)==tuple(row[k] for k in ('W','F','R','K')),'window payload')
        lengths.append(h)
    # Failures are checked rather than trusted.
    for row in g['failures']:
        B=integer(row['B'],1,Bmax,'failure B');ell=integer(row['start'],lo,hi,'failure start')
        need(gcd(B,30)==1 and (B,ell) not in keys,'duplicate failure')
        keys.add((B,ell));W,F=1,0
        for h in range(1,hm+1):
            a=ell+h-1;b=P[a+1]//P[a];W*=b;F=b*F+m[a]
            n=ns[ell+h];K=B*(n*n+8*n+18)//9;R=1+((-B*F-1)%W)
            need(R<=K,'claimed failure escaped')
    expected={(B,ell) for B in range(1,Bmax+1) if gcd(B,30)==1 for ell in range(lo,hi+1)}
    need(keys==expected,'incomplete declared rectangle')
    return {'no_crossing_rows':len(totals),'row_endpoint_inequalities':sum(len(r['row_counts']) for r in c['rows']),
            'cubic_numerators':totals,'cubic_D':45,'finite_pairs':len(expected),
            'window_witnesses':len(g['witnesses']),'finite_failures':len(g['failures']),
            'first_escape_min':min(lengths) if lengths else None,'first_escape_max':max(lengths) if lengths else None,
            'B_max':Bmax,'starts':[lo,hi],'max_length_searched':hm}

def main() -> None:
    p=argparse.ArgumentParser();p.add_argument('certificate',type=Path,nargs='?',default=Path(__file__).with_name('pass2_certificates.json'));a=p.parse_args()
    need(a.certificate.stat().st_size<10_000_000,'certificate too large')
    print(json.dumps(verify(json.loads(a.certificate.read_text())),indent=2))
if __name__=='__main__':main()
