#!/usr/bin/env python3
# SPDX-FileCopyrightText: 2026 Will Cook
# SPDX-License-Identifier: Apache-2.0
"""Exact finite certificates for pass 2. Python 3.10+, standard library only.
No logarithmic rounding, network access, or formal-system invocation.
Run without -O: inherited check_structures uses assertions.
"""
from __future__ import annotations
from fractions import Fraction as F
from pathlib import Path
from math import gcd
import argparse, copy, json, platform
from check_structures import literal_data
from verify_certificates import verify, CertificateError

def floorlog(num: int, den: int, p: int) -> int:
    if not (num >= den > 0 and p >= 2): raise ValueError('invalid floorlog arguments')
    power, k = den, 0
    while power*p <= num: power *= p; k += 1
    return k

def triangle(u: int) -> list[tuple[int,int,int]]:
    out=[]; q3=1; j=0; bound=1 << (u+1)
    while q3 < bound:
        q5=1; k=0
        while q3*q5 < bound:
            out.append((j,k,q3*q5)); k+=1; q5*=5
        j+=1; q3*=3
    return out

def run() -> tuple[dict,dict]:
    P,m,z3,z5=literal_data(160)
    rows=[]
    for u in (0,35,70,105):
        points=triangle(u); counts=[0]*(max(x[0] for x in points)+1)
        for j,k,y in points: counts[j]+=1
        rows.append(dict(u=u,floor3_u=z3[u],floor3_u_plus_1=z3[u+1],
                         floor5_u=z5[u],floor5_u_plus_1=z5[u+1],
                         row_counts=counts,total=sum(counts),m=m[u]))
    cs=[1,-3,3,-1]
    cert={'schema':'erdos269_pass2_certificates_v1','date':'2026-09-16',
          'no_crossing_cubic':{'a':0,'r':35,'coefficients':cs,'rows':rows,'D':45},
          'window_grid':{'B_max':97,'start_min':1,'start_max':96,'max_length':24,
                         'coprime_to':30,'bound':'floor(B*(n*n+8*n+18)/9), n=a+floor_log_3(2^a)+floor_log_5(2^a)',
                         'witnesses':[],'failures':[]},
          'scope':'Only this finite rectangle and this particular cubic instance are certified; no infinite escape or general no-go conclusion.'}
    grid=cert['window_grid']
    for B in range(1,98):
        if gcd(B,30)!=1: continue
        for ell in range(1,97):
            W,forcing=1,0
            for h in range(1,25):
                a=ell+h-1;b=P[a+1]//P[a];W*=b;forcing=b*forcing+m[a]
                end=ell+h;nn=end+z3[end]+z5[end];K=B*(nn*nn+8*nn+18)//9
                R=1+((-B*forcing-1)%W)
                if R>K:
                    grid['witnesses'].append(dict(B=B,start=ell,length=h,W=W,F=forcing,R=R,K=K))
                    break
            else: grid['failures'].append({'B':B,'start':ell})
    strip_checks=0
    for a in (0,1,2,5,10):
        for r in (1,2,5,11,35):
            smax=a+3*r
            D=15*sum((F(c*P[j*r]*P[a+1],P[a+j*r+1])*m[a+j*r]
                       for j,c in enumerate(cs)),F(0))
            total=F(0)
            for j,k,odd in triangle(smax):
                s=next(s for s in range(4) if odd < (1 << (a+s*r+1)))
                den=1 << (odd.bit_length()-1);num=odd << a
                e3=floorlog(num,den,3);e5=floorlog(num,den,5)
                omega=F(3)**(z3[a+1]-e3)*F(5)**(z5[a+1]-e5)
                suffix=F(0)
                for nu in range(s,4):
                    k3=floorlog(num << (nu*r),den,3)-e3-z3[nu*r]
                    k5=floorlog(num << (nu*r),den,5)-e5-z5[nu*r]
                    if k3 not in (0,1) or k5 not in (0,1): raise AssertionError('carry outside alphabet')
                    suffix+=F(cs[nu],3**k3*5**k5)
                total+=omega*suffix
            if D!=15*total: raise AssertionError('strip identity failed')
            strip_checks+=1
    denominator_checks=onset_checks=0
    for u in range(5):
        for v in range(5):
            for w in range(5):
                M=2**u*3**v*5**w
                onset=next(a for a in range(1,40) if (1 << a)>=max(2**(u+1),3**v,5**w))
                if onset>u+1+2*v+3*w: raise AssertionError('onset bound')
                for B in (1,7,11,13):
                    for N in (1, M*B+1):
                        if gcd(N,M*B)!=1: raise AssertionError('fixture not reduced')
                        for a in range(1,15):
                            h=P[a]//2; x=F(h*N,M*B)-17
                            if x.denominator!=M*B//gcd(M,h): raise AssertionError('denominator formula')
                            if (B*x).denominator!=M//gcd(M,h): raise AssertionError('scaled denominator')
                            if ((B*x).denominator==1)!=(a>=onset): raise AssertionError('exact onset')
                            denominator_checks+=1
                onset_checks+=1
    recoding_checks=coefficient_checks=0
    for a in range(150):
        if 30**(a+1)%P[a+1]: raise AssertionError('base-30 divisibility')
        e=m[a]*30**(a+1)//P[a+1];v=F(m[a]*8**(a+1),P[a+1])
        if F(e,30**(a+1))!=F(m[a],P[a+1]) or F(e)<F(15,4)**(a+1): raise AssertionError('base30')
        if not (0<v<225*(a+1)**2): raise AssertionError('base8 bound')
        d=v.denominator
        for p in (3,5):
            while d%p==0:d//=p
        if d!=1:raise AssertionError('base8 localisation')
        recoding_checks+=1
    C=225*sum(abs(c)*max(1,j)**2 for j,c in enumerate(cs))
    for r in range(1,40):
        for a in range(160-3*r):
            D=15*sum((F(c*P[j*r]*P[a+1],P[a+j*r+1])*m[a+j*r] for j,c in enumerate(cs)),F(0))
            if D.denominator!=1 or abs(D)>C*(a+r+1)**2:raise AssertionError('D coefficient bound')
            coefficient_checks+=1
        J=3
        if sum(F(abs(cs[j]),2**((J-j)*r)) for j in range(J))<abs(cs[J]):
            if 15*sum(cs[j]*P[j*r] for j in range(4))==0:raise AssertionError('A nonzero threshold')
    independent=verify(cert)
    mutations=[]
    for name,path in [
      ('row_count',['no_crossing_cubic','rows',1,'row_counts',0]),
      ('floor_crossing',['no_crossing_cubic','rows',2,'floor3_u_plus_1']),
      ('cubic_result',['no_crossing_cubic','D']),
      ('window_residue',['window_grid','witnesses',0,'R']),
      ('window_cap',['window_grid','witnesses',0,'K']),
      ('grid_extent',['window_grid','start_max'])]:
        bad=copy.deepcopy(cert);cursor=bad
        for key in path[:-1]:cursor=cursor[key]
        cursor[path[-1]]+=1
        try:verify(bad)
        except (CertificateError,ValueError):mutations.append({'mutation':name,'rejected':True})
        else:raise AssertionError('verifier accepted '+name)
    result={'schema':'erdos269_pass2_checks_v1','python':platform.python_version(),
            'independent_certificate_verification':independent,'strip_identity_cases':strip_checks,
            'exact_denominator_cases':denominator_checks,'minimal_onset_fixtures':onset_checks,
            'direct_recoding_indices':recoding_checks,'explicit_D_bound_cases':coefficient_checks,
            'mutation_tests':mutations,'formal_systems_run':[],
            'limitations':['Finite checks do not prove irrationality, eventual sparse defects, or a general obstruction to all operators.',
                           'Denominator tests use synthetic reduced rational values, not an assertion that the target series is rational.',
                           'No large historical scan or missing denominator-exclusion certificate was reconstructed.']}
    return cert,result

def main() -> None:
    parser=argparse.ArgumentParser();parser.add_argument('--output-dir',type=Path,default=Path(__file__).resolve().parent)
    a=parser.parse_args();a.output_dir.mkdir(parents=True,exist_ok=True)
    cert,result=run()
    for name,obj in [('pass2_certificates.json',cert),('pass2_checks.json',result)]:
        (a.output_dir/name).write_text(json.dumps(obj,indent=2)+'\n')
    print(json.dumps(result,indent=2))
if __name__=='__main__':main()
