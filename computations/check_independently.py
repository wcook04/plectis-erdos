#!/usr/bin/env python3
# SPDX-FileCopyrightText: 2026 Will Cook
# SPDX-License-Identifier: Apache-2.0
"""Independent finite cross-checks, not a substitute for polynomial identities.

Uses Fraction Gaussian elimination rather than the polynomial determinant engine;
uses exhaustive permutations rather than the residue subset dynamic programme.
Writes only the explicitly requested new output file. No network or Lean.
"""
from fractions import Fraction as F
from functools import lru_cache
from pathlib import Path
from itertools import permutations
import argparse,json,sys,subprocess,tempfile
import sympy as sp
from polynomials import p,entry_residue,phi,gaussian,index
from reproduce import residue_witness
ROOT=Path(__file__).resolve().parent

def require(c,msg):
    if not c:raise ArithmeticError(msg)

def det(a):
    a=[list(row) for row in a];n=len(a);answer=F(1)
    for j in range(n):
        pivot=next((i for i in range(j,n) if a[i][j]),None)
        if pivot is None:return F(0)
        if pivot!=j:a[pivot],a[j]=a[j],a[pivot];answer=-answer
        v=a[j][j];answer*=v
        for i in range(j+1,n):
            q=a[i][j]/v
            for k in range(j+1,n):a[i][k]-=q*a[j][k]
    return answer

@lru_cache(None)
def g(n,k,x):
    if k<0 or k>n:return F(0)
    if k in (0,n):return F(1)
    return g(n-1,k,x)+x**(n-k)*g(n-1,k-1,x)

def moment_values(x):
    out=[];factorial=F(1)
    for m in range(16):
        if m:factorial*=sum(x**j for j in range(m))
        r=sum(((-1)**(m+k)*x**(k*(k+1)//2)*g(m,k,x)*g(m+k,k,x) for k in range(m+1)),F(0))
        out.append(factorial**3*r)
    return out

def eval_coeffs(cs,x):
    a=F(0)
    for c in reversed(cs):a=a*x+F(c)
    return a

def inverse_series(a,n):
    require(a[0]==1,'series must have unit constant term');b=[F(1)]
    for k in range(1,n+1):b.append(-sum((a[j]*b[k-j] for j in range(1,min(k,len(a)-1)+1)),F(0)))
    return b

def main():
    ap=argparse.ArgumentParser(description=__doc__);ap.add_argument('--output',type=Path,required=True);a=ap.parse_args()
    if a.output.exists():ap.error('refusing to overwrite output')
    rows=[]
    for x in [F(1),F(3,2),F(2)]:
        s=moment_values(x);D=[F(1)];E=[F(1)]
        for h,target in [(0,D),(1,E)]:
            for n in range(1,9):
                d=det([[s[i+j+h] for j in range(n)] for i in range(n)])
                cs=json.loads((ROOT/f'certificates/s_hankel_rank{n}_shift{h}.json').read_text())['coefficients_low_to_high']
                require(d==eval_coeffs(cs,x-1),f'polynomial value n={n},h={h},p={x}')
                require(d>0,'determinant sign');target.append(d)
        ls=[]
        for n in range(1,9):
            ls.append(E[n]*D[n-1]/(D[n]*E[n-1]))
            if n<8:ls.append(D[n+1]*E[n-1]/(E[n]*D[n]))
        require(all(v>0 for v in ls),'Stieltjes coefficients positive')
        tail=[F(1)]+[F(0)]*15
        for v in reversed(ls):tail=inverse_series([F(1)]+[-v*c for c in tail[:15]],15)
        require(tail==s,'formal S-fraction coefficient comparison through order 15')
        rows.append({'p':str(x),'moment_determinants_checked':16,'Stieltjes_coefficients_checked':15,'series_order_checked':15})
    comparisons=0
    for n in range(1,6):
        for d in range(1,9):
            y=1 if n==1 else 0;mincost=None;total=sp.Poly(0,p,domain=sp.QQ)
            for sigma in permutations(range(n)):
                terms=[entry_residue(i+sigma[i],d) for i in range(n)];cost=sum(t[0] for t in terms)
                if mincost is not None and cost>mincost:continue
                inv=sum(sigma[i]>sigma[j] for i in range(n) for j in range(i+1,n));v=sp.Poly((-1)**inv,p,domain=sp.QQ)
                for _,aa,bb in terms:v=(v*(aa*y-bb)).rem(phi(d))
                if mincost is None or cost<mincost:mincost,total=cost,v
                else:total=(total+v).rem(phi(d))
            e,r=residue_witness(n,d,y);require(e==mincost and r==total,f'permutation cross-check {n,d}')
            comparisons+=1
    invalid=0
    for fun,args in [(index,(-1,)),(index,(True,)),(index,(1.5,)),(gaussian,(3,0.5)),(phi,(0,)),(phi,(True,))]:
        try:fun(*args)
        except ValueError:invalid+=1
        else:raise ArithmeticError('invalid input was accepted')
    # The optimisation flag must not disable explicit contract checks.
    cp=subprocess.run([sys.executable,'-O',str(ROOT/'reproduce.py'),'--output',str(ROOT/'certificates')],capture_output=True,text=True)
    require(cp.returncode!=0 and 'not empty' in cp.stderr,'nonempty output guard under -O')
    result={'schema':'independent_finite_cross_checks_v1','fraction_elimination_samples':rows,'exhaustive_permutation_residue_checks':comparisons,'invalid_input_checks':invalid,'nonempty_output_guard_under_optimised_python':True,'scope':'Pointwise cross-checks do not independently prove polynomial identities; the full coefficient calculation is the primary finite certificate. No Lean run.'}
    a.output.parent.mkdir(parents=True,exist_ok=True)
    with a.output.open('x') as f:json.dump(result,f,indent=2);f.write('\n')
    print('48 exact pointwise determinant comparisons; 45 Stieltjes coefficients; 40 exhaustive residue comparisons passed.')
if __name__=='__main__':main()
