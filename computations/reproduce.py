#!/usr/bin/env python3
# SPDX-FileCopyrightText: 2026 Will Cook
# SPDX-License-Identifier: Apache-2.0
"""Recompute exact finite certificates. No network, floating point or Lean.
A non-empty output directory is refused. Conditions remain active under -O.
"""
from pathlib import Path
import argparse,json,time,sys
import sympy as sp
from polynomials import p,diagonal,positive_diagonal,moments,alpha,beta,exact_det,phi,entry_residue

def require(condition,message):
    if not condition: raise ArithmeticError(message)
def write(out,name,obj): (out/name).write_text(json.dumps(obj,indent=2)+'\n')
def residue_witness(N,d,y):
    """Subset determinant DP retaining only minimum-valuation assignments."""
    dp={0:(0,sp.Poly(1,p,domain=sp.QQ))}
    for i in range(N):
        nd={}
        for mask,(cost,value) in dp.items():
            for j in range(N):
                if mask&(1<<j): continue
                v,a,b=entry_residue(i+j,d)
                term=(value*(a*y-b)*(-1)**((mask>>(j+1)).bit_count())).rem(phi(d))
                nc=cost+v; nm=mask|(1<<j)
                if nm not in nd or nc<nd[nm][0]: nd[nm]=(nc,term)
                elif nc==nd[nm][0]: nd[nm]=(nc,(nd[nm][1]+term).rem(phi(d)))
        dp=nd
    return dp[(1<<N)-1]

def main():
    ap=argparse.ArgumentParser(description=__doc__)
    ap.add_argument('--output',type=Path,required=True)
    ap.add_argument('--max-rank',type=int,default=8)
    ap.add_argument('--residue-max-rank',type=int,default=8)
    a=ap.parse_args()
    if not 1<=a.max_rank<=10 or not 1<=a.residue_max_rank<=10: ap.error('rank must be in 1,...,10')
    out=a.output.resolve()
    if out.exists() and any(out.iterdir()): ap.error('output directory is not empty')
    out.mkdir(parents=True,exist_ok=True); start=time.time()
    for m in range(max(13,2*a.max_rank,2*a.residue_max_rank-1)):
        require(diagonal(m)==positive_diagonal(m),f'positive expansion m={m}')
        require(moments(m).degree()==3*m*m-m and moments(m).LC()==1,f'degree m={m}')
    print('Positive expansion and monic degrees passed',flush=True)
    bare=sp.Poly(exact_det(sp.Matrix(3,3,lambda i,j:diagonal(i+j).as_expr())),p,domain=sp.QQ).shift(1)
    require([bare.nth(i) for i in range(3)]==[0,0,-36],'bare diagonal obstruction')
    results=[]
    for h in (0,1):
        for N in range(1,a.max_rank+1):
            d=sp.Poly(exact_det(sp.Matrix(N,N,lambda i,j:moments(i+j+h).as_expr())),p,domain=sp.QQ)
            dt=d.shift(1); cs=dt.all_coeffs(); degree=sum(3*(2*i+h)**2-(2*i+h) for i in range(N))
            require(d.degree()==degree and d.LC()==1,f'determinant degree {N,h}')
            require(all(c>0 for c in cs),f'coefficient positivity {N,h}')
            row={'rank':N,'shift':h,'degree':degree,'positive_at_one':str(dt.nth(0)),'all_coefficients_strictly_positive':True,'negative_coefficients':0}
            results.append(row)
            write(out,f's_hankel_rank{N}_shift{h}.json',{'variable':'t=p-1','coefficients_low_to_high':[str(c) for c in reversed(cs)]})
            print('Moment certificate',N,h,'degree',degree,'seconds',round(time.time()-start,2),flush=True)
    write(out,'finite_moment_results.json',results)
    expected=[p,p**5*(p-1)**4,p**14*(p-1)**15*(p+1)**4,p**30*(p-1)**32*(p+1)**8*(p*p+p+1)**4,p**55*(p-1)**55*(p+1)**19*(p*p+1)**4*(p*p+p+1)**8]
    contents=[]
    for N in range(1,6):
        content=sp.Poly(0,p,domain=sp.QQ)
        for y in range(N+1):
            mat=sp.Matrix(N,N,lambda i,j:(alpha(i+j)*y-beta(i+j)).as_expr())
            content=sp.gcd(content,sp.Poly(exact_det(mat),p,domain=sp.QQ))
        content=content.monic(); require(content==sp.Poly(expected[N-1],p,domain=sp.QQ),f'full content N={N}')
        contents.append({'rank':N,'monic_content':str(sp.factor(content.as_expr()))})
        print('Complete polynomial content rank',N,flush=True)
    write(out,'full_contents.json',contents)
    witnesses=[]
    for N in range(1,a.residue_max_rank+1):
        for d in range(1,max(8,2*N-2)+1):
            found=False
            for y in range(N+1):
                e,residue=residue_witness(N,d,y)
                if not residue.is_zero:
                    found=True;break
            require(found,f'cancellation encountered rank={N}, d={d}; no sharpness certificate')
            witnesses.append({'rank':N,'cyclotomic_index':d,'assignment_bound':int(e),'Y':y,'residue_coefficients_low_to_high':[str(residue.nth(k)) for k in range(phi(d).degree())]})
        print('Cyclotomic residue witnesses rank',N,flush=True)
    write(out,'cyclotomic_residue_witnesses.json',witnesses)
    write(out,'run.json',{'python':sys.version,'sympy':sp.__version__,'max_moment_rank':a.max_rank,'max_residue_rank':a.residue_max_rank,'complete_content_max_rank':5,'seconds':time.time()-start,'floating_point_used_for_mathematics':False,'lean_run':False})
    print('All exact checks passed.',flush=True)
if __name__=='__main__': main()
