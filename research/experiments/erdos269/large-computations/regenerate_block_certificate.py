#!/usr/bin/env python3
# SPDX-FileCopyrightText: 2026 Will Cook
# SPDX-License-Identifier: Apache-2.0
"""Regenerate a 64-start, length-128 lattice certificate from actual digits.
LLL is a search only. All acceptance checks are integer and fraction-free.
The first 64 starts >=10005 with the launch product are selected deterministically.
This need not reproduce an archived basis; it is a new certificate at the same scale.
"""
import argparse, json, math, time
from pathlib import Path
import lattice_from_packet as LA
from regenerate_269 import compose

PUBLISHED_BMAX=int('1134599670999687767349520845707093359257353022286558739363600235'
                   '016103207564063373270305324172145281971729')

def main():
    ap=argparse.ArgumentParser()
    ap.add_argument('--data',type=Path,default=Path(__file__).parent/'regenerated/dyadic_blocks.json')
    ap.add_argument('--out',type=Path,default=Path(__file__).parent/'regenerated/block_certificate.json')
    args=ap.parse_args()
    t=time.perf_counter()
    blocks=json.loads(args.data.read_text())['blocks']
    L,m,launch=128,64,10005
    P,_=compose(blocks,launch,L)
    starts=[]; force=[]
    for a in range(launch,len(blocks)-L+2):
        W,F=compose(blocks,a,L)
        if W==P:
            starts.append(a);force.append(F)
            if len(starts)==m: break
    if len(starts)!=m: raise RuntimeError('insufficient P-class starts')
    m0=P//2
    g=[f%m0 for f in force]
    rows,diag,index=LA.lambda_basis(g,m0)
    weights=[(a+L)**2+6*(a+L)+11 for a in starts]
    print(json.dumps(dict(stage='basis_ready',starts=starts,log2P=math.log2(P),index_eq_m0=index==m0)),flush=True)
    basis,steps=LA.weighted_reduce(rows,weights)
    elapsed=time.perf_counter()-t
    budgets=[LA.budget(row,weights) for row in basis]
    max_budget=max(budgets)
    determinant=LA.det_bareiss(basis)
    if abs(determinant)!=index: raise ArithmeticError('not full lattice basis')
    if not all(LA.in_lambda(row,g,m0) for row in basis): raise ArithmeticError('membership failed')
    Bmax=(P-1)//max_budget
    report=dict(schema='actual-235-lattice-certificate/1',
       evidence_status='exact_Python_regeneration_not_Lean_checked',
       selection='first 64 starts >=10005 sharing the launch window product',
       L=L,m=m,launch=launch,starts=starts,
       P=str(P),m0=str(m0),forcing=[str(f) for f in force],g=[str(x) for x in g],
       index=str(index),determinant=str(determinant),weights=weights,
       basis=basis,budgets=budgets,max_budget=max_budget,Bmax=str(Bmax),
       published_Bmax=str(PUBLISHED_BMAX),covers_published_Bmax=Bmax>=PUBLISHED_BMAX,
       seconds=elapsed,lll_steps=steps,
       checks=dict(membership=True,full_index=True,budget=Bmax*max_budget<P),
       required_remaining_formal_bridges=[
           'computed forcing entries equal actual windowForcing',
           'elaborate the full-height width and actual-series transport candidates',
           'run add_inverse_witness.py to construct the scaled inverse used by the finite consumer'])
    args.out.write_text(json.dumps(report,indent=2)+'\n')
    print(json.dumps({k:v for k,v in report.items() if k not in ['basis','forcing','g','budgets','weights']},indent=2),flush=True)
if __name__=='__main__': main()
