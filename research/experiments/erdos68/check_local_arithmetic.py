#!/usr/bin/env python3
# SPDX-FileCopyrightText: 2026 Will Cook
# SPDX-License-Identifier: Apache-2.0
"""Small exact checks supporting the research note; no asymptotic inference."""
from __future__ import annotations
import argparse, hashlib, json, math
from pathlib import Path

def prime(q: int) -> bool:
    return q >= 2 and all(q % d for d in range(2, math.isqrt(q) + 1))

def cancellation(q: int) -> dict:
    assert prime(q)
    f = 1
    hits = []
    for n in range(1, q):
        f = f * n % (q*q)
        if n >= 2 and f % q == 1:
            u = ((f-1)//q) % q
            if not u:
                raise ArithmeticError('Higher valuation encountered; do not call this an exponent-one example')
            hits.append({'n': n, 'unit_cofactor': u, 'inverse': pow(u, -1, q)})
    return {'prime': q, 'prefix_end': q-1, 'all_hits': hits,
            'maximum_valuation': 1, 'inverse_sum_mod_q': sum(x['inverse'] for x in hits)%q}

def gap_checks(max_total: int = 18) -> int:
    count = 0
    # Every composition of every total <= max_total, hence every finite
    # ordered positive gap pattern in this range. No factorial congruence assumed.
    for total in range(2, max_total + 1):
        for mask in range(1, 1 << (total-1)):
            cuts = [0] + [i+1 for i in range(total-1) if mask >> i & 1] + [total]
            g = sorted(b-a for a,b in zip(cuts,cuts[1:]))
            r = len(g)
            m = r//2 + 1
            first = g[:m]
            b,a = min(zip(first, first[1:]), key=lambda pair: pair[1]-pair[0])
            assert a*r <= 2*total
            assert b*r <= 2*total
            assert (a-b)*((r*r)//4) <= total
            count += 1
    return count

def small_joint_checks() -> dict:
    cases = inequalities = 0
    for q in range(3, 200, 2):
        if not prime(q): continue
        fs=[1]*q; hs=[0]*q
        for n in range(1,q):
            fs[n]=fs[n-1]*n%q
            hs[n]=(hs[n-1]+pow(n,-1,q))%q
        R=[]
        for h in range(1,math.isqrt(q)+1):
            roots=0
            for x in range(q):
                f,df=1,0
                for j in range(1,h+1):
                    df=(df*(x+j)+f)%q
                    f=f*(x+j)%q
                roots += (f==1 and df==0)
            R.append(roots)
        for c in set(hs[n] for n in range(1,q) if fs[n]==1):
            ns=[n for n in range(1,q) if fs[n]==1 and hs[n]==c]
            for n,z in zip(ns,ns[1:]):
                h=z-n; f,df=1,0
                for j in range(1,h+1):
                    df=(df*(n+j)+f)%q; f=f*(n+j)%q
                assert f==1 and df==0
                cases+=1
            for K in range(1,len(R)+1):
                assert K*len(ns) <= K+q+K*sum(R[:K])
                inequalities+=1
    return {'prime_upper_bound_exclusive':200,'joint_gap_identities':cases,
            'joint_fibre_inequalities':inequalities,'implementation':'scalar Python, independent of NumPy recurrence scan'}

def main() -> None:
    ap=argparse.ArgumentParser(description=__doc__);ap.add_argument('--output',type=Path,required=True);args=ap.parse_args()
    rows=[cancellation(q) for q in (139,2593)]
    assert [x['n'] for x in rows[0]['all_hits']]==[69,122,137]
    assert [x['n'] for x in rows[1]['all_hits']]==[349,2243,2591]
    assert all(row['inverse_sum_mod_q']==0 for row in rows)
    out={'schema':'erdos68_local_arithmetic_checks_v1','evidence_class':'finite_exact_checks',
         'cancellation_examples':rows,'gap_pattern_checks':gap_checks(),
         'gap_total_maximum':18,'joint_fibre_checks':small_joint_checks(),
         'scope_warning':'The finite gap test checks only the selection bounds, not the unresolved nonvanishing under factorial congruences. No asymptotic conjecture is proved by these scans.',
         'implementation_sha256':hashlib.sha256(Path(__file__).read_bytes()).hexdigest()}
    args.output.parent.mkdir(parents=True,exist_ok=True);args.output.write_text(json.dumps(out,indent=2)+'\n');print(json.dumps(out,indent=2))
if __name__=='__main__': main()
