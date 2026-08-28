#!/usr/bin/env python3
"""Dependency-free deterministic falsification for open WGP3 and DGP3."""
import json
import math
import random

def rho2(q,r,c): return (q*q-2*q*r*c+r*r)/(1-2*q*r*c+q*q*r*r)
def H(q,r,c): return (1-r*r)*(q*(1+r*r)-r*c*(1+q*q))/((q*q-2*q*r*c+r*r)*(1-2*q*r*c+q*q*r*r))

def gaps(r,q,a):
    p=math.prod(r); T=(q**3-p)/(1-p*q**3); logs=[]
    for j in range(3):
        square=math.prod(rho2(q,r[k],math.cos(a[j]-a[k])) for k in range(3))
        logs.append(.5*math.log(square))
    log_gap=sum(r[j]*logs[j] for j in range(3))-sum(r)*math.log(T)
    lhs=sum(r[j]*H(q,r[k],math.cos(a[j]-a[k])) for j in range(3) for k in range(3))
    rhs=sum(r)*(3*q*q/(q**3-p)+3*p*q*q/(1-p*q**3))
    return log_gap,lhs-rhs

def main():
    rows=[]
    for seed in (7,1041):
        rng=random.Random(seed); hi=-math.inf; lo=math.inf
        tests=[([.2,.2,.2],.6,[0,2*math.pi/3,-2*math.pi/3])]
        for _ in range(100000):
            r=[math.exp(rng.uniform(-9,-.002)) for _ in range(3)]
            mr=max(r); q=mr+(1-mr)*rng.random()
            tests.append((r,q,[0,rng.uniform(-math.pi,math.pi),rng.uniform(-math.pi,math.pi)]))
        for r,q,angles in tests:
            lg,dg=gaps(r,q,angles); hi=max(hi,lg); lo=min(lo,dg)
        rows.append({"seed":seed,"sample_count":len(tests),"weighted_log_gap_maximum":hi,"weighted_derivative_gap_minimum":lo})
    ok=all(x["weighted_log_gap_maximum"]<1e-9 and x["weighted_derivative_gap_minimum"]>-1e-9 for x in rows)
    print(json.dumps({"schema":"erdos1041-public-gp3-falsification/1","runs":rows,"finite_search_consistent_with_open_conjecture":ok,"claim_boundary":"Finite sampling only; GP3, DGP3, the selector lemma, and unrestricted Erdos 1041 remain unproved."},indent=2))
    return 0 if ok else 1

if __name__=="__main__": raise SystemExit(main())
