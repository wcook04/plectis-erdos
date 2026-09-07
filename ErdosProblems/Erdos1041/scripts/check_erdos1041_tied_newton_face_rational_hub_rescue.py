#!/usr/bin/env python3
"""Exact rational replay of the tied-face rational-hub rescue."""
from __future__ import annotations
import argparse, json, math
import sympy as sp

def main() -> int:
    ap=argparse.ArgumentParser(); ap.add_argument("--json",action="store_true"); a=ap.parse_args()
    I=sp.I; n=5; R=sp.Rational(3,2)
    h=-sp.Rational(3,5)+sp.Rational(9,10)*I
    u=sp.Rational(57,185)+sp.Rational(176,185)*I
    v=-sp.Rational(1431,1769)+sp.Rational(1040,1769)*I
    A={1:-sp.Rational(379,256),2:sp.Integer(3)}
    Q=lambda z: A[1]*z+A[2]*z**2-z**5
    def arm(w):
        d=R*w; out=[]
        for r in range(n+1):
            z=-h**(n-r)*d**r
            for m in A:
                z += A[m]*sum(sp.Rational(math.comb(m,k)*math.comb(n-m,r-k),math.comb(n,r))*h**(m-k)*d**k for k in range(max(0,r-(n-m)),min(m,r)+1))
            out.append(sp.factor(sp.re(sp.expand_complex(z))))
        return out
    def tail(w):
        out=[]
        for j in range(n+1):
            z=-R**n*sp.re(w**n)
            for m in A:
                k=n-m
                if j>=k:z += A[m]*sp.re(w**m)*R**m*sp.Rational(math.comb(j,k),math.comb(n,k))
            out.append(sp.factor(z))
        return out
    controls={"arm_u":arm(u),"arm_v":arm(v),"tail_u":tail(u),"tail_v":tail(v)}
    du=sp.factor(sp.re((R*u-h)*sp.conjugate(R*u-h)))
    dv=sp.factor(sp.re((R*v-h)*sp.conjugate(R*v-h)))
    gates={
      "u_unit":sp.re(u*sp.conjugate(u))==1,"v_unit":sp.re(v*sp.conjugate(v))==1,
      "u_negative_asymptotic_sector":sp.re(u**5)>0,"v_negative_asymptotic_sector":sp.re(v**5)>0,
      "hub_strictly_safe":sp.re(Q(h))<0,"all_controls_strictly_negative":all(x<0 for row in controls.values() for x in row),
      "distance_u_lt_R":du<R**2,"distance_v_lt_R":dv<R**2,
    }
    gates={k:bool(vv) for k,vv in gates.items()}; passed=all(gates.values())
    out={"schema":"erdos1041_tied_newton_face_rational_hub_rescue_v1","passed":passed,"gates":gates,
      "model":"Q(z)=-(379/256)z+3z^2-z^5","hub":str(h),"radius":str(R),"u":str(u),"v":str(v),
      "controls":{k:[str(x) for x in row] for k,row in controls.items()},"distance_squares":[str(du),str(dv)],
      "claim_boundary":"Exact rescue of one tied quintic model; not an all-degree selector or a proof of Erdos #1041."}
    print(json.dumps(out,indent=2,sort_keys=True) if a.json else out); return 0 if passed else 1
if __name__=="__main__": raise SystemExit(main())
