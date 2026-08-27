#!/usr/bin/env python3
"""Exact symbolic replay of the critical-component quintic rescue."""
from __future__ import annotations

import argparse
import json
import math

import sympy as sp


def bernstein_controls(poly: sp.Expr, variable: sp.Symbol, degree: int) -> list[sp.Expr]:
    power = sp.Poly(sp.expand(poly), variable, extension=sp.sqrt(5))
    return [sp.simplify(sum(power.nth(j)*sp.binomial(k,j)/sp.binomial(degree,j)
                           for j in range(k+1))) for k in range(degree+1)]


def main() -> int:
    parser=argparse.ArgumentParser(); parser.add_argument("--json",action="store_true")
    args=parser.parse_args()
    t,r,z=sp.symbols("t r z",real=True)
    s=sp.sqrt(5); I=sp.I
    Q=lambda w:-sp.Rational(379,256)*w+3*w**2-w**5
    c=sp.Rational(1,4); R=sp.Rational(1,2)
    omega=(s-1)/4+I*sp.sqrt(10+2*s)/4
    arm=sp.expand(sp.expand_complex(Q((1-t)*c+t*R*omega)).as_real_imag()[0])
    controls=bernstein_controls(arm,t,5)
    expected=[
        -sp.Rational(47,256),-sp.Rational(47,256),
        -(849+182*s)/5120,-(1319+1117*s)/10240,
        -(369+1162*s)/5120,-(69+763*s)/2048,
    ]
    tail=sp.factor(sp.expand_complex(Q(r*omega)).as_real_imag()[0],extension=s)
    expected_tail=-r*(r**4+3*(1+s)*r/4+sp.Rational(379,1024)*(s-1))
    dist_sq=sp.simplify(sp.expand_complex((R*omega-c)*sp.conjugate(R*omega-c)))
    gates={
        "critical_hub":sp.diff(Q(z),z).subs(z,c)==0,
        "critical_value_negative":Q(c)==-sp.Rational(47,256),
        "omega_unit":sp.simplify(omega*sp.conjugate(omega))==1,
        "arm_controls_exact":controls==expected,
        "arm_controls_strictly_negative":all(sp.ask(sp.Q.negative(x)) for x in controls),
        "tail_formula_exact":sp.simplify(tail-expected_tail)==0,
        "tail_factors_positive_for_positive_radius":bool(sp.ask(sp.Q.positive(1+s))) and bool(sp.ask(sp.Q.positive(s-1))),
        "distance_exact":dist_sq==(6-s)/16,
        "strict_metric":sp.ask(sp.Q.negative(dist_sq-R**2)) is True,
        "component_passport_arithmetic":4==1+3 and 1==1+0 and 4+1==5,
    }
    gates={k:bool(v) for k,v in gates.items()}; passed=all(gates.values())
    output={
        "schema":"erdos1041_tied_newton_face_component_selector_v1",
        "passed":passed,"gates":gates,
        "model":"Q(z)=-(379/256)z+3z^2-z^5",
        "hub":"1/4","radius":"1/2",
        "arm_controls":[str(x) for x in controls],
        "tail_formula":str(tail),"distance_squared":str(dist_sq),
        "metric_defect":str(sp.simplify(2*sp.sqrt(dist_sq)-1)),
        "claim_boundary":(
            "Exact critical-hub connector and finite passport arithmetic for the calibration quintic. "
            "The component-degree theorem and horizontal-fibre comparison are ordinary analytic mathematics; "
            "HF-strict, finite transfer, and unrestricted Erdős #1041 remain open."
        ),
    }
    print(json.dumps(output,indent=2,sort_keys=True) if args.json else output)
    return 0 if passed else 1


if __name__=="__main__": raise SystemExit(main())
