#!/usr/bin/env python3
"""Compact exact replay of the minimal quartic fixed-pair CE--GM no-go."""
from __future__ import annotations

import argparse
import json
import math

import sympy as sp


def bernstein_split_half(controls: list[sp.Rational]) -> tuple[list[sp.Rational], list[sp.Rational]]:
    rows = [controls]
    while len(rows[-1]) > 1:
        rows.append([(a+b)/2 for a, b in zip(rows[-1], rows[-1][1:])])
    degree = len(controls)-1
    return [rows[k][0] for k in range(degree+1)], [rows[degree-k][k] for k in range(degree+1)]


def main() -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument("--json", action="store_true")
    args = parser.parse_args()

    z = sp.symbols("z")
    t = sp.symbols("t", real=True)
    I = sp.I
    F = (z**4-(sp.Rational(1321,5000)+sp.Rational(33,125)*I)*z**2
         -(sp.Rational(33,12500)+sp.Rational(1183,12500)*I)*z
         -sp.Rational(16,25)-sp.Rational(9,50)*I)
    c1 = sp.Rational(11,25)+sp.Rational(1,5)*I
    c2 = -sp.Rational(7,20)-sp.Rational(1,10)*I
    cs = -sp.Rational(9,100)-sp.Rational(1,10)*I
    criticals = [c1,c2,cs]
    values = [sp.expand(F.subs(z,c)) for c in criticals]
    norms = [sp.factor(sp.re(sp.expand_complex(v*sp.conjugate(v)))) for v in values]
    T = sp.Rational(27,40)

    centres = [
        -sp.Rational(122,125)-sp.Rational(53,500)*I,
        -sp.Rational(1,200)-sp.Rational(213,250)*I,
        sp.Rational(493,500)+sp.Rational(163,1000)*I,
        -sp.Rational(3,500)+sp.Rational(159,200)*I,
    ]
    eps = sp.Rational(1,1000)

    def l1(w: sp.Expr) -> sp.Expr:
        w = sp.expand_complex(w)
        return abs(sp.re(w))+abs(sp.im(w))

    def linf(w: sp.Expr) -> sp.Expr:
        w = sp.expand_complex(w)
        return max(abs(sp.re(w)),abs(sp.im(w)))

    margins=[]
    for centre in centres:
        coeffs=[sp.factor(sp.diff(F,z,k).subs(z,centre)/math.factorial(k)) for k in range(5)]
        margins.append(sp.factor(linf(coeffs[1])*eps-l1(coeffs[0])-
                                 sum(l1(coeffs[k])*eps**k for k in range(2,5))))

    centre_m=-sp.Rational(11,10)-sp.Rational(1,4)*I
    circle_r=sp.Rational(3,4)
    circle_z=centre_m+circle_r*(1+I*t)/(1-I*t)
    circle_value=sp.cancel(F.subs(z,circle_z))
    circle_sq=sp.re(sp.expand_complex(circle_value*sp.conjugate(circle_value)))
    cleared=sp.factor((1+t**2)**4*(circle_sq-T**2))
    P=sp.Poly(sp.cancel(cleared*10**11),t)
    expected_desc=[
        10874172360773,-10022578403256,11403058106654,-4349728276488,
        2240976658314,-335445488208,129719679758,-24307214976,1427842325,
    ]
    power_asc=list(reversed(expected_desc))
    controls=[sp.Rational(power_asc[k],math.comb(8,k)) for k in range(9)]
    left_half,cell4=bernstein_split_half(controls)
    left_quarter,cell3=bernstein_split_half(left_half)
    cell1,cell2=bernstein_split_half(left_quarter)
    cells=[cell1,cell2,cell3,cell4]
    minima=[min(cell) for cell in cells]

    def norm_sq(w: sp.Expr) -> sp.Expr:
        return sp.factor(sp.re(sp.expand_complex(w*sp.conjugate(w))))

    centre_dist=[norm_sq(q-cs) for q in centres]
    barrier_inner=(circle_r-eps)**2-norm_sq(centres[0]-centre_m)
    barrier_outer=[norm_sq(q-centre_m)-(circle_r+eps)**2 for q in centres[1:]]
    pairwise=[norm_sq(centres[i]-centres[j])-(2*eps)**2
              for i in range(4) for j in range(i+1,4)]

    expected_norms=[
        sp.Rational(1108755728681,2441406250000),
        sp.Rational(7315188509201,16000000000000),
        sp.Rational(4459277974823361,10000000000000000),
    ]
    expected_margins=[
        sp.Rational(73095707,200000000000),sp.Rational(145462253,62500000000),
        sp.Rational(707606309,500000000000),sp.Rational(718138961,500000000000),
    ]
    expected_minima=[
        sp.Rational(14036359191955,458752),sp.Rational(69526329128125,524288),
        sp.Rational(3649093538125,2048),sp.Rational(77478869257,2),
    ]

    gates={
        "derivative_factorization": sp.expand(sp.diff(F,z)-4*(z-c1)*(z-c2)*(z-cs))==0,
        "critical_values_exact": norms==expected_norms,
        "least_critical_unique": norms[2]<norms[0] and norms[2]<norms[1],
        "gcrit_below_threshold": T**6>sp.prod(norms),
        "threshold_below_merge": T**2<norms[1],
        "rouche_margins_exact_positive": margins==expected_margins and all(x>0 for x in margins),
        "root_discs_pairwise_disjoint": all(x>0 for x in pairwise),
        "nearest_pair_intervals": (
            centre_dist[1]<sp.Rational(757,1000)**2 and
            centre_dist[0]<sp.Rational(887,1000)**2 and
            centre_dist[3]>sp.Rational(898,1000)**2 and
            centre_dist[2]>sp.Rational(1107,1000)**2),
        "barrier_separates_root_discs": barrier_inner>0 and all(x>0 for x in barrier_outer),
        "circle_polynomial_exact": P.all_coeffs()==expected_desc,
        "circle_negative_halfline_signs": all(((-1)**k)*power_asc[k]>0 for k in range(9)),
        "circle_bernstein_cells_exact_positive": minima==expected_minima and all(x>0 for x in minima),
        "scaled_roots_strictly_in_unit_disc": max(abs(sp.re(q))+abs(sp.im(q)) for q in centres)+eps<2,
    }
    gates={key:bool(value) for key,value in gates.items()}
    passed=all(gates.values())
    output={
        "schema":"erdos1041_cegm_quartic_fixed_pair_no_go_v1",
        "passed":passed,
        "gates":gates,
        "critical_value_squares":[str(x) for x in norms],
        "gcrit_power_margin":str(sp.factor(T**6-sp.prod(norms))),
        "merge_power_margin":str(sp.factor(norms[1]-T**2)),
        "rouche_margins":[str(x) for x in margins],
        "circle_bernstein_cell_minima":[str(x) for x in minima],
        "claim_boundary":(
            "Exact minimal-degree refutation of the fixed least-critical/two-nearest-root CE--GM selector. "
            "Free-pair FP-GM and unrestricted Erdős #1041 remain open."
        ),
    }
    print(json.dumps(output,indent=2,sort_keys=True) if args.json else output)
    return 0 if passed else 1


if __name__=="__main__":
    raise SystemExit(main())
