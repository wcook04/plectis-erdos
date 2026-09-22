#!/usr/bin/env python3
# SPDX-FileCopyrightText: 2026 Will Cook
# SPDX-License-Identifier: Apache-2.0
"""Rational enclosures for the stated irrationality-exponent bound.
No floating-point mathematical operations; run with --output new_file.json.
The integral comparison and alternating-series bounds are described in README.
"""
from __future__ import annotations
import argparse, json
from fractions import Fraction as F
from pathlib import Path


def atan_bounds(x: F, n: int) -> tuple[F, F]:
    value = sum(((-1)**k*x**(2*k+1)/F(2*k+1) for k in range(n)), F(0))
    other = value + (-1)**n*x**(2*n+1)/F(2*n+1)
    return min(value, other), max(value, other)


def twice_atanh_bounds(x: F, n: int) -> tuple[F,F]:
    if not 0 < x < 1 or n < 1:
        raise ValueError('Require 0<x<1 and n>=1')
    low = 2*sum((x**(2*k+1)/F(2*k+1) for k in range(n)), F(0))
    return low, low + 2*x**(2*n+1)/(F(2*n+1)*(1-x*x))


def directed(x: F, places: int, upper: bool) -> str:
    scale=10**places
    a=x.numerator*scale
    b=x.denominator
    k=-((-a)//b) if upper else a//b
    sign='-' if k<0 else ''
    k=abs(k)
    return f'{sign}{k//scale}.{k%scale:0{places}d}'


def compute() -> dict:
    pairs=[(F(1,14),F(1,12)),(F(1,7),F(1,6)),(F(3,14),F(1,4)),
        (F(2,7),F(1,3)),(F(5,14),F(2,5)),(F(3,7),F(7,15)),
        (F(1,2),F(8,15)),(F(4,7),F(3,5)),(F(9,14),F(2,3)),
        (F(5,7),F(11,15)),(F(11,14),F(4,5)),(F(6,7),F(13,15)),
        (F(13,14),F(14,15))]
    M=256; jl=ju=F(0)
    for u,v in pairs:
        main=sum((1/(k+u)**2-1/(k+v)**2 for k in range(M)),F(0))
        integral=1/(M+u)-1/(M+v)
        jl += main+integral
        ju += main+integral+1/(M+u)**2-1/(M+v)**2
    al,au=atan_bounds(F(1,5),28);bl,bu=atan_bounds(F(1,239),10)
    pl,pu=16*al-4*bu,16*au-4*bl
    c0l,c0u=266-3*(225-jl)/pl**2,266-3*(225-ju)/pu**2
    tl,tu=c0l/F(1091,2),c0u/F(1091,2)
    l2,u2=twice_atanh_bounds(F(1,3),64)
    lr,ur=twice_atanh_bounds(F(1,63),24)
    l31,u31=5*l2-ur,5*u2-lr
    rl,ru=2*l2/u31,2*u2/l31
    # f(r,t)=(1-r)/(t-r) increases with r and decreases with t when r<t<1.
    ml,mu=(1-rl)/(tu-rl),(1-ru)/(tl-ru)
    if not (0<jl<ju<225 and 0<rl<ru<tl<tu<1):
        raise ArithmeticError('Unexpected interval ordering')
    checks={'theta_star_above_0.40568':tl>F(40568,100000),
      'log_ratio_below_0.4036982':ru<F(4036982,10000000),
      'exponent_bound_below_301':mu<301,
      '31_squared_below_4_to_5':31**2<4**5,
      '4_to_200_below_31_to_81':4**200<31**81}
    if not all(checks.values()):raise ArithmeticError('Failed exact inequality')
    values={'J':(jl,ju),'pi':(pl,pu),'C0':(c0l,c0u),'theta_star':(tl,tu),
        'log4_over_log31':(rl,ru),'irrationality_exponent_bound':(ml,mu)}
    return {'schema':'rational_interval_certificate_v1','trigamma_terms_per_interval':M,
      'method':'positive decreasing tail integral comparison; Machin formula; atanh log series',
      'values':{k:{'lower':str(v[0]),'upper':str(v[1]),
      'decimal_lower_outward':directed(v[0],14,False),
      'decimal_upper_outward':directed(v[1],14,True)}for k,v in values.items()},
      'exact_checks':checks,'floating_point_used':False,'lean_checked':False}


def main() -> None:
    parser=argparse.ArgumentParser();parser.add_argument('--output',required=True,type=Path)
    args=parser.parse_args()
    if args.output.exists():raise FileExistsError(args.output)
    args.output.parent.mkdir(parents=True,exist_ok=True)
    result=compute();args.output.write_text(json.dumps(result,indent=2)+'\n')
    for key,value in result['values'].items():
        print(key, value['decimal_lower_outward'],value['decimal_upper_outward'])
if __name__=='__main__':main()
