#!/usr/bin/env python3
# SPDX-FileCopyrightText: 2026 Will Cook
# SPDX-License-Identifier: Apache-2.0
"""Exact rational-interval checks for the limiting critical-hub obstruction.

Only Python's standard library is required. This certifies the strict algebraic
signs in research/critical_hubs.tex, not the analytic implicit-function theorem
or a numerical epsilon threshold for the asymptotic proposition.
"""
from fractions import Fraction as Q
from dataclasses import dataclass
import json
from pathlib import Path

@dataclass(frozen=True)
class I:
    lo: Q
    hi: Q
    def __post_init__(self):
        if self.lo > self.hi: raise ValueError('Reversed interval')
    @staticmethod
    def point(x): return I(Q(x), Q(x))
    def __add__(self, y):
        y = y if isinstance(y,I) else I.point(y)
        return I(self.lo+y.lo,self.hi+y.hi)
    __radd__=__add__
    def __neg__(self): return I(-self.hi,-self.lo)
    def __sub__(self,y): return self+-as_i(y)
    def __rsub__(self,y): return as_i(y)+-self
    def __mul__(self,y):
        y=as_i(y); p=[a*b for a in (self.lo,self.hi) for b in (y.lo,y.hi)]
        return I(min(p),max(p))
    __rmul__=__mul__
    def __truediv__(self,y):
        y=as_i(y)
        if y.lo <= 0 <= y.hi: raise ZeroDivisionError('Interval contains zero')
        return self*I(1/y.hi,1/y.lo)
    def __pow__(self,n):
        if n<0: raise ValueError('Only nonnegative integer powers')
        out=I.point(1)
        for _ in range(n): out=out*self
        return out

def as_i(x): return x if isinstance(x,I) else I.point(x)
def root(q, n, steps=180):
    q=Q(q)
    if q<0 or n<1: raise ValueError('Positive radicand and degree required')
    lo,hi=Q(0),max(Q(1),q)
    for _ in range(steps):
        m=(lo+hi)/2
        if m**n<=q: lo=m
        else: hi=m
    assert lo**n<=q<=hi**n
    return I(lo,hi)
def sqrt_i(x):
    x=as_i(x)
    if x.lo<0: raise ValueError('Negative square-root interval')
    return I(root(x.lo,2).lo,root(x.hi,2).hi)

def cadd(x,y): return (x[0]+y[0], x[1]+y[1])
def cmul(x,y): return (x[0]*y[0]-x[1]*y[1],x[0]*y[1]+x[1]*y[0])
def cpow(x,n):
    out=(I.point(1),I.point(0))
    for _ in range(n): out=cmul(out,x)
    return out

def main():
    s5=root(5,2); s3=root(3,2); alpha=root(Q(2,5),3)
    c1=(s5-1)/4; t1=sqrt_i(10+2*s5)/4
    c2=-(s5+1)/4; t2=sqrt_i(10-2*s5)/4
    roots=[(I.point(1),I.point(0)),(c1,t1),(c2,t2),(c2,-t2),(c1,-t1)]
    hub=(-alpha/2, alpha*s3/2)
    rows=[]
    for j,s in [(0,Q(2)),(1,Q(7,10)),(3,Q(2)),(4,Q(3,5))]:
        z=cadd(hub,(s*roots[j][0],s*roots[j][1]))
        re=cpow(z,5)[0]-cpow(z,2)[0]
        assert re.hi<0, (j,re)
        coarse={0:(Q(-7025,1000),Q(-7024,1000)),1:(Q(-462,1000),Q(-460,1000)),3:(Q(-12773,1000),Q(-12770,1000)),4:(Q(-30,1000),Q(-28,1000))}[j]
        assert coarse[0]<re.lo<=re.hi<coarse[1]
        rows.append({'root_index':j,'spoke_scale':str(s),'lower':str(re.lo),'upper':str(re.hi),'decimal_interval':[float(re.lo),float(re.hi)],'strictly_negative':True})
    assert c1.lo>Q(1,4)
    report={'method':'rational interval arithmetic; 180 bisections per radical','assertions_passed':True,'outer_complex_hub':rows,'central_length_coefficient':{'lower':str(c1.lo),'upper':str(c1.hi)},'scope':'Algebraic limiting signs only. No explicit valid epsilon interval or Lean verification is asserted.'}
    path=Path(__file__).with_name('certified_hub_limits.json')
    path.write_text(json.dumps(report,indent=2)+'\n')
    print(json.dumps({'assertions_passed':True,'output':path.name,'limits':[x['decimal_interval'] for x in rows]},indent=2))
if __name__=='__main__': main()
