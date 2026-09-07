#!/usr/bin/env python3
"""Optional exact symbolic regression (SymPy); no numerical sampling."""
import json

if not __debug__:
    raise RuntimeError("Run without -O: exact assertions must remain enabled")
import sympy as s
x,y,b,p,h,q = s.symbols('x y b p h q')
defect = (x*x+y*y)*((x+b)**2+y*y)-((1+b*x)**2+(b*y)**2)
assert s.expand(defect-(x*x+y*y-1)*(x*x+y*y+1+2*b*x)) == 0
H=b*(p*p-1)/2-q
residual=s.expand(H*(H+b)-p*p*(1+b*H))
assert s.expand(residual-(q*q-p*p-b*b*(p*p-1)**2/4)) == 0
A=h*(h+b);D=1+b*h
assert s.expand(D*s.diff(A,h)-b*A-(b*h*h+2*h+b)) == 0
print(json.dumps({'status':'pass','identities':['circle norm defect','quadratic inverse discriminant','critical Wronskian'], 'evidence':'exact symbolic polynomial identities, not Lean compilation'}))
