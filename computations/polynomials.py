# SPDX-FileCopyrightText: 2026 Will Cook
# SPDX-License-Identifier: Apache-2.0
"""Exact polynomial definitions. Importing this module performs no experiments."""
from functools import lru_cache
from math import inf
import sympy as sp
from sympy.polys.matrices import DomainMatrix
p = sp.Symbol('p')
def index(n):
    if not isinstance(n,(int,sp.Integer)) or isinstance(n,bool) or n<0: raise ValueError('non-negative integer required')
@lru_cache(None)
def gaussian(n,k):
    index(n)
    if not isinstance(k,(int,sp.Integer)) or isinstance(k,bool): raise ValueError('integer lower index required')
    if k<0 or k>n: return sp.Poly(0,p,domain=sp.QQ)
    if k==0 or k==n: return sp.Poly(1,p,domain=sp.QQ)
    return gaussian(n-1,k)+sp.Poly(p**(n-k),p,domain=sp.QQ)*gaussian(n-1,k-1)
@lru_cache(None)
def diagonal(m):
    index(m)
    return sum(((-1)**(m+k)*sp.Poly(p**(k*(k+1)//2),p,domain=sp.QQ)*gaussian(m,k)*gaussian(m+k,k) for k in range(m+1)),sp.Poly(0,p,domain=sp.QQ))
@lru_cache(None)
def positive_diagonal(m):
    index(m); total=sp.Poly(0,p,domain=sp.QQ)
    for k in range(m+1):
        tail=sp.Poly(1,p,domain=sp.QQ)
        for j in range(m-k+1,m+1): tail*=sp.Poly(p**j-1,p,domain=sp.QQ)
        total+=gaussian(m,k)*gaussian(m+k,k)*sp.Poly(p**((m-k)*(m-k+1)//2),p,domain=sp.QQ)*tail
    return total
@lru_cache(None)
def moments(m):
    index(m); f=sp.Poly(1,p,domain=sp.QQ)
    for j in range(1,m+1): f*=sp.Poly.from_list([1]*j,p,domain=sp.QQ)
    return f**3*diagonal(m)
@lru_cache(None)
def alpha(m):
    index(m)
    return sp.Poly(p**(m+1)*(p-1)**(3*m),p,domain=sp.QQ)*moments(m)
@lru_cache(None)
def beta(m):
    a=alpha(m); d=a.degree(); cs=list(reversed(a.all_coeffs())); tau=[0]*(d+1)
    for j in range(1,d+1):
        for k in range(j,d+1,j): tau[k]+=1
    b=[sum(cs[i]*tau[i-r] for i in range(r+1,d+1)) for r in range(d)]
    b[0]-=1
    return sp.Poly.from_list(list(reversed(b)),p,domain=sp.QQ)
def exact_det(matrix):
    dm=DomainMatrix.from_Matrix(matrix)
    return dm.domain.to_sympy(dm.det())
@lru_cache(None)
def phi(d):
    index(d)
    if d<1: raise ValueError('positive cyclotomic index required')
    return sp.Poly(sp.cyclotomic_poly(d,p),p,domain=sp.QQ)
def valuation(poly,d):
    if poly.is_zero: return inf
    n=0
    while True:
        quotient,remainder=poly.div(phi(d))
        if not remainder.is_zero: return n
        n+=1;poly=quotient
@lru_cache(None)
def entry_residue(m,d):
    a,b=alpha(m),beta(m); v=min(valuation(a,d),valuation(b,d)); divisor=phi(d)**v
    return v,a.exquo(divisor).rem(phi(d)),b.exquo(divisor).rem(phi(d))
