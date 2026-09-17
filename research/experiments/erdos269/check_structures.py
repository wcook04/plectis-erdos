#!/usr/bin/env python3
# SPDX-FileCopyrightText: 2026 Will Cook
# SPDX-License-Identifier: Apache-2.0
"""Exact finite checks for the second Erdős 269 outreach review.
Python 3.10+; standard library only. No network access, logarithms or floating
point endpoint decisions. This is not an irrationality test or a Lean build.
"""
from __future__ import annotations
from bisect import bisect_right
from fractions import Fraction
from pathlib import Path
import argparse, json, math


def powers(p: int, upper: int) -> list[int]:
    ans, x = [], 1
    while x <= upper:
        ans.append(x)
        x *= p
    return ans


def literal_data(n: int) -> tuple[list[int], list[int], list[int], list[int]]:
    """P_a=H(2^a), 0<=a<=n; m_a for 0<=a<n, including m_0=1."""
    if n < 1:
        raise ValueError('n must be positive')
    endpoint = 1 << n
    p3, p5 = powers(3, endpoint), powers(5, endpoint)
    z3 = [bisect_right(p3, 1 << a)-1 for a in range(n+1)]
    z5 = [bisect_right(p5, 1 << a)-1 for a in range(n+1)]
    P = [(1 << a)*p3[z3[a]]*p5[z5[a]] for a in range(n+1)]
    m = [0]*n
    # Unique factorisation means that every point is counted once.
    for y3 in p3:
        for y5 in p5:
            value = y3*y5
            if value >= endpoint:
                break
            while value < endpoint:
                a = value.bit_length()-1
                h = (1 << a)*p3[bisect_right(p3,value)-1]*p5[bisect_right(p5,value)-1]
                q, rem = divmod(P[a+1], 2*h)
                assert rem == 0 and q > 0
                m[a] += q
                value *= 2
    assert m[0] == 1 and all(x > 0 for x in m)
    assert all(P[a+1]//P[a] in (2,6,10,30) for a in range(n))
    return P,m,z3,z5


def rank(A: list[list[int]]) -> int:
    mat = [[Fraction(x) for x in row] for row in A]
    if not mat:
        return 0
    nrow,ncol,pivot = len(mat),len(mat[0]),0
    for j in range(ncol):
        k = next((k for k in range(pivot,nrow) if mat[k][j]),None)
        if k is None:
            continue
        mat[pivot],mat[k] = mat[k],mat[pivot]
        fac = mat[pivot][j]
        mat[pivot] = [x/fac for x in mat[pivot]]
        for k in range(pivot+1,nrow):
            fac = mat[k][j]
            if fac:
                mat[k] = [x-fac*y for x,y in zip(mat[k],mat[pivot])]
        pivot += 1
        if pivot == nrow:
            break
    return pivot


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument('--n', type=int, default=192)
    parser.add_argument('--output',type=Path,default=Path('exact_checks.json'))
    args = parser.parse_args()
    if args.n < 150:
        parser.error('--n must be at least 150 for the declared fixtures')
    P,m,z3,z5 = literal_data(args.n)
    b = [P[a+1]//P[a] for a in range(args.n)]
    alpha = [Fraction(0)]
    for a in range(args.n):
        alpha.append(alpha[-1] + Fraction(m[a],P[a+1]))
    allowed = {Fraction(1),Fraction(1,3),Fraction(1,5),Fraction(1,15)}
    gamma_tests = 0
    for t in range(65):
        for a in range(args.n-t):
            gamma = Fraction(P[t]*P[a+1],P[a+t+1])
            assert gamma in allowed
            gamma_tests += 1
    cs = (1,-3,3,-1)
    tests = []
    for r in (1,2,3,5,8,13,21,32):
        L = min(64,args.n-3*r)
        D = []
        for a in range(L):
            d = 15*sum((c*Fraction(P[j*r]*P[a+1],P[a+j*r+1])*m[a+j*r]
                        for j,c in enumerate(cs)),Fraction(0))
            assert d.denominator == 1
            D.append(d.numerator)
        lhs = sum((Fraction(D[a],P[a+1]) for a in range(L)),Fraction(0))
        rhs = 15*sum((c*P[j*r]*(alpha[L+j*r]-alpha[j*r])
                      for j,c in enumerate(cs)),Fraction(0))
        assert lhs == rhs
        tests.append({'r':r,'a_start':0,'a_count':L,'nonzero_count':sum(d!=0 for d in D),
                      'first_values':D[:8], 'finite_shift_identity_exact':True})
    def basis(a: int) -> list[int]:
        x,y=z3[a],z5[a]
        return [1,a,x,y,a*a,a*x,a*y,x*x,x*y,y*y]
    poly = []
    for start in (0,10,50,100):
        rows = [[b[a]*x-y for x,y in zip(basis(a),basis(a+1))]
                for a in range(start,start+31)]
        augmented = [row+[m[a]] for row,a in zip(rows,range(start,start+31))]
        poly.append({'start':start,'end_inclusive':start+30,
                     'coefficient_rank':rank(rows),'augmented_rank':rank(augmented)})
    shadow_tests=[]
    for N in (1,5,20,64):
        # A literal prefix followed by b_a-1 has total alpha_N+1/P_N.
        L=min(args.n,N+40)
        spliced=alpha[N]+sum((Fraction(b[a]-1,P[a+1]) for a in range(N,L)),Fraction(0))
        assert spliced+Fraction(1,P[L])==alpha[N]+Fraction(1,P[N])
        shadow_tests.append({'splice_index':N,'telescoping_identity_exact':True})
    result={'status':'exact finite checks only; no infinite conclusion', 'n':args.n,
            'm_prefix':m[:20],'b_prefix':b[:20], 'gamma_membership_checks':gamma_tests,
            'gamma_values':['1','1/3','1/5','1/15'],
            'third_difference_tests':tests,'quadratic_carry_fit_tests':poly,
            'shadow_tests':shadow_tests,
            'limitations':['Finite failures do not exclude an eventual polynomial beyond every tested interval.',
                           'Dense tested defects do not exclude all fixed operators or all unbounded shifts.',
                           'No Expanding Gaps or Polynomial Variation hypothesis is verified for the infinite source.',
                           'All calculations use the literal repeated series, with its multiplicities and half-height normalisation.']}
    args.output.write_text(json.dumps(result,indent=2)+'\n')
    print(json.dumps(result,indent=2))

if __name__ == '__main__':
    main()
