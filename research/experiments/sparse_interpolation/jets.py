#!/usr/bin/env python3
# SPDX-FileCopyrightText: 2026 Will Cook
# SPDX-License-Identifier: Apache-2.0
"""Exact checks for the factorial-jet proof; not a proof of its limits.

Uses only the standard library. Run from any working directory. The paper
proves the infinite-dimensional coding, measure and interior statements.
"""
from fractions import Fraction as Q
from math import comb, factorial
import argparse
import hashlib
import json
from pathlib import Path


def multiply_carry(b, k):
    """EGF coefficients of (z-1)^k sum b_n z^n/n!."""
    out = [0] * (len(b) + k)
    for m, digit in enumerate(b):
        for j in range(k + 1):
            n = m + j
            out[n] += (-1)**(k-j) * comb(k, j) * factorial(n)//factorial(m) * digit
    return out


def jet(a, d):
    return [sum((Q(a[n], factorial(n-r)) for n in range(r, len(a))), Q())
            for r in range(d)]


def shifted_jet(a, d, n):
    """Taylor coefficients of z^(-n) A(z) at 1, for support >= n."""
    assert all(v == 0 for v in a[:n])
    return [sum((Q(a[m] * comb(m-n, r), factorial(m))
                 for m in range(n, len(a)) if m-n >= r), Q())
            for r in range(d)]


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--output', type=Path,
                        help='Write a reproducible finite-check receipt with current source hashes.')
    args = parser.parse_args()
    checks = 0
    b = [(-1)**n * (n*n+3) for n in range(18)]
    for k in range(8):
        a = multiply_carry(b, k)
        actual = jet(a, 9)
        base = jet(b, 9)
        expected = [Q() if r < k else factorial(r)//factorial(r-k)*base[r-k]
                    for r in range(9)]
        assert actual == expected
        checks += 1

    # The endpoint terms are essential: truncated carries do not preserve value.
    for N in range(16):
        a = [(n+1)*b[n]-b[n+1] for n in range(N+1)]
        assert sum((Q(a[n], factorial(n+1)) for n in range(N+1)), Q()) == (
            b[0] - Q(b[N+1], factorial(N+1)))
        assert sum((Q((n+1)*a[n], factorial(n+1)) for n in range(N+1)), Q()) == (
            sum((Q(b[n], factorial(n)) for n in range(N+1)), Q())
            - Q((N+1)*b[N+1], factorial(N+1)))
        checks += 2

    # Recover integer coefficients in the falling-factorial basis of P_N.
    for d in range(1, 9):
        for N in (d, 2*d+7, 100):
            def p(n):
                v = 1
                for j in range(1, d):
                    v *= n-N-j
                return v
            coeff = []
            for r in range(d):
                difference = sum((-1)**(r-t)*comb(r,t)*p(t) for t in range(r+1))
                assert difference % factorial(r) == 0
                coeff.append(difference//factorial(r))
            for n in range(N+d+8):
                assert p(n) == sum(coeff[r]*factorial(n)//factorial(n-r)
                                   for r in range(min(n,d-1)+1))
            assert all(p(N+j) == 0 for j in range(1,d))
            assert p(N+d) == factorial(d-1)
            checks += N+d+11

    # Independent polynomial and Taylor-coordinate checks of the coding map.
    for d in range(1, 8):
        n = d+5
        codes = [[0]*n+[k+1, 2*k-1, 3-k] for k in range(d)]
        pieces = [multiply_carry(code,k) for k,code in enumerate(codes)]
        a = [sum(piece[m] if m < len(piece) else 0 for piece in pieces)
             for m in range(max(map(len,pieces)))]
        direct = shifted_jet(a,d,n)
        formula = []
        for r in range(d):
            formula.append(sum((Q(codes[k][m]*comb(m-n,r-k),factorial(m))
                                for k in range(r+1)
                                for m in range(n,len(codes[k])) if m-n >= r-k), Q()))
        assert direct == formula
        # Multiply the ordinary Taylor jet by the binomial expansion of z^-n.
        ordinary = jet(a,d)
        transformed = [sum(((-1)**j * comb(n+j-1,j) * ordinary[r-j]/factorial(r-j)
                            for j in range(r+1)), Q()) for r in range(d)]
        assert transformed == direct
        checks += 2

    # Uniform tail constant: sum 2^t/(t-1)! < 18. Certify the infinite
    # remainder by a geometric bound on its successive rational terms.
    terms = [Q(2**t, factorial(t-1)) for t in range(1,21)]
    next_term = Q(2**21, factorial(20))
    assert sum(terms,Q()) + next_term/(1-Q(2,21)) < 18
    checks += 1

    # The quotient has two independent coefficient formulas: a signed
    # prefix at zero and an unsigned complementary tail at one. Test every
    # basis vector, including beyond its support, to catch signs/endpoints.
    for d in range(1, 9):
        for support in range(12):
            basis = [0] * support + [(-1)**support * (support+1)]
            g = multiply_carry(basis, d)
            assert jet(g, d) == [0] * d
            checks += 1
            for n in range(len(g)+2):
                prefix = (-1)**d * sum(
                    (Q(comb(n-k+d-1, d-1)*factorial(n)*g[k], factorial(k))
                     for k in range(min(n+1, len(g)))), Q())
                tail = sum(
                    (Q(comb(j-1, d-1)*factorial(n)*g[n+j], factorial(n+j))
                     for j in range(d, len(g)-n)), Q())
                expected = basis[n] if n < len(basis) else 0
                assert prefix == tail == expected
                checks += 1

    # The entropy allocation must include fractional and saturated cases.
    for d in range(1, 9):
        for numerator in range(1, 55):
            c = Q(numerator, 5)
            exponents = [min(Q(1), c-k) for k in range(d) if k < c]
            assert sum(exponents, Q()) == min(c, d)
            checks += 1
    result = {"status":"passed", "exact_checks":checks,
        "covers":["all tested carry powers and derivative orders",
                  "finite carry endpoint terms", "integer annihilators",
                  "moving Taylor coordinates", "infinite tail majorant",
                  "quotient prefix and complementary tail identities",
                  "fractional and saturated entropy allocations"],
        "boundary":"finite algebra and one uniform tail certificate; the general theorem is an ordinary proof"}
    if args.output:
        root = Path(__file__).resolve().parents[3]
        sources = [
            'paper/synthesis/optimal-sparse-perturbations.tex',
            'paper/synthesis/optimal-sparse-perturbations.pdf',
            'lean/ErdosProblems/Synthesis/FactorialJet.lean',
            'research/experiments/sparse_interpolation/jets.py',
        ]
        result.update(
            schema='factorial-jet-validation/2',
            ordinary_theorems=['capacity:thm:jets', 'capacity:thm:rational-jets'],
            proof_boundary='The complete dimension, interior, nullity and rational-derivative rigidity theorems have ordinary proofs. This command checks finite identities and a uniform tail majorant; it does not invoke Lean or verify the complete theorems.',
            sources={name: 'sha256:' + hashlib.sha256((root / name).read_bytes()).hexdigest()
                     for name in sources},
        )
        args.output.write_text(json.dumps(result, indent=2) + '\n')
    print(json.dumps(result, indent=2))


if __name__ == '__main__':
    main()
