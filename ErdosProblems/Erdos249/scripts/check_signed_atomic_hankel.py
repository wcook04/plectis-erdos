#!/usr/bin/env python3
"""Exact determinant/expansion and effective-error checks on finite signed atoms."""
from fractions import Fraction as F
from itertools import combinations, permutations
from math import factorial, prod
import json


def determinant(matrix):
    n = len(matrix)
    return sum((-1)**sum(p[i] > p[j] for i in range(n) for j in range(i+1, n))
               * prod(matrix[i][p[i]] for i in range(n)) for p in permutations(range(n)))


def main():
    xs = [F(1, 2**d-1) for d in (1, 2, 3, 5, 6, 7, 10, 11)]
    signs = [1, -1, -1, -1, 1, -1, 1, -1]
    checks = 0
    for n in range(1, 5):
        delta2 = prod((xs[j]-xs[i])**2 for i in range(n) for j in range(i+1, n))
        X = prod(xs[:n])
        rho = xs[n]/xs[n-1]
        A = sum(xs)
        constant = A**n/(factorial(n)*X*delta2)
        for s in (1, 2, 5, 12):
            moments = [sum(a*x**r for a, x in zip(signs, xs)) for r in range(s, s+2*n-1)]
            det = determinant([[moments[i+j] for j in range(n)] for i in range(n)])
            expansion = sum(prod(signs[j]*xs[j]**s for j in J)
                            * prod((xs[b]-xs[a])**2 for a, b in combinations(J, 2))
                            for J in combinations(range(len(xs)), n))
            leading = prod(signs[:n])*X**s*delta2
            assert det == expansion
            assert abs(det/leading-1) <= constant*rho**(s-1)
            checks += 1
    print(json.dumps({"status": "pass", "exact_checks": checks,
                      "scope": "finite signed atomic regression; infinite theorem is an ordinary proof"}))


if __name__ == "__main__":
    main()
