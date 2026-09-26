#!/usr/bin/env python3
# SPDX-FileCopyrightText: 2026 Will Cook
# SPDX-License-Identifier: Apache-2.0
"""Exact finite controls for the exact rank of the Moebius truncations.

Stdlib only; no files are written. For D = 1, ..., 16 the program computes
every grouped root-of-unity coefficient as a Fraction, checks that the nonzero
ones occur exactly at squarefree orders, and checks that the leading R_D block
of A_D has full rank modulo the trial-division-checked prime 1,000,003. Every
denominator is at most D, so a nonsingular reduction certifies a nonsingular
rational block. The universal statement is the ordinary proof in
totient_approximation.md, section 3; these controls are not a Lean proof.
"""

from fractions import Fraction
from math import gcd, isqrt
import json
from totient_approximation import arithmetic_sieve


def rank_mod_prime(a: list[list[int]], p: int) -> int:
    a = [r[:] for r in a]
    rank = 0
    for col in range(len(a[0]) if a else 0):
        pivot = next((i for i in range(rank, len(a)) if a[i][col] % p), None)
        if pivot is None:
            continue
        a[rank], a[pivot] = a[pivot], a[rank]
        inv = pow(a[rank][col] % p, -1, p)
        a[rank] = [(x * inv) % p for x in a[rank]]
        for i in range(rank + 1, len(a)):
            scale = a[i][col] % p
            if scale:
                a[i] = [(x - scale * y) % p for x, y in zip(a[i], a[rank])]
        rank += 1
        if rank == len(a):
            break
    return rank


def main() -> None:
    prime = 1000003
    assert all(prime % d for d in range(2, isqrt(prime) + 1))
    results = []
    for cutoff in range(1, 17):
        phi, mu = arithmetic_sieve(cutoff)
        predicted = sum(phi[q] for q in range(1, cutoff + 1) if mu[q])
        coefficients = []
        for q in range(1, cutoff + 1):
            beta = sum((Fraction(mu[q*m], q*q*m*m)
                        for m in range(1, cutoff // q + 1)), Fraction())
            assert (beta != 0) == (mu[q] != 0)
            if mu[q]:
                inner = sum((Fraction(mu[m], m*m)
                             for m in range(1, cutoff // q + 1) if gcd(m, q) == 1), Fraction())
                assert inner > 0
                assert beta == Fraction(mu[q], q*q) * inner
            coefficients.append({'q': q, 'coefficient': str(beta)})
        # All rational denominators in the matrix are at most cutoff < prime.
        # Nonzero determinant after reduction certifies nonzero determinant over Q.
        a = [[sum(mu[d] * pow(d, -1, prime)
                  for d in range(1, cutoff + 1) if (i + j) % d == 0) % prime
              for j in range(1, predicted + 1)]
             for i in range(1, predicted + 1)]
        observed = rank_mod_prime(a, prime)
        assert observed == predicted
        results.append({'D': cutoff,
                        'exact_rank_from_ordinary_proof': predicted,
                        'old_separated_factor_upper_bound': sum(d for d in range(1, cutoff + 1) if mu[d]),
                        'leading_block_size': predicted,
                        'rank_mod_prime': observed,
                        'prime': prime,
                        'grouped_frequency_coefficients': coefficients})
    print(json.dumps({'evidence': 'Exact finite arithmetic controls for a new ordinary-proof deduction; not Lean verification',
                      'cutoffs_tested': [1, 16], 'cases': results}, indent=2))


if __name__ == '__main__':
    main()
