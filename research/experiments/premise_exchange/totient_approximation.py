#!/usr/bin/env python3
# SPDX-FileCopyrightText: 2026 Will Cook
# SPDX-License-Identifier: Apache-2.0
"""Exact finite probes for the normalized totient Hankel approximation note.

Stdlib only; no files are written. Fractions certify the tested identities and
inequalities. This does not certify the infinite uniform approximation theorem,
Dirichlet's theorem, or novelty. See totient_approximation.md for ordinary proofs.
"""

from fractions import Fraction
from math import gcd, isqrt, prod
import json


def arithmetic_sieve(limit):
    phi = list(range(limit + 1))
    mu = [1] * (limit + 1)
    mu[0] = 0
    for p in range(2, limit + 1):
        if phi[p] != p:
            continue
        for n in range(p, limit + 1, p):
            phi[n] -= phi[n] // p
            mu[n] = -mu[n]
        for n in range(p * p, limit + 1, p * p):
            mu[n] = 0
    return phi, mu


def divisor_approximation(m, cutoff, mu):
    return sum((Fraction(mu[d], d) for d in range(1, cutoff + 1)
                if m % d == 0), Fraction())


def residue_factorization(i, n, cutoff, mu):
    return sum((Fraction(mu[d], d) * (i % d == a) * (n % d == (-a) % d)
                for d in range(1, cutoff + 1)
                for a in range(d)), Fraction())


def verify_matrix_case(size, cutoff):
    assert size >= 1 and cutoff >= 1
    phi, mu = arithmetic_sieve(max(2 * size, cutoff))
    for m in range(1, 2 * size + 1):
        assert Fraction(phi[m], m) == divisor_approximation(m, m, mu)

    # Exhaust all residue pairs, not just those occurring in the sampled matrix.
    for d in range(1, cutoff + 1):
        for a in range(d):
            for b in range(d):
                assert sum((a == r) * (b == (-r) % d) for r in range(d)) == (
                    (a + b) % d == 0)

    # Explicitly evaluate the separated factors on a bounded leading submatrix.
    probe_size = min(size, 16)
    for i in range(1, probe_size + 1):
        for n in range(1, probe_size + 1):
            assert residue_factorization(i, n, cutoff, mu) == (
                divisor_approximation(i + n, cutoff, mu))

    total_error = Fraction()
    one_dimensional_tail = Fraction()
    worst_error = Fraction()
    counted_entries = 0
    # Entries are constant on antidiagonals; exact multiplicities cover all N².
    for m in range(2, 2 * size + 1):
        multiplicity = min(m - 1, 2 * size + 1 - m, size)
        counted_entries += multiplicity
        error = abs(Fraction(phi[m], m) - divisor_approximation(m, cutoff, mu))
        tail = sum((Fraction(1, d) for d in range(cutoff + 1, m + 1)
                    if m % d == 0), Fraction())
        assert error <= tail
        total_error += multiplicity * error
        one_dimensional_tail += tail
        worst_error = max(worst_error, error)
    assert counted_entries == size * size
    mean_error = total_error / (size * size)
    finite_tail_bound = 2 * sum((Fraction(1, d * d)
                               for d in range(cutoff + 1, 2 * size + 1)), Fraction())
    assert mean_error <= one_dimensional_tail / size <= finite_tail_bound
    assert finite_tail_bound <= Fraction(2, cutoff)
    return {
        "N": size,
        "D": cutoff,
        "factorization_checked_on_leading_size": probe_size,
        "all_residue_pairs_checked_through_modulus": cutoff,
        "separable_rank_upper_bound": sum(d for d in range(1, cutoff + 1) if mu[d]),
        "generic_rank_upper_bound": cutoff * (cutoff + 1) // 2,
        "mean_absolute_error_exact": str(mean_error),
        "mean_absolute_error_decimal": float(mean_error),
        "worst_entry_error_exact": str(worst_error),
        "proved_mean_bound": str(Fraction(2, cutoff)),
    }


def is_prime(n):
    if n < 2:
        return False
    if n % 2 == 0:
        return n == 2
    return all(n % d for d in range(3, isqrt(n) + 1, 2))


def totient_by_trial_division(n):
    assert n >= 1
    result, remaining, p = n, n, 2
    while p * p <= remaining:
        if remaining % p == 0:
            result -= result // p
            while remaining % p == 0:
                remaining //= p
        p += 1
    if remaining > 1:
        result -= result // remaining
    return result


def prime_progression_witness(i, j, prime_count=4, max_trials=10000):
    assert i >= 1 and j >= 1 and i != j
    delta = j - i
    primes, p = [], 2
    while len(primes) < prime_count:
        if is_prime(p) and delta % p:
            primes.append(p)
        p += 1
    modulus = prod(primes)
    assert gcd(delta, modulus) == 1
    q = None
    # q = kM - delta is the reduced progression used in the ordinary proof.
    for k in range(1, max_trials + 1):
        candidate = k * modulus - delta
        if candidate > max(modulus, i) and is_prime(candidate):
            q = candidate
            break
    if q is None:
        raise RuntimeError("No prime found inside the declared finite search domain")
    n = q - i
    assert n >= 1 and n + i == q and (n + j) % modulus == 0
    left = Fraction(q - 1, q)
    right = Fraction(totient_by_trial_division(n + j), n + j)
    euler_product = prod(Fraction(p - 1, p) for p in primes)
    assert right <= euler_product
    assert left - right >= 1 - Fraction(1, q) - euler_product
    return {
        "rows": [i, j], "column": n, "prime": q,
        "forced_prime_divisors_of_second_argument": primes,
        "modulus": modulus, "reduced_progression_verified": True,
        "first_entry_exact": str(left), "second_entry_exact": str(right),
        "row_separation_exact": str(left - right),
        "row_separation_decimal": float(left - right),
        "elementary_lower_bound_exact": str(1 - Fraction(1, q) - euler_product),
        "maximum_progression_trials": max_trials,
    }


def main():
    cases = [(1, 1), (8, 2), (32, 4), (128, 8), (256, 16)]
    result = {
        "evidence": "Finite exact rational computation, not Lean validation",
        "matrix": "H(i,n)=phi(i+n)/(i+n), with i,n>=1",
        "cases": [verify_matrix_case(n, d) for n, d in cases],
        "arithmetic_separation_witnesses": [
            prime_progression_witness(i, j) for i, j in [(1, 2), (1, 3), (2, 5), (1, 7)]
        ],
        "limits": [
            "No finite computation proves the infinite uniform error barrier.",
            "The mean bound is for the leading N by N square, not arbitrary translated squares.",
            "Reported ranks are certified upper bounds from explicit factors, not measured exact ranks.",
            "No irrationality or novelty claim follows from this experiment.",
        ],
    }
    print(json.dumps(result, indent=2))


if __name__ == "__main__":
    main()
