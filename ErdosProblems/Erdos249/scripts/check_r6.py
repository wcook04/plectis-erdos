#!/usr/bin/env python3
"""Exact finite checks accompanying r6. These checks do not prove unbounded results.
Requires Python 3.10+, numpy and sympy. No network access or data downloads.
Run: python checks/check_r6.py --output checks/receipt.json
"""
from __future__ import annotations
import argparse
from fractions import Fraction
from itertools import combinations_with_replacement
from math import comb, gcd, isqrt, prod
from pathlib import Path
import json
import numpy as np
from sympy.ntheory.modular import crt
from sympy import isprime, nextprime, totient


def sieve_phi(limit: int) -> list[int]:
    if limit < 1:
        raise ValueError('limit must be positive')
    a = list(range(limit + 1))
    a[1] = 1
    for p in range(2, limit + 1):
        if a[p] == p:
            for j in range(p, limit + 1, p):
                a[j] -= a[j] // p
    return a


def prime_trial(n: int) -> bool:
    """Trial division is used to certify each reported CRT central prime."""
    if n < 2:
        return False
    if n % 2 == 0:
        return n == 2
    return all(n % d for d in range(3, isqrt(n) + 1, 2))


def modular_rank(mat: np.ndarray, p: int) -> int:
    if not isprime(p) or p > 1_100_000:
        raise ValueError('require prime <= 1,100,000 for the int64 safety bound')
    a = np.asarray(mat, dtype=np.int64).copy() % p
    m, n = a.shape
    rank = 0
    for j in range(n):
        hits = np.flatnonzero(a[rank:, j])
        if not len(hits):
            continue
        t = rank + int(hits[0])
        a[[rank, t]] = a[[t, rank]]
        a[rank, j:] = a[rank, j:] * pow(int(a[rank, j]), -1, p) % p
        if rank + 1 < m:
            factors = a[rank + 1:, j].copy()
            a[rank + 1:, j:] = (
                a[rank + 1:, j:] - factors[:, None] * a[rank, j:][None, :]
            ) % p
        rank += 1
        if rank == m:
            break
    return rank


def monomial_matrix(values: np.ndarray, degree: int, p: int) -> np.ndarray:
    rows, variables = values.shape
    cols = [np.ones(rows, dtype=np.int64)]
    reduced = values % p
    for d in range(1, degree + 1):
        for indices in combinations_with_replacement(range(variables), d):
            v = np.ones(rows, dtype=np.int64)
            for j in indices:
                v = v * reduced[:, j] % p
            cols.append(v)
    return np.column_stack(cols)


def kernel_checks() -> list[dict]:
    out = []
    cases = [(2, 1, 2, 350), (2, 2, 2, 500), (2, 3, 2, 850),
             (6, 1, 3, 1400), (6, 1, 4, 2200)]
    ph = sieve_phi(30_000)
    for k, e, degree, rows in cases:
        indices = [(0, 0), (1, 0)] + [
            (j, r) for j in range(1, e + 1)
            for r in range(1, k**j) if r % k
        ]
        q = len(indices)
        assert q == k**e + 1
        prime_divisors = [p for p in range(2, k + 1) if k % p == 0 and prime_trial(p)]
        h = 2 ** len(prime_divisors)
        expected = comb(q + degree, q) - (comb(q + degree - h, q) if degree >= h else 0)
        values = np.array([[ph[k**j * n + r] for j, r in indices]
                           for n in range(1, rows + 1)], dtype=np.int64)
        ranks = {}
        for p in [1_000_003, 1_000_033]:
            ranks[str(p)] = modular_rank(monomial_matrix(values, degree, p), p)
            assert ranks[str(p)] == expected, (k, e, degree, ranks, expected)
        out.append(dict(base=k, level=e, degree=degree, rows=rows,
                        columns=comb(q + degree, q), expected_rank=expected,
                        ranks=ranks))
    return out


def polynomial_identity_checks() -> dict:
    ph = sieve_phi(150_000)
    samples = 0
    ratios = {}
    for k in [2, 3, 4, 6, 10, 12, 30]:
        primes = [p for p in range(2, k + 1) if k % p == 0 and prime_trial(p)]
        lam = []
        for bits in range(2 ** len(primes)):
            v = Fraction(k)
            for i, p in enumerate(primes):
                if not (bits >> i & 1):
                    v *= Fraction(p - 1, p)
            assert v.denominator == 1
            lam.append(v.numerator)
        assert len(set(lam)) == 2 ** len(primes)
        seen = set()
        for n in range(1, 4001):
            X, Y = ph[n], ph[k*n]
            assert prod(Y - l * X for l in lam) == 0
            assert Y % X == 0
            seen.add(Y // X)
            samples += 1
        assert seen == set(lam)
        ratios[str(k)] = sorted(lam)
    return dict(samples=samples, ratios=ratios)


def pulse_witness(m: int, D: list[int], L: int, coeff: list[int], b: int) -> dict:
    assert D == sorted(set(D)) and D[0] > 0 and len(D) == len(coeff)
    d0, r = D[0], (m - 2 if m != 8 else 2)
    offsets = list(range(-L, 0)) + list(range(1, L + 1))
    qs = []
    candidate = max(L, max(D))
    for _ in offsets:
        candidate = int(nextprime(candidate))
        while candidate % m != 1:
            candidate = int(nextprime(candidate))
        assert prime_trial(candidate)
        qs.append(candidate)
    residues = [r + 1] + [(-t * pow(d0, -1, q)) % q for t, q in zip(offsets, qs)]
    moduli = [m] + qs
    result = crt(moduli, residues)
    assert result is not None
    a, Q = map(int, result)
    assert gcd(a, Q) == 1
    p = a
    while p <= max(D) or d0*p <= L + 2*max(D) or not isprime(p):
        p += Q
    assert p < 10**12, 'trial-primality check intended for small certificate examples'
    assert prime_trial(p)
    N = d0*p
    def g(c: int, residue: int) -> int:
        return c * (int(residue == r) if m == 8 else residue)
    block = {}
    for t in range(-L, L + 1):
        value = sum(g(c, int(totient((N+t)//d)) % m)
                    for d, c in zip(D, coeff) if (N+t) % d == 0)
        block[str(t)] = value
        assert (value != 0) if t == 0 else (value == 0)
    for t, q in zip(offsets, qs):
        assert (N+t) % q == 0 and q % m == 1
        for d in D:
            if (N+t) % d == 0:
                assert ((N+t)//d) % q == 0
    C = sum(abs(c) for c in coeff) * (1 if m == 8 else m-1)
    eta = Fraction(C, (b-1)*b**L)
    cert = eta < 1 and Fraction(C+eta, b**(L+1)) < Fraction(1,2)
    return dict(modulus=m, exponents=D, coefficients=coeff, half_width=L,
                base=b, centre_prime=p, centre=N, central_residue=r,
                CRT_modulus=Q, CRT_residue=a,
                auxiliary_primes=dict(zip(map(str, offsets), qs)), block=block,
                bound=C, eta=str(eta), separation_certificate=cert,
                separation_lower_bound=(f'({abs(block["0"])} - {eta}) * {b}^(-{N})'
                                        if cert else None))


def certified_control(max_n: int) -> tuple[list[int], dict]:
    """A finite prefix of the EXISTING rational control, by interval arithmetic."""
    N = max_n + 160
    ph = sieve_phi(N)
    prefix = 0
    for n in range(1, N+1):
        prefix = 2*prefix + ph[n]
    den = 1 << N
    # S in [prefix/den, (prefix+N+2)/den].
    low = 5*den//4 - prefix - (N+2)
    high = 5*den//4 - prefix
    c = ph[:max_n+1]
    digits = []
    for j in range(1, max_n//2 + 1):
        dl = (12*low + 2*den) // (3*den)
        dh = (12*high + 2*den) // (3*den)
        assert dl == dh, ('ambiguous digit', j)
        d = dl
        assert -2 <= d <= 1
        low, high = 4*low-d*den, 4*high-d*den
        c[2*j] += d
        digits.append(d)
    assert all(0 <= c[n] <= n and abs(c[n]-ph[n]) <= 2 for n in range(1,max_n+1))
    return c, dict(coefficients_certified=max_n, enclosure_terms=N,
                   first_twenty_digits=digits[:20])


def robust_independence_checks() -> dict:
    max_n = 2500
    c, evidence = certified_control(max_n)
    phi = sieve_phi(max_n)
    ns = range(1,901)
    ranks = {}
    for name, f in [('totient',phi),('existing_rational_control',c)]:
        values = np.array([[n, f[n], f[n+1], f[2*n+1]] for n in ns],dtype=np.int64)
        for p in [1_000_003, 1_000_033]:
            rank = modular_rank(monomial_matrix(values,3,p),p)
            assert rank == 35
            ranks[f'{name}_mod_{p}'] = rank
    return dict(control_prefix=evidence, monomials=35, rows=900, ranks=ranks,
                interpretation='Finite evidence only; full independence is proved in the memorandum.')


def branch_control_check() -> dict:
    limit=100_000
    ph=sieve_phi(2*limit)
    odd_primorials=[]
    t=1
    for p in [3,5,7,11,13,17,19]:
        t*=p
        if 2*t <= 2*limit:
            odd_primorials.append(t)
    changes=set(2*t for t in odd_primorials)
    def g(n:int)->int:
        return 2*ph[n//2] if n in changes else ph[n]
    for n in range(1,limit+1):
        assert (g(2*n)-g(n))*(g(2*n)-2*g(n)) == 0
    return dict(tested_through=limit, changed_indices=sorted(changes),
                first_change={'n':6,'phi':ph[6],'g':g(6)},
                rationality_of_this_control='not asserted')


def main() -> None:
    parser=argparse.ArgumentParser()
    parser.add_argument('--output',type=Path,default=Path(__file__).with_name('receipt.json'))
    args=parser.parse_args()
    result={
        'status':'exact finite checks; no Lean compilation; no infinite theorem inferred from data',
        'kernel_product_ranks':kernel_checks(),
        'kernel_polynomial_identities':polynomial_identity_checks(),
        'dilated_pulses':[
            pulse_witness(3,[1,2],1,[1,-2],4),
            pulse_witness(3,[1,2],2,[1,-2],4),
            pulse_witness(3,[1,2],3,[1,-2],2),
            pulse_witness(8,[2,3,5],2,[1,-2,3],4)],
        'robust_algebraic_independence':robust_independence_checks(),
        'unlabelled_branch_control':branch_control_check(),
    }
    args.output.parent.mkdir(parents=True,exist_ok=True)
    args.output.write_text(json.dumps(result,indent=2)+'\n')
    print(json.dumps(result,indent=2))

if __name__=='__main__':
    main()
