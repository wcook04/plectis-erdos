#!/usr/bin/env python3
"""Finite-source certificates for factorial-channel tail gcds.

Python 3.10+, standard library only. Run:
  python check_finite_source.py --max-depth 60 --output certificates.json

No real floating point, network or Lean is used. The mathematical justification
for the uncomputed tail is in proofs/mathematical_refinements.md, not in a
claim that a finite numerical plateau proves stability.
"""
from __future__ import annotations
import argparse
from fractions import Fraction
from functools import lru_cache
from hashlib import sha256
from math import factorial, gcd, lcm, isqrt
from pathlib import Path
import json


def require(ok: bool, message: str) -> None:
    if not ok:
        raise ArithmeticError(message)


@lru_cache(None)
def fac(n: int) -> int:
    return factorial(n)


@lru_cache(None)
def weight(d: int, n: int) -> int:
    require(1 <= d <= n, 'Invalid weight indices')
    den = fac(d) ** (n // d)
    q, rem = divmod(fac(n), den)
    require(rem == 0, 'Weight is not integral')
    return q


def scalar_table(limit: int) -> list[int]:
    divisors = [[] for _ in range(limit + 1)]
    for d in range(2, limit // 2 + 1):
        for n in range(2 * d, limit + 1, d):
            divisors[n].append(d)
    u = [0] * (limit + 1)
    u[2] = 2
    for n in range(3, limit + 1):
        u[n] = -sum(weight(d, n) * u[d] for d in divisors[n])
    return u


def least_factorial_multiple(h: int) -> int:
    require(h > 0, 'Positive modulus required')
    k, f = 1, 1
    while f % h:
        k += 1
        f *= k
    return k


def prime(n: int) -> bool:
    return n >= 2 and all(n % d for d in range(2, isqrt(n) + 1))


def source_certificate(D: int, N: int, u: list[int]) -> dict:
    require(2 <= D < N < len(u), 'Invalid certificate interval')
    g = 0
    for n in range(D + 1, N + 1):
        g = gcd(g, u[n])
    require(g > 0, 'Zero finite gcd')
    sources = []
    exceptional_targets = set()
    block_tests = 0
    for d in range(2, D + 1):
        h = g // gcd(g, u[d])
        s = least_factorial_multiple(h)
        bad = []
        # For k >= s, k! | W(d,dk) makes this source vanish modulo g.
        for k in range(2, s):
            w = weight(d, d * k)
            require(w % fac(k) == 0, 'Unordered-block divisibility failed')
            block_tests += 1
            residue = (w * u[d]) % g
            if residue:
                bad.append({'k': k, 'target': d * k, 'residue': str(residue)})
                if d * k > N:
                    exceptional_targets.add(d * k)
        sources.append({'d': d, 'remaining_modulus': str(h),
                        'factorial_cutoff': s, 'bad_terms': bad})
    net = []
    for n in sorted(exceptional_targets):
        terms = [{'d': d, 'residue': str((weight(d, n) * u[d]) % g)}
                 for d in range(2, D + 1) if n % d == 0 and d < n]
        remainder = sum(int(t['residue']) for t in terms) % g
        require(remainder == 0, f'Uncancelled boundary source at D={D}, n={n}')
        net.append({'target': n, 'nonzero_terms': [t for t in terms if int(t['residue'])],
                    'sum_mod_g': remainder})
    ell = next(p for p in range(D // 2 + 1, D + 1) if prime(p))
    H = D * (2 * ell - 1)
    require(H < 2 * D * D and 2 * ell <= H, 'Quadratic horizon arithmetic failed')
    # This witness also checks the elementary factorial upper bound for g.
    require(u[2 * ell] == -fac(2 * ell) // (2 ** (ell - 1)), 'Prime-index formula failed')
    require(fac(2 * ell) % g == 0, 'Prime witness does not clear g')
    return {'D': D, 'scalar_prefix_N': N, 'tail_gcd': str(g),
            'prime_witness': ell, 'universal_horizon': H,
            'sources': sources, 'net_cancellations_beyond_N': net,
            'block_tests': block_tests}


def determinant(matrix: list[list[int]]) -> int:
    a = [[Fraction(x) for x in row] for row in matrix]
    sign = 1
    value = Fraction(1)
    for j in range(len(a)):
        pivot = next((i for i in range(j, len(a)) if a[i][j]), None)
        if pivot is None:
            return 0
        if pivot != j:
            a[pivot], a[j] = a[j], a[pivot]
            sign = -sign
        v = a[j][j]
        value *= v
        for i in range(j + 1, len(a)):
            scale = a[i][j] / v
            for k in range(j + 1, len(a)):
                a[i][k] -= scale * a[j][k]
            a[i][j] = 0
    value *= sign
    require(value.denominator == 1, 'Nonintegral integer determinant')
    return value.numerator


@lru_cache(None)
def channel_unit(n: int) -> tuple[int, ...]:
    # Coordinates 1,...,n stored at list positions 0,...,n-1.
    require(n >= 2, 'Unit index must be at least two')
    v = [0] * n
    v[n - 2] = n
    v[n - 1] = -1
    for d in range(2, n):
        if n % d:
            continue
        w = weight(d, n)
        for j, x in enumerate(channel_unit(d)):
            v[j] -= w * x
    return tuple(v)


def lattice_determinant_tests() -> list[dict]:
    rows = []
    for r in range(2, 9):
        for ell in [p for p in range(r + 1, r + 12) if prime(p)][:2]:
            columns = [channel_unit(ell * d)[:r-1] for d in range(2, r+1)]
            matrix = [list(x) for x in zip(*columns)]
            det = determinant(matrix)
            expected = fac(r)
            for d in range(2, r + 1):
                expected *= weight(d, ell * d)
            require(abs(det) == expected, f'Remote determinant failed for r={r}, ell={ell}')
            rows.append({'r': r, 'prime': ell, 'absolute_determinant': str(abs(det))})
    return rows


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--max-depth', type=int, default=60)
    parser.add_argument('--output', type=Path, default=Path('certificates.json'))
    args = parser.parse_args()
    require(2 <= args.max_depth <= 200, 'This demonstration supports 2 <= max-depth <= 200')
    prefix = max(2 * args.max_depth, 48)
    u = scalar_table(prefix)
    # N=2D is a tested choice for these depths, NOT the proved universal bound.
    rows = [source_certificate(D, 2*D, u) for D in range(2, args.max_depth+1)]
    depth24 = source_certificate(24, 32, u) if args.max_depth >= 24 else None
    if depth24:
        require(depth24['tail_gcd'] == '21684626964000', 'D=24 gcd disagrees')
        require([x['target'] for x in depth24['net_cancellations_beyond_N']] == [36,48],
                'D=24 exception set disagrees')
    # Independent check well beyond the scalar prefixes used in certificates.
    diagnostic_limit = max(1000, prefix)
    diagnostic = scalar_table(diagnostic_limit)
    for row in rows:
        g, D = int(row['tail_gcd']), row['D']
        require(all(v % g == 0 for v in diagnostic[D+1:]), 'Post-certificate diagnostic failed')
    dets = lattice_determinant_tests()
    # The general proof is termwise; these are independent finite diagnostics.
    for n in range(4, 101):
        require((fac(n) - 4 * weight(2, n)) % 360 == 0,
                'Remote-support dual congruence failed')
    require(-15 * weight(2, 4) + weight(2, 6) == 0,
            'Remote-support witness has nonzero channel')
    require(-15 * fac(4) + fac(6) == 360,
            'Remote-support witness has wrong moment')
    out = {'evidence': 'Exact arithmetic plus ordinary finite-source and partition-counting proofs; not Lean',
           'max_depth': args.max_depth, 'universal_bound': 'D(2 ell - 1) < 2D^2; D/2 < ell <= D prime',
           'linear_cutoff_status': 'N=2D is certified for the displayed depths only; no universal linear bound claimed',
           'scalar_prefix_computed': prefix, 'separate_diagnostic_limit': diagnostic_limit,
           'scalar_prefix_sha256': sha256('\n'.join(map(str,u)).encode()).hexdigest(),
           'rows': rows, 'depth24_compressed_certificate': depth24,
           'remote_determinant_tests': dets,
           'remote_minimum_example': {'D': 2, 'r': 4, 'minimum_moment': 360,
               'witness': {'4': -15, '6': 1}, 'dual_congruence': '360 | M - 4 V_2',
               'finite_termwise_diagnostic': '4 <= n <= 100'}}
    args.output.write_text(json.dumps(out, indent=2) + '\n')
    print(f'PASS: {len(rows)} finite-source certificates; '
          f'{sum(r["block_tests"] for r in rows)} finite block-divisibility tests; '
          f'{len(dets)} remote determinant tests.')
    if depth24:
        print('D=24: prefix 32; only net-source checks beyond prefix at 36 and 48; gcd=21684626964000.')
    print(f'Independent scalar diagnostic through {diagnostic_limit}; no universal N=2D assertion.')
    print(args.output)


if __name__ == '__main__':
    main()
