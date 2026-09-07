#!/usr/bin/env python3
"""Exact finite regressions for the round-6 ordinary proofs.

No floating-point arithmetic is used. Finite regressions do not establish
infinite interval realisation, equidistribution, or a Lean kernel receipt.
Requires SymPy for its independent integer Smith normal form implementation.
"""
from __future__ import annotations
import argparse
import bisect
import itertools
import json
from collections import Counter
from fractions import Fraction as F
from math import gcd
from pathlib import Path
from sympy import Matrix, ZZ
from sympy.matrices.normalforms import smith_normal_form

COUNTS: Counter[str] = Counter()

def check(ok: bool, category: str, context: object = None) -> None:
    if not ok:
        raise AssertionError((category, context))
    COUNTS[category] += 1

def ilog(base: int, n: int) -> int:
    if base < 2 or n < 1:
        raise ValueError('ilog requires base >= 2 and n >= 1')
    e, p = 0, 1
    while p * base <= n:
        e, p = e + 1, p * base
    return e

def unit_strip(n: int, r: int) -> int:
    n = abs(n)
    while n and gcd(n, r) > 1:
        n //= gcd(n, r)
    return n

def cut_normal_forms() -> None:
    for m in range(1, 7):
        for mask in range(1, 1 << (m + 1)):
            cuts = [s for s in range(m + 1) if mask & (1 << s)]
            rho = len(cuts) - int(0 in cuts and m in cuts)
            for r in (2, 3, 5, 7, 11):
                # r*C has entries r before the cut and 1 afterwards.
                a = Matrix([[r if i < s else 1 for s in cuts] for i in range(m)])
                snf = smith_normal_form(a, domain=ZZ)
                nz = [int(snf[i, i]) for i in range(min(snf.shape)) if snf[i, i]]
                observed = [unit_strip(x, r) for x in nz]
                check(observed == [1] + [r - 1] * (rho - 1),
                      'localised_smith_form', (m, cuts, r, observed))
    for m in range(1, 4):
        for mask in range(1, 1 << (m + 1)):
            cuts = [s for s in range(m + 1) if mask & (1 << s)]
            rho = len(cuts) - int(0 in cuts and m in cuts)
            for r, modulus in ((3, 2), (3, 4), (3, 5), (5, 3),
                               (5, 4), (5, 6), (7, 4), (11, 5)):
                inv_r = pow(r, -1, modulus)
                a = [[1 if i < s else inv_r for s in cuts] for i in range(m)]
                image = {tuple(sum(a[i][j] * x[j] for j in range(len(cuts))) % modulus
                               for i in range(m))
                         for x in itertools.product(range(modulus), repeat=len(cuts))}
                expected = modulus * (modulus // gcd(modulus, r - 1)) ** (rho - 1)
                check(len(image) == expected, 'modular_image_cardinality',
                      (m, cuts, r, modulus, len(image), expected))

def circle_cover_and_good_sites() -> dict:
    rho = F(27, 25)
    grid = sorted(F(5 ** j, 2 ** ilog(2, 5 ** j)) for j in range(25))
    gaps = [grid[j + 1] / grid[j] for j in range(24)] + [2 * grid[0] / grid[-1]]
    maxgap = max(gaps)
    check(maxgap == F(5 ** 22, 2 ** 51), 'cover_certificate')
    check(maxgap < rho, 'cover_certificate')
    for p, expected in ((2, F(5, 4)), (3, rho)):
        orbit = sorted(F(5 ** j, p ** ilog(p, 5 ** j)) for j in range(3))
        mingap = min([orbit[j + 1] / orbit[j] for j in range(2)]
                     + [p * orbit[0] / orbit[-1]])
        check(mingap == expected and mingap >= rho, 'three_point_gap_certificate')
    good = []
    hits = 0
    last_good = None
    Rstar = 2 ** 7 * 3 ** 5 * 5 ** 3
    for e in range(1, 401):
        t = 5 ** e
        hit = F(2 ** (ilog(2, t) + 1), t) < rho
        hits += int(hit)
        check(hits >= e // 25, 'finite_count_lower_bound', e)
        eligible = all(F(p ** (ilog(p, t) + 1), t) >= rho for p in (2, 3))
        good.append(eligible)
        if eligible:
            if last_good is not None:
                last_e, last_h = last_good
                height = 2 ** ilog(2, t) * 3 ** ilog(3, t) * t
                check(1 <= e - last_e <= 3, 'good_exponent_gap', (last_e, e))
                check(height % last_h == 0 and height // last_h <= Rstar,
                      'selected_height_ratio', (last_e, e))
            last_good = (e, 2 ** ilog(2, t) * 3 ** ilog(3, t) * t)
        if e >= 3:
            check(any(good[-3:]), 'every_three_has_good_site', e)
    return {'rho': str(rho), 'max_25_grid_gap': str(maxgap),
            'radix_upper_bound': Rstar,
            'positive_correction_bound_per_modulus': Rstar - 1}

def actual_cells_and_pulses() -> dict:
    limit = 2 * 5 ** 35
    powers = {}
    for p in (2, 3, 5):
        xs = [1]
        while xs[-1] * p < limit:
            xs.append(xs[-1] * p)
        powers[p] = xs
    jumps = sorted((x, p) for p in (2, 3, 5) for x in powers[p][1:])
    ts = [x for x, _ in jumps]
    mu = [0] * (len(ts) - 1)
    for x in powers[2]:
        for y in powers[3]:
            xy = x * y
            if xy >= ts[-1]:
                break
            for z in powers[5]:
                value = xy * z
                if value >= ts[-1]:
                    break
                if value >= 2:
                    mu[bisect.bisect_right(ts, value) - 1] += 1
    hs = []
    h = 1
    for _, p in jumps:
        h *= p
        hs.append(h)
    for n in range(len(mu)):
        check(mu[n] >= 1, 'actual_cell_positive', n)
    modulus = 3
    v = [0] * len(ts)
    pulses = []
    for n in range(1, len(mu) - 1):
        t, p = jumps[n]
        if p == 5 and t >= 5 ** 12 and F(jumps[n + 1][0], t) >= F(27, 25):
            amount = modulus * min(3, (mu[n] - 1) // modulus)
            if amount:
                v[n] = amount
                pulses.append((n, amount))
    check(bool(pulses), 'nonempty_pulse_test')
    eps = [v[n + 1] - v[n] for n in range(len(mu))]
    for n in range(len(mu)):
        check(mu[n] + eps[n] >= 1, 'modified_multiplicity_positive', n)
        check(eps[n] % modulus == 0, 'multiplicity_congruence', n)
    prefix = [0]
    for e in eps:
        prefix.append(prefix[-1] + e)
    for p in (2, 3):
        inds = [n for n, (_, q) in enumerate(jumps) if q == p]
        for a, b in zip(inds, inds[1:]):
            check(prefix[b] - prefix[a] == 0, 'complete_channel_block_preserved', (p, a, b))
    weighted = sum((F(eps[n], hs[n]) for n in range(len(mu))), F(0))
    pulse_value = sum((F(4 * amount, hs[n]) for n, amount in pulses), F(0))
    check(weighted == pulse_value and weighted > 0, 'weighted_pulse_identity')
    # The finite identity, including the endpoint term, is tested at every cutoff.
    for N in range(len(mu)):
        lhs = sum((F(eps[n], hs[n]) for n in range(N + 1)), F(0))
        rhs = F(v[N + 1], hs[N]) - F(v[0], hs[0])
        rhs += sum((v[j] * (F(1, hs[j-1]) - F(1, hs[j]))
                    for j in range(1, N + 1)), F(0))
        check(lhs == rhs, 'finite_weighted_summation_by_parts', N)
    return {'finite_jump_count': len(jumps), 'pulse_count': len(pulses),
            'modulus': modulus, 'maximum_pulse': max(v),
            'strictly_positive_value_change': True}

def cantor_and_spectral_algebra() -> None:
    radices = [5, 12, 6, 10, 30, 2, 3, 4, 15, 8] * 3
    for den in range(2, 41):
        for num in range(den):
            x = z = F(num, den)
            p, partial = 1, F(0)
            for b in radices:
                digit = (b * z).numerator // (b * z).denominator
                z = b * z - digit
                p *= b
                partial += F(digit, p)
                check(0 <= digit < b and 0 <= z < 1 and x == partial + z / p,
                      'cantor_exact_remainder')
    for den in range(2, 30):
        for num in range(1, den):
            c = F(num, den)
            co, si = 2*c/(1+c*c), (1-c*c)/(1+c*c)
            check(co*co + si*si == 1 and co - c*si == c and si+c*co == 1,
                  'spectral_boundary_algebra')
            # Numerator of the oscillatory part of the squared eigenfunction norm.
            check((1-c*c)*2*si*co - 2*c*(1-(co*co-si*si)) == 0,
                  'spectral_normalisation_algebra')

def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument('--output', type=Path)
    args = parser.parse_args()
    cut_normal_forms()
    cert = circle_cover_and_good_sites()
    pulse = actual_cells_and_pulses()
    cantor_and_spectral_algebra()
    report = {'schema': 'erdos269-r6-exact-regressions/1',
              'status': 'passed', 'arithmetic': 'integers_and_exact_rationals',
              'claim_ceiling': 'finite_regressions_not_infinite_proofs_or_Lean_receipts',
              'check_counts': dict(sorted(COUNTS.items())), 'total_checks': sum(COUNTS.values()),
              'circle_and_capacity_certificate': cert, 'finite_actual_pulse_test': pulse}
    text = json.dumps(report, indent=2, sort_keys=True)
    if args.output:
        args.output.write_text(text + '\n', encoding='utf-8')
    print(text)

if __name__ == '__main__':
    main()
