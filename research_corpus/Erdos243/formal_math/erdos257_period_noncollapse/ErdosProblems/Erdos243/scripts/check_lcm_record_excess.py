#!/usr/bin/env python3
"""Exact finite checks for LcmRecordExcess.md; no infinite-orbit claim.

Independent direct integer implementation, deliberately bounded to 20,000
denominator bits and 15 transitions. Fractions verify wall charges without
floating-point logarithms. Run from the repository root with repo-python.
"""
from fractions import Fraction
from math import gcd, lcm, prod
import json


def centered(d, c):
    r = d % c
    return r - c if 2 * r >= c else r


def weight(t, kind):
    return Fraction(1, t * (max(2, t) - 1).bit_length()) if kind else Fraction(1, t)


def run():
    counts = dict(cases=0, distinct_seeds=0, transitions=0, terminated=0,
                  capped=0, charged_steps=0, charged_walls=0, weight_checks=0)
    seeds = set()
    drawdown_example = None
    for mods in [(3,), (3, 5), (5, 7, 11)]:
        B, P = len(mods), prod(mods)
        x = next(x for x in range(P) if all((x + i) % m == 0 for i, m in enumerate(mods)))
        residue = (x + B) % P
        for k in range(1, 9):
            q = k * P
            for p in range(1, q):
                if gcd(p, q) != 1:
                    continue
                counts['cases'] += 1
                seeds.add((p, q))
                C, D, L, M, record = p, q, q, 1, p
                for n in range(15):
                    E = centered(D, C)
                    assert -C <= 2 * E < C
                    assert D == M * L and C % M == E % M == 0
                    U, V = C // M, E // M
                    a = (D - E) // C + 1
                    assert V == L - (a - 1) * U
                    if E == 0:
                        counts['terminated'] += 1
                        break
                    if D.bit_length() > 20000:
                        counts['capped'] += 1
                        break
                    rho = gcd(L, a)
                    Cnext, Dnext = C - E, a * D
                    Lnext, Mnext = lcm(L, a), M * rho
                    assert Dnext == Mnext * Lnext and Cnext % Mnext == 0
                    Unext = Cnext // Mnext
                    assert rho * Unext == U - V
                    if Unext > U:
                        assert rho == 1 and Unext - U == -V
                    if Unext > record:
                        d = Unext - U
                        first = record + 1 + (residue - record - 1) % P
                        walls = list(range(first, Unext + 1, P))
                        if walls:
                            counts['charged_steps'] += 1
                            counts['charged_walls'] += len(walls)
                            assert d > B and len(walls) <= d - B
                        for kind in (0, 1):
                            charge = sum((weight(t, kind) for t in walls), Fraction())
                            assert charge <= max(0, d - B) * weight(U, kind)
                            counts['weight_checks'] += 1
                        if U < record and drawdown_example is None:
                            drawdown_example = dict(seed=[p, q], step=n, U=U,
                                                    old_record=record, new_U=Unext,
                                                    actual_jump=d,
                                                    record_increment=Unext-record)
                        record = Unext
                    Enext = centered(Dnext, Cnext)
                    anext = (Dnext - Enext) // Cnext + 1
                    theta, thetanext = Fraction(E, C), Fraction(Enext, Cnext)
                    gamma = Fraction(a*a, anext) - 1
                    assert gamma + theta == (1-theta)*(a-1+thetanext)/anext
                    C, D, L, M = Cnext, Dnext, Lnext, Mnext
                    counts['transitions'] += 1
                else:
                    counts['capped'] += 1
    counts['distinct_seeds'] = len(seeds)
    assert counts['cases'] == 6008 and counts['distinct_seeds'] == 6000
    assert counts['capped'] == 0
    # One protected prime cannot forbid a clean rise of three.
    u, v, a, H, prime = 10, 187, 20, 11, 11
    e = v - (a-1)*u
    w = a*u-v
    assert e == -3 and -u <= 2*e < u
    assert gcd(u, v) == gcd(w, a*v) == 1
    assert u < H <= w and v % prime == 0 and 3*H < 2*prime**2
    # No positive local overlap charge can pay for every record contribution.
    for m in range(1, 20):
        c = 100*m + 1
        D, a = c*(c+m)-m, c+m+1
        assert gcd(c, D) == gcd(a, D) == 1
        assert D-(a-1)*c == -m and m*2 < c
    # The scalar witness is not a denominator-coherent orbit: two successive
    # zero numerators modulo 5 force all later numerators to be zero modulo 5.
    assert [(n*n+1) % 5 for n in (2, 3, 4)] == [0, 0, 2]
    return dict(status='pass', **counts, drawdown_example=drawdown_example,
                inspected_states=counts['transitions'] + counts['terminated'],
                primitive_three_jump=dict(u=u, v=v, a=20, e=e, next_u=w, protected_prime=prime),
                evidence_boundary='finite exact checks, not proof of termination in general')


if __name__ == '__main__':
    print(json.dumps(run(), indent=2, sort_keys=True))
