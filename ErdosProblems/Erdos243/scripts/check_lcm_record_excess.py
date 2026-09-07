#!/usr/bin/env python3
"""Exact finite checks for LcmRecordExcess.md; no infinite-orbit claim.

Independent direct integer implementation, deliberately bounded to 20,000
denominator bits and 15 transitions. Fractions verify wall charges without
floating-point logarithms. Run from the repository root with repo-python.
"""
from fractions import Fraction
from itertools import product
from math import gcd, lcm, prod
import json


def centered(d, c):
    r = d % c
    return r - c if 2 * r >= c else r


def weight(t, kind):
    return Fraction(1, t * (max(2, t) - 1).bit_length()) if kind else Fraction(1, t)


def first_crossing_checks():
    """Check the nonmonotone time partition independently of canonical orbits.

    Arbitrary words test the order lemma, not denominator realizability.
    The even-state specialization tests the finite weighted charge with
    B=1, P=2 and odd walls. The last witness tests the actual-jump convention.
    """
    heights = final_drawdowns = weighted_words = 0
    for N in range(1, 6):
        for U in product(range(4), repeat=N + 1):
            reached = range(U[0] + 1, max(U) + 1)
            owners = {}
            record = U[0]
            for n in range(N):
                if U[n + 1] > record:
                    for t in range(record + 1, U[n + 1] + 1):
                        assert t not in owners
                        owners[t] = n
                    record = U[n + 1]
            assert set(owners) == set(reached)
            # Signed weights are allowed in the exact partition identity.
            signed = lambda t: (-1) ** t * t
            assert sum(map(signed, reached)) == sum(
                sum(signed(t) for t in reached if owners[t] == n)
                for n in range(N))
            for t in reached:
                direct = [n for n in range(N)
                          if all(U[j] < t for j in range(n + 1)) and t <= U[n + 1]]
                assert direct == [owners[t]]
                assert all(U[j] < U[owners[t] + 1] for j in range(owners[t] + 1))
                heights += 1
                final_drawdowns += U[-1] < t
        for U in product((2, 4, 6, 8), repeat=N + 1):
            walls = range(U[0] + 1, max(U) + 1, 2)
            for kind in (0, 1):
                lhs = sum((weight(t, kind) for t in walls), Fraction())
                rhs = sum(((U[n + 1] - U[n] - 1) * weight(U[n], kind)
                           for n in range(N) if U[n + 1] > max(U[:n + 1])), Fraction())
                assert lhs <= rhs
            weighted_words += 1

    # Local arithmetic feedback with a genuine overlap-one jump; no claim
    # that the entire three-state word extends to a canonical infinite orbit.
    old_record, U, Unext, B, L, a = 22, 19, 24, 3, 14245, 751
    mods = (5, 7, 11)
    x, wall = 20, 23
    assert all(gcd(m, r) == 1 for i, m in enumerate(mods) for r in mods[i + 1:])
    assert all(L % m == (x + i) % m == 0 for i, m in enumerate(mods))
    d = (a - 1) * U - L
    assert gcd(L, a) == 1 and U + d == Unext and -U <= -2 * d < U
    assert U < old_record < wall <= Unext
    assert max(0, Unext - old_record - B) == 0 < Fraction(1, wall)
    assert Fraction(1, wall) <= (d - B) * Fraction(1, U)
    assert (heights, final_drawdowns, weighted_words) == (6966, 3556, 5456)
    return dict(height_cases=heights, heights_above_final_state=final_drawdowns,
                weighted_words=weighted_words, weighted_inequalities=2 * weighted_words,
                actual_jump_witness=dict(old_record=old_record, U=U, Unext=Unext,
                                         B=B, L=L, a=a, wall=wall,
                                         actual_jump=d, record_increment=Unext-old_record),
                evidence_boundary='finite exact order/charging checks and a local arithmetic witness; '
                                  'not infinite canonical realizability or Lean verification')


def run():
    counts = dict(cases=0, distinct_seeds=0, transitions=0, terminated=0,
                  capped=0, charged_steps=0, charged_walls=0, weight_checks=0,
                  composed_weight_checks=0, composed_walls=0,
                  walls_before_translated_phase=0)
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
                states, denominators, digits = [p], [], []
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
                    states.append(Unext)
                    denominators.append(L)
                    digits.append(a)
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
                # Independently reconstruct the full finite theorem from
                # states, rather than adding the loop's local charge totals.
                # The CRT representative is the one in [P,2P), and a height
                # need only have been reached: the last state may be lower.
                phase = x + P + B
                first = phase + max(0, (states[0] + 1 - phase + P - 1) // P) * P
                selected = list(range(first, max(states) + 1, P))
                local_first = states[0] + 1 + (residue - states[0] - 1) % P
                all_walls = set(range(local_first, max(states) + 1, P))
                assert set(selected) == {t for t in all_walls if t >= phase}
                counts['walls_before_translated_phase'] += len(all_walls - set(selected))
                first_times = {t: next(j for j, u in enumerate(states) if t <= u)
                               for t in selected}
                for t, j in first_times.items():
                    assert j > 0 and all(u < t for u in states[:j])
                    n, source = j - 1, states[j - 1]
                    assert all(u < states[j] for u in states[:j])
                    assert states[j] - source == (digits[n] - 1) * source - denominators[n]
                    # Check the actual CRT cover against the actual old L_n.
                    for i, m in enumerate(mods):
                        assert m > B and denominators[n] % m == (t - B + i) % m == 0
                for kind in (0, 1):
                    wall_mass = sum((weight(t, kind) for t in selected), Fraction())
                    record_mass = sum((max(0, states[n + 1] - states[n] - B)
                                       * weight(states[n], kind)
                                       for n in range(len(states) - 1)
                                       if states[n + 1] > max(states[:n + 1])), Fraction())
                    assert wall_mass <= record_mass
                    counts['composed_weight_checks'] += 1
                counts['composed_walls'] += len(selected)
    counts['distinct_seeds'] = len(seeds)
    assert counts['cases'] == 6008 and counts['distinct_seeds'] == 6000
    assert counts['capped'] == 0
    assert counts['charged_walls'] == counts['composed_walls'] + counts['walls_before_translated_phase']
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
                first_crossing=first_crossing_checks(),
                inspected_states=counts['transitions'] + counts['terminated'],
                primitive_three_jump=dict(u=u, v=v, a=20, e=e, next_u=w, protected_prime=prime),
                evidence_boundary='finite exact checks, not proof of termination in general')


if __name__ == '__main__':
    print(json.dumps(run(), indent=2, sort_keys=True))
