#!/usr/bin/env python3
"""Exact finite checks for the r6 arithmetic claims; no external packages.

These are discriminating finite checks. Infinite existence, asymptotics and
weighted divergence are established by the ordinary proofs, not this script.
"""
from __future__ import annotations
from fractions import Fraction
from math import gcd, isqrt, prod
from pathlib import Path
import hashlib
import json


def crt_block(moduli: tuple[int, ...]) -> tuple[int, int]:
    """Return the CRT start in [P,2P), with m_i | start+i."""
    x, P = 0, 1
    for i, m in enumerate(moduli):
        if m < 2 or gcd(P, m) != 1:
            raise ValueError('Moduli must exceed one and be pairwise coprime')
        x += P * (((-i - x) * pow(P, -1, m)) % m)
        P *= m
        x %= P
    x += P
    assert all((x + i) % m == 0 for i, m in enumerate(moduli))
    return x, P


def first_walls(R: int, y: int, phase: int, P: int) -> range:
    first = R + 1 + (phase - R - 1) % P
    return range(first, y + 1, P)


def is_prime_trial(p: int) -> bool:
    """Deterministic trial division, used only for the small displayed fixture."""
    if p < 2:
        return False
    if p % 2 == 0:
        return p == 2
    return all(p % d for d in range(3, isqrt(p) + 1, 2))


def main() -> dict:
    counters = dict(transitions=0, record_frames=0, fresh_frames=0,
                    overlap_frames=0, crossed_walls=0, weighted_frames=0,
                    raw_comparisons=0, partition_words=0)
    for moduli in ((2,), (3, 5), (5, 7, 11)):
        B = len(moduli)
        z, L = crt_block(moduli)
        assert all(m > B for m in moduli)
        for u in range(1, 91):
            for a in range(2, 24):
                rho = gcd(L, a)
                for b in range(-3, 7):
                    numerator = a*u - b*L
                    assert numerator % rho == 0
                    y = numerator // rho
                    if y <= 0:
                        continue
                    counters['transitions'] += 1
                    r = rho*y-u
                    V = b*L-(a-1)*u
                    assert r == -V == (y-u)+(rho-1)*y
                    if y <= u:
                        continue
                    for R in sorted({u, (u+y)//2, y-1}):
                        if not u <= R < y:
                            continue
                        counters['record_frames'] += 1
                        walls = first_walls(R, y, z+B, L)
                        count = len(walls)
                        counters['crossed_walls'] += count
                        if rho == 1:
                            counters['fresh_frames'] += 1
                            charge = max(y-u-B, 0)
                            if count:
                                assert y-u > B
                                assert (count-1)*L < y-u
                        else:
                            counters['overlap_frames'] += 1
                            charge = y-R
                        assert count <= charge
                        if y >= B:
                            assert charge <= max(r-B, 0)
                            counters['raw_comparisons'] += 1
                        # Sample two decreasing rational weights, independently
                        # of the cardinality bound checked in every frame.
                        if count and counters['weighted_frames'] < 2000:
                            for f in (lambda t: Fraction(1,t),
                                      lambda t: Fraction(1,t*max(1,t.bit_length()))):
                                assert sum(map(f,walls), Fraction(0)) <= charge*f(u)
                            counters['weighted_frames'] += 1
    # Unique first-crossing partition, including repeated drawdowns.
    for seed in range(1, 301):
        word = [1 + seed % 7]
        state = seed
        for _ in range(18):
            state = (1103515245*state + 12345) % 2**31
            word.append(1 + state % 80)
        seen = {}
        R = word[0]
        for n, y in enumerate(word[1:]):
            for height in range(R+1, y+1):
                assert height not in seen
                assert all(x < height for x in word[:n+1])
                seen[height] = n
            R = max(R, y)
        assert set(seen) == set(range(word[0]+1, max(word)+1))
        counters['partition_words'] += 1

    # Exact overlap example: all actual jumps one, rational sum one.
    partial = Fraction(0)
    for n in range(100):
        a, b, L, U = 2**(n+2), n+1, 2**(n+1), n+2
        rho, y = gcd(a,L), n+3
        assert rho*y == a*U-b*L
        assert y-U == 1
        partial += Fraction(b,a)
        assert partial == 1-Fraction(y,2**(n+2))

    # Integrable-weight example, checked using rational epsilon=1.
    partial = Fraction(0)
    charge_sum = Fraction(0)
    for n in range(9):
        L, U = 2**(2**n)-1, 2**n
        a, b = L+2, U
        nextL, y = L*a, 2*U
        assert gcd(L,a) == 1
        assert nextL == 2**(2**(n+1))-1
        assert y == a*U-b*L
        partial += Fraction(b,a)
        assert partial == 1-Fraction(y,nextL)
        charge_sum += Fraction(U,U*U)
    assert charge_sum < 2

    # A finite fixture of the adaptive congruence construction. This does
    # not claim a numerical certificate of the infinite Dirichlet supply.
    U=L=1
    rows=[]
    partial=Fraction(0)
    previous=0
    for n in range(4):
        v=U+1
        while gcd(v,L)!=1:
            v+=1
        residue=(v*pow(U,-1,L))%L if L>1 else 0
        lower=max(2*v+1, 2**(n+4), previous+1)
        a=lower+(residue-lower)%L
        while not is_prime_trial(a):
            a+=L
        b=(a*U-v)//L
        assert b*L == a*U-v
        assert 0<b<a and gcd(a,L)==gcd(v,a*L)==gcd(a,b)==1
        partial+=Fraction(b,a)
        rows.append(dict(n=n,U=U,L=L,v=v,a=a,b=b))
        U,L,previous=v,a*L,a
        assert partial == 1-Fraction(U,L)
    receipt = {
        'status':'PASS', 'arithmetic':'Python integers and fractions; small fixture primality by trial division',
        'counters':counters,
        'overlap_example_steps':100,
        'integrable_weight_example_steps':9,
        'adaptive_fixture':rows,
        'lean_compiled':False,
        'infinite_theorems':'ordinary proofs, not certified by these finite checks',
        'checker_sha256':hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),
    }
    target=Path(__file__).with_name('r6_receipt.json')
    target.write_text(json.dumps(receipt,indent=2)+'\n')
    print(json.dumps(receipt,indent=2))
    return receipt


if __name__=='__main__':
    main()
