#!/usr/bin/env python3
"""
Erdos 257 -- where does eps stop being low-complexity?

y = sum_{k in A} 1/(2^k-1) is rational  <=>  its binary word eps is eventually
periodic  <=>  (Morse-Hedlund) p_eps(n) <= n for some n.

The structured-family scan showed a sharp split: SPARSE A (lacunary 2^k,
factorials) give eps with LINEAR complexity -- p(16) = 122 and 55 -- while every
positive-density A gives eps saturating the sample (p(16) ~ 3800 of 3945).

That split matters, because linear-complexity binary words are exactly the regime
covered by the Mahler-Nishioka and Adamczewski-Bugeaud transcendence theorems.
Everything below the transition is (in principle) already settled; everything
above it is where a counterexample must live.

This locates the transition: A random of density delta, delta from 2^-12 up to
1/2, measuring the complexity growth of eps.  Reported as the exponent
    alpha = log2( p(2n) / p(n) )
which is 1 for linear complexity and n for full complexity, and as p(n)/n.
"""
from __future__ import annotations
import sys, math, random

K = int(sys.argv[1]) if len(sys.argv) > 1 else 12000
TRIALS = int(sys.argv[2]) if len(sys.argv) > 2 else 3
M = K + 96
WS = {}
def W(n):
    if n in WS: return WS[n]
    J = M // n
    if J == 0: v = 0
    elif J > 32: v = (((1 << (J*n)) - 1) // ((1 << n) - 1)) << (M - J*n)
    else:
        v = 0
        for j in range(1, J+1): v |= 1 << (M - j*n)
    WS[n] = v
    return v

def eps_bits(A, nbits):
    v = 0
    for k in A: v += W(k)
    return [int(c) for c in bin(v)[2:].rjust(M, "0")[:nbits]]

def pcount(w, n):
    seen = set(); mask = (1 << n) - 1; v = 0
    for i, b in enumerate(w):
        v = ((v << 1) | b) & mask
        if i >= n-1: seen.add(v)
    return len(seen)

NB = K - 60
print(f"K={K}, {NB} bits of eps, {TRIALS} trials per density\n")
print(f"{'density':>10} {'E|A|':>7} {'p(6)':>6} {'p(9)':>7} {'p(12)':>7} {'p(15)':>7} "
      f"{'p(18)':>7} {'p(12)/12':>9} {'alpha 6->12':>12}")
rows = []
for e in range(12, 0, -1):
    delta = 2.0**-e
    accs = {n: 0 for n in (6, 9, 12, 15, 18)}
    na = 0
    for t in range(TRIALS):
        rnd = random.Random(1000*e + t)
        A = [k for k in range(2, K+1) if rnd.random() < delta]
        na += len(A)
        if not A: continue
        w = eps_bits(A, NB)
        for n in accs: accs[n] += pcount(w, n)
    for n in accs: accs[n] /= TRIALS
    alpha = math.log2(accs[12]/accs[6])/1.0 if accs[6] else 0
    print(f"{delta:>10.6f} {na/TRIALS:>7.0f} {accs[6]:>6.0f} {accs[9]:>7.0f} "
          f"{accs[12]:>7.0f} {accs[15]:>7.0f} {accs[18]:>7.0f} {accs[12]/12:>9.1f} {alpha:>12.3f}")
    rows.append((delta, accs[12]/12))
print(f"\nfull complexity caps at min(2^n, {NB}-n+1); p(18) saturating means the")
print("sample, not the word, is the limit.  alpha = log2(p(12)/p(6)): 1.0 would be")
print("linear growth, 6.0 is full 2^n growth.")
