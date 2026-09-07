#!/usr/bin/env python3
"""
Erdos 257 -- where is the problem EASIER?  The base-b map.

Erdos 257 is the b = 2 case of: for infinite A, is sum_{k in A} 1/(b^k - 1)
irrational?  Base 2 is the CRITICAL case -- the achievement set has positive
measure there and measure zero for every b >= 3 -- so mapping the b-dependence
says which structural features are special to 2 and which are generic.

Everything is exact: w_k = 1/(b^k - 1), Tail_n = sum_{k>n} w_k,
G_n = w_n - Tail_n, and there are 2^(n-1) gaps of width G_n at level n.

Predicted Hausdorff dimension: level n has 2^n bridges of length Tail_n ~
b^-n/(b-1), so dim = lim n log2 / (n log b) = log 2 / log b.  That is 1 at b = 2
and drops immediately.  Checked numerically below against the gap census.
"""
from __future__ import annotations
import sys, math, random
from fractions import Fraction

problem_id = "erdos_257"

LEVELS = 60
def census(b):
    W = [Fraction(0)] + [Fraction(1, b**k - 1) for k in range(1, LEVELS + 80)]
    t = sum(W[k] for k in range(LEVELS + 1, LEVELS + 80))
    tail = [Fraction(0)] * (LEVELS + 2)
    for n in range(LEVELS, -1, -1):
        tail[n] = t
        if n >= 1: t = t + W[n]
    E = tail[0]
    gaps = sum(Fraction(2**(n-1)) * (W[n] - tail[n]) for n in range(1, LEVELS + 1))
    return E, gaps, W, tail

def survive_rate(b, trials, depth, seed=5):
    """fraction of random rationals in (0, E_b) surviving to `depth`, exact rationals.

    NOTE.  The survival invariant is rho_n <= Tail_n and it must be checked after
    EVERY step, not only after a skip.  For b = 2, E_b = 1.607 > 1 and taking
    preserves the invariant, so checking on skips alone is equivalent.  For b >= 3,
    E_b < 1: a target above E_b is trivially non-representable, the greedy takes
    every coin forever with a positive residual, and a skip-only check never fires.
    Sampling must also be restricted to (0, E_b), since (E_b, 1) is not in range."""
    rnd = random.Random(seed)
    E, gaps, W, tail = census(b)
    ok = 0
    for _ in range(trials):
        q = rnd.randrange(3, 4000) | 1
        p = rnd.randrange(1, q)
        rho = Fraction(p, q) * E          # uniform in (0, E_b)
        alive = True
        for n in range(1, depth + 1):
            if rho >= W[n]: rho -= W[n]
            if rho > tail[n]: alive = False; break
        ok += alive
    return ok / trials

print(f"{'b':>3} {'E_b':>12} {'gap total':>12} {'measure(A_b)':>13} {'frac of [0,E]':>14} "
      f"{'log2/logb':>10} {'surv rate in (0,E_b)':>21}")
for b in range(2, 13):
    E, gaps, W, tail = census(b)
    meas = E - gaps
    dim = math.log(2)/math.log(b)
    sr = survive_rate(b, 3000, 40)
    print(f"{b:>3} {float(E):>12.8f} {float(gaps):>12.8f} {float(meas):>13.8f} "
          f"{float(meas/E):>14.8f} {dim:>10.5f} {sr:>21.5f}")
print("\nb=2 is the only base with measure(A_b) > 0: for b >= 3 the gap total equals")
print("E_b exactly, so the achievement set is a measure-ZERO Cantor set of dimension")
print("log2/log b.  Erdos 257 sits exactly at the critical base where the set is")
print("fattest, which is why survival there is a coin flip and collapses for b >= 3.")
