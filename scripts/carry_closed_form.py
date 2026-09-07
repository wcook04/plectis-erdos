#!/usr/bin/env python3
"""
Erdos 257 -- closed form for the carry, and the prime slack distribution.

CLOSED FORM.  C_m = floor( sum_{k>=1} tau_A(m+k) 2^-k ).  Swapping the order of
summation, the k with d | (m+k) are k = r, r+d, r+2d, ... with r = (-m) mod d
taken in {1,...,d}, so sum_k 2^-k = 2^-r / (1 - 2^-d) and

    C_m = floor(  sum_{d in A}  2^( d - ((-m) mod d) ) / (2^d - 1)  ).

The Mersenne weights reappear as an ALMOST-PERIODIC sum: each d in A contributes
a term depending only on m mod d.  Every term is ~ 2^-r_d(m), so the sum is
dominated by the d dividing m+1 (weight 1/2), m+2 (1/4), and so on; its
expectation is sum_{d in A, d<=m} 1/d ~ (1/2) ln m, matching the measured growth.

PRIME SLACK.  Section 12 proves 2 C_(p-1) <= C_p + 1 at every prime.  The slack
s(p) = (C_p + 1) div 2 - C_(p-1) >= 0 measures how close that is to tight.  This
reports its distribution and where it vanishes.
"""
from __future__ import annotations
import sys
from fractions import Fraction

problem_id = "erdos_257"

sys.path.insert(0, "public-source-redacted://scripts")
from cantor_staircase_run_length_lab import Engine

D = int(sys.argv[1]) if len(sys.argv) > 1 else 3000
eng = Engine(D)
def sieve(N):
    s = bytearray([1])*(N+1); s[0]=s[1]=0
    for i in range(2, int(N**.5)+1):
        if s[i]: s[i*i::i] = bytearray(len(s[i*i::i]))
    return s
PS = sieve(D+2)

print(f"depth {D}\n{'y':>8} {'closed form = C':>18} {'slack s(p)=0':>13} {'#primes':>8} "
      f"{'mean s':>7} {'max s':>6}")
for name, p, q in [("1/21",1,21),("4/9",4,9),("1/465",1,465),("1/5",1,5),("1/2",1,2)]:
    r = eng.run(p, q)
    if r["status"] != "alive": print(f"{name}: {r['status']}"); continue
    w = r["word"]; M = len(w); A = [i+1 for i, b in enumerate(w) if b]
    tauA = [0]*(M+2)
    for d in A:
        for j in range(d, M+1, d): tauA[j] += 1
    N = 0; C = [0]*(M+2); pw = 1
    for m in range(1, M+1):
        N = 2*N + tauA[m]; pw <<= 1; C[m] = (pw*p)//q - N
    # closed form, exact rationals, over a test range
    lo, hi = M//3, M//3 + 300
    ok = 0
    for m in range(lo, hi):
        tot = Fraction(0)
        for d in A:
            rr = (-m) % d
            if rr == 0: rr = d
            tot += Fraction(1 << (d - rr), (1 << d) - 1)
        ok += (int(tot) == C[m])
    sl = [((C[x] + 1)//2 - C[x-1]) for x in range(3, M+1) if PS[x]]
    print(f"{name:>8} {str(ok)+'/'+str(hi-lo):>18} {sum(1 for s in sl if s==0):>13} "
          f"{len(sl):>8} {sum(sl)/len(sl):>7.3f} {max(sl):>6}")
print("\nslack s(p) = 0 means the prime halving bound is exactly tight at p.")
