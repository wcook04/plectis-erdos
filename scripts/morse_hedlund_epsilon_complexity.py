#!/usr/bin/env python3
"""
Erdos 257 via Morse-Hedlund.

For any A, the value is  y = sum_m tau_A(m) 2^-m, whose binary digit word is
eps_m = (tau_A(m) + C_m) mod 2 -- determined by A alone.  And

    y is RATIONAL  <=>  eps is eventually periodic
                   <=>  (Morse-Hedlund)  p_eps(n) <= n  for some n.

So:  Erdos 257  <=>  for every infinite A,  p_eps(n) >= n+1 for all n.

That is a statement about the SUBWORD COMPLEXITY of an explicitly computable
binary word.  It is checkable: any structured A whose eps drops to p(n) <= n at
some n is a counterexample, outright.

This scans structured infinite A -- lacunary, polynomial, arithmetic, automatic,
Beatty, digit-defined, multiplicative -- computing eps exactly in fixed point and
measuring p_eps(n) against the Morse-Hedlund threshold n+1, plus a direct
eventual-periodicity check.

Lacunary and automatic A are expected to be covered by Mahler/Nishioka and
Adamczewski-Bugeaud transcendence, so the interest is in (a) confirming that the
complexity really does stay above n, and (b) locating which families come
CLOSEST to the threshold -- that is where a counterexample would have to live.
"""
from __future__ import annotations
import sys, math

K = int(sys.argv[1]) if len(sys.argv) > 1 else 4000
M = K + 96

def w_scaled(n):
    J = M // n
    if J == 0: return 0
    if J > 32:
        return (((1 << (J*n)) - 1) // ((1 << n) - 1)) << (M - J*n)
    v = 0
    for j in range(1, J+1): v |= 1 << (M - j*n)
    return v
WS = {}
def W(n):
    if n not in WS: WS[n] = w_scaled(n)
    return WS[n]

def bits_of(A, nbits):
    v = 0
    for k in A:
        if k <= K: v += W(k)
    s = bin(v)[2:].rjust(M, "0")
    return [int(c) for c in s[:nbits]]

def complexity(w, nmax):
    out = {}
    L = len(w)
    for n in range(1, nmax+1):
        seen = set(); mask = (1 << n) - 1; v = 0
        for i in range(L):
            v = ((v << 1) | w[i]) & mask
            if i >= n-1: seen.add(v)
        out[n] = len(seen)
        if out[n] <= n: break
    return out

def eventual_period(w, pmax):
    L = len(w); s = L//2
    for p in range(1, pmax+1):
        if all(w[i] == w[i+p] for i in range(s, L-p)): return p
    return None

def thue_morse(N):
    return [bin(i).count("1") & 1 for i in range(N+2)]
TM = thue_morse(K+4)

def rudin_shapiro(N):
    out = [0]*(N+2)
    for i in range(N+2):
        b = bin(i)[2:]; out[i] = sum(1 for j in range(len(b)-1) if b[j] == b[j+1] == "1") & 1
    return out
RS = rudin_shapiro(K+4)

def is_prime_sieve(N):
    s = bytearray([1])*(N+1); s[0]=s[1]=0
    for i in range(2, int(N**.5)+1):
        if s[i]: s[i*i::i] = bytearray(len(s[i*i::i]))
    return s
PS = is_prime_sieve(K+4)

PHI = (1+5**0.5)/2
FAMILIES = [
  ("lacunary 2^k",       [1 << j for j in range(1, 13)]),
  ("squares k^2",        [j*j for j in range(2, 64)]),
  ("cubes k^3",          [j**3 for j in range(2, 17)]),
  ("k^2+k+1",            [j*j+j+1 for j in range(1, 64)]),
  ("primes",             [i for i in range(2, K+1) if PS[i]]),
  ("AP 3k+1",            list(range(4, K+1, 3))),
  ("AP 2k",              list(range(2, K+1, 2))),
  ("Thue-Morse support", [i for i in range(2, K+1) if TM[i]]),
  ("Rudin-Shapiro supp", [i for i in range(2, K+1) if RS[i]]),
  ("Beatty floor(k*phi)",[int(j*PHI) for j in range(2, K)] ),
  ("squarefree",         [i for i in range(2, K+1) if all(i % (d*d) for d in range(2, int(i**.5)+1))]),
  ("Omega even",         [i for i in range(2, K+1) if sum(1 for d in range(2, i+1) for _ in iter(()) ) == 0]),  # placeholder
  ("Fibonacci",          [1,2,3,5,8,13,21,34,55,89,144,233,377,610,987,1597,2584]),
  ("factorials",         [2,6,24,120,720,5040]),
]
FAMILIES = [(n, sorted(set(x for x in a if 2 <= x <= K))) for n, a in FAMILIES if n != "Omega even"]

NB = K - 40
print(f"K={K}, using first {NB} bits of eps\n")
print(f"{'family':>22} {'|A|':>6} {'p(4)':>5} {'p(8)':>6} {'p(12)':>7} {'p(16)':>7} "
      f"{'min n with p(n)<=n':>19} {'ev.period':>10}")
for name, A in FAMILIES:
    if len(A) < 3: continue
    w = bits_of(A, NB)
    c = complexity(w, 20)
    hit = next((n for n in sorted(c) if c[n] <= n), None)
    per = eventual_period(w, 400)
    g = lambda n: c.get(n, "-")
    print(f"{name:>22} {len(A):>6} {str(g(4)):>5} {str(g(8)):>6} {str(g(12)):>7} "
          f"{str(g(16)):>7} {str(hit):>19} {str(per):>10}")
print("\np(n) <= n at any n would mean eps is eventually periodic, i.e. the value")
print("is RATIONAL -- an outright counterexample to Erdos 257.")
