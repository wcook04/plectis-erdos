#!/usr/bin/env python3
"""
Erdos 257 -- death as an arithmetic bound on the carry.

Section 11 gives the FORWARD integer recursion (no reals):

    C_m = 2 C_{m-1} + eps_m - tau_A(m),   tau_A(m) = t_fixed(m) + 1_A(m),  C_0 = 0.

C_m = floor(2^m * sum_{j>m} tau_A(j) 2^-j), and tau_A(j) <= tau(j), so every
surviving orbit must satisfy the explicit DIVISOR-FUNCTION bound

    0 <= C_m <= Theta(m) := sum_{k>=1} tau(m+k) 2^-k.

Theta is arithmetic: no Mersenne weights, no irrational tails.  If C_m ever
exceeds Theta(m) no continuation exists, so y is not representable.  So:

    Erdos 257 <=> for every rational y, the forward carry recursion eventually
                  forces C_m above Theta(m).

This measures how tight that bound is on the surviving candidates: the ratio
C_m / Theta(m), its running maximum, and whether it approaches 1.  A ratio
bounded away from 1 means the divisor bound is slack and cannot be the binding
constraint; a ratio approaching 1 infinitely often means it is.
"""
from __future__ import annotations
import sys, math

problem_id = "erdos_257"

sys.path.insert(0, "public-source-redacted://scripts")
from cantor_staircase_run_length_lab import Engine

D = int(sys.argv[1]) if len(sys.argv) > 1 else 8000
eng = Engine(D)

def sieve_tau(N):
    t = [0]*(N+1)
    for d in range(1, N+1):
        for m in range(d, N+1, d): t[m] += 1
    return t

TAU = sieve_tau(D + 80)
def theta(m, K=60):
    return sum(TAU[m+k] / (1 << k) for k in range(1, K+1) if m+k <= D+79)

print(f"depth {D}:  C_m against the divisor bound Theta(m) = sum_k tau(m+k) 2^-k\n")
print(f"{'y':>8} {'max C':>6} {'max C/Theta':>12} {'at m':>7} {'mean C/Theta':>13} "
      f"{'#(ratio>0.9)':>13} {'#(ratio>0.99)':>14}")
for name, p, q in [("1/2",1,2),("1/21",1,21),("4/9",4,9),("1/465",1,465),("1/5",1,5),("5/12",5,12)]:
    r = eng.run(p, q)
    if r["status"] != "alive": print(f"{name}: {r['status']}"); continue
    w = r["word"]; M = len(w); A = [i+1 for i, b in enumerate(w) if b]
    tauA = [0]*(M+2)
    for d in A:
        for j in range(d, M+1, d): tauA[j] += 1
    N = 0; C = [0]*(M+2); pw = 1
    for m in range(1, M+1):
        N = 2*N + tauA[m]; pw <<= 1; C[m] = (pw*p)//q - N
    rows = []
    for m in range(2, M-70):
        th = theta(m)
        if th > 0: rows.append((C[m]/th, m))
    best = max(rows)
    mean = sum(x for x, _ in rows)/len(rows)
    n9 = sum(1 for x, _ in rows if x > 0.9)
    n99 = sum(1 for x, _ in rows if x > 0.99)
    print(f"{name:>8} {max(C[1:M]):>6} {best[0]:>12.5f} {best[1]:>7} {mean:>13.5f} "
          f"{n9:>13} {n99:>14}")
print("\nratio > 1 anywhere would be a contradiction (the bound is necessary);")
print("ratio bounded away from 1 means the divisor bound is slack.")
