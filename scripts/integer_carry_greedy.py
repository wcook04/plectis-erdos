#!/usr/bin/env python3
"""
Erdos 257 -- the greedy as a bounded-look-ahead parity rule on the divisor lattice.

Setup (see RunLengthMarginLawAndDivisorMultiplicity.md sections 3, 10, 11).
eps = the eventually periodic binary word of the rational target y;
tau_A(m) = #{d in A : d | m};  C_m = floor(2^m * sum_{j>m} tau_A(j) 2^-j).

The carry identity  tau_A(m) = eps_m + 2 C_{m-1} - C_m  is exactly a binary adder
run from the least significant end:

    eps_m   = (tau_A(m) + C_m) mod 2          [output bit]
    C_{m-1} = (tau_A(m) + C_m) div 2          [carry]

Since tau_A(m) = t_fixed(m) + 1_A(m) with t_fixed(m) = #{d in A : d | m, d < m}
depending only on indices below m, the output bit FORCES membership:

    1_A(m) = (eps_m + C_m + t_fixed(m)) mod 2.

and C_m is pinned by tau_A on a window (m, m+L] with L <= 12, because the
downward recursion contracts by a factor 2 per step and C is bounded by ~13 in
the tested range.

WHAT THIS IS AND IS NOT.  It is an exact local characterisation: the support is
the unique sequence satisfying a 12-window parity consistency relation.  It is
NOT a forward algorithm -- deciding 1_A(m) needs C_m, which needs 1_A on
(m, m+12], so the recursion regresses.  The problem is a consistency condition on
a sequence (a subshift-like object over the divisor lattice), not an orbit.

REFUTED EN ROUTE: the rule "take m into A whenever C_m stays >= 0" is NOT the
Mersenne greedy.  It agrees with the true support at chance level (~50%) and
pins C at 0 identically.  Recorded so it is not retried.
"""
from __future__ import annotations
import sys
from fractions import Fraction
sys.path.insert(0, "public-source-redacted://ia_workflow".replace("ia_", "ai_") +
                "/formal_math/erdos257_period_noncollapse/scripts")
from cantor_staircase_run_length_lab import Engine

D = int(sys.argv[1]) if len(sys.argv) > 1 else 4000
LOOKAHEAD, SEED = 12, 32
TARGETS = [("1/2",1,2),("1/4",1,4),("3/8",3,8),("1/21",1,21),("4/9",4,9),
           ("1/465",1,465),("1/5",1,5),("2/21",2,21),("5/12",5,12),("3/7",3,7)]

def eps_word(p, q, M):
    e = [0]*(M+2); t = Fraction(p, q)
    for m in range(1, M+1):
        t *= 2
        if t >= 1: e[m] = 1; t -= 1
    return e

eng = Engine(D)
print(f"depth {D}, look-ahead L={LOOKAHEAD}, seed {SEED}\n")
print(f"{'y':>8} {'dyadic':>7} {'parity rule = A':>18} {'L-window = C':>14} "
      f"{'maxC':>5} {'seed-below off':>15}")
for name, p, q in TARGETS:
    r = eng.run(p, q)
    if r["status"] != "alive":
        print(f"{name:>8}  {r['status']}@{r['death']}"); continue
    w = r["word"]; M = len(w); A = [i+1 for i, b in enumerate(w) if b]
    tauA = [0]*(M+2); tfix = [0]*(M+2)
    for d in A:
        for j in range(d, M+1, d): tauA[j] += 1
        for j in range(2*d, M+1, d): tfix[j] += 1
    N = 0; C = [0]*(M+2); pw = 1
    for m in range(1, M+1):
        N = 2*N + tauA[m]; pw <<= 1; C[m] = (pw*p)//q - N
    eps = eps_word(p, q, M)
    parity_ok = sum(1 for m in range(1, M+1)
                    if w[m-1] == (eps[m] + C[m] + tfix[m]) % 2)
    lo, hi = M//4, M//4 + 1500
    win_ok = 0; below = set()
    for m in range(lo, hi):
        a = SEED; b = 0
        for j in range(m+LOOKAHEAD, m, -1):
            a = (tauA[j] + a)//2; b = (tauA[j] + b)//2
        win_ok += (a == C[m]); below.add(b - C[m])
    dy = (q & (q-1)) == 0
    print(f"{name:>8} {str(dy):>7} {str(parity_ok)+'/'+str(M):>18} "
          f"{str(win_ok)+'/'+str(hi-lo):>14} {max(C[lo:hi]):>5} {str(sorted(below)):>15}")
print("\nseed-below offset is {-1} exactly for the dyadic targets and {0} otherwise:")
print("dyadic y has eps_m = 0 past its last 1-bit, so tau_A(m)+C_m is always even")
print("and a seed below the true carry stays exactly one below forever.")
