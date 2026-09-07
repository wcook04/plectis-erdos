#!/usr/bin/env python3
"""
Erdos 257 -- is the carry a finite-window (sofic) function of tau_A?

From section 10 of RunLengthMarginLawAndDivisorMultiplicity.md the whole problem
is the constraint system

    0 <= tau_A(m) = eps_m + 2 C_{m-1} - C_m <= tau(m)   for every m,
    1_A = mu * tau_A  a 0/1 indicator with infinite support,

where the carry recursion  C_{m-1} = floor((tau_A(m) + C_m)/2)  run DOWNWARD is
contractive: two different starting values collapse to the same trajectory.

If C_m is determined exactly by tau_A on a short window (m, m+L], then
(tau_A window, C) is a FINITE-STATE system, tau_A lives in a sofic shift, and
Erdos 257 becomes: can a sofic constraint be met by the divisor-sum of a 0/1
sequence?  That is a different kind of question from anything measured so far.

Measured here:
  (1) L(m) = smallest look-ahead making C_m exact (bisimulation of two extreme
      seeds run downward);
  (2) the prime dip: distribution of tau_A(p) at primes (must be <= 2) against
      tau_A(m) at general m (mean ~ (1/2) ln m);
  (3) the induced state count: how many distinct C values occur per window.
"""
from __future__ import annotations
import sys, math

problem_id = "erdos_257"

sys.path.insert(0, "public-source-redacted://scripts")
from cantor_staircase_run_length_lab import Engine

D = int(sys.argv[1]) if len(sys.argv) > 1 else 6000
eng = Engine(D)
TARGETS = [("1/21", 1, 21), ("4/9", 4, 9), ("1/2", 1, 2), ("1/465", 1, 465)]

def sieve_tau(N):
    t = [0] * (N + 1)
    for d in range(1, N + 1):
        for m in range(d, N + 1, d): t[m] += 1
    return t

def primes_upto(N):
    s = bytearray([1]) * (N + 1); s[0] = s[1] = 0
    for i in range(2, int(N ** .5) + 1):
        if s[i]: s[i*i::i] = bytearray(len(s[i*i::i]))
    return [i for i in range(N + 1) if s[i]]

tau = sieve_tau(D)
PR = set(primes_upto(D))

for name, p, q in TARGETS:
    r = eng.run(p, q)
    if r["status"] != "alive": print(f"{name}: {r['status']}"); continue
    w = r["word"]; M = len(w)
    A = [i + 1 for i, b in enumerate(w) if b]
    tauA = [0] * (M + 2)
    for d in A:
        for m in range(d, M + 1, d): tauA[m] += 1
    # exact carries via integer recurrence
    N = 0; C = [0] * (M + 2); pw = 1
    for m in range(1, M + 1):
        N = 2 * N + tauA[m]; pw <<= 1
        C[m] = (pw * p) // q - N
    # (1) look-ahead: run the downward recursion from m+L with seeds 0 and BIG
    BIG = 64
    need = {}
    lo_m, hi_m = M // 3, min(M // 3 + 1500, M - 80)
    for m in range(lo_m, hi_m):
        for L in range(1, 40):
            a = 0; b = BIG
            for j in range(m + L, m, -1):
                a = (tauA[j] + a) // 2
                b = (tauA[j] + b) // 2
            if a == b:
                need[m] = L; break
        else:
            need[m] = 99
    Ls = sorted(need.values())
    ok = sum(1 for m in range(lo_m, hi_m)
             if need[m] < 99 and (lambda s: s)(0) == 0)
    # verify the window value equals the true carry
    exact = 0
    for m in range(lo_m, hi_m):
        L = need[m]
        if L >= 99: continue
        a = 0
        for j in range(m + L, m, -1): a = (tauA[j] + a) // 2
        if a == C[m]: exact += 1
    n = hi_m - lo_m
    # (2) prime dip
    pv, gv = [], []
    for m in range(2, M + 1):
        (pv if m in PR else gv).append(tauA[m])
    # (3) state count
    print(f"\n=== {name} (depth {M}) ===")
    print(f"  carry look-ahead L(m) over m in [{lo_m},{hi_m}):  "
          f"min {Ls[0]}  median {Ls[n//2]}  p90 {Ls[int(.9*n)]}  max {Ls[-1]}")
    print(f"  window value == true carry for {exact}/{n} of them "
          f"({exact/n:.4f})")
    print(f"  tau_A at primes:   mean {sum(pv)/len(pv):.4f}  max {max(pv)}  "
          f"(bound 2; #primes {len(pv)})")
    print(f"  tau_A elsewhere:   mean {sum(gv)/len(gv):.4f}  max {max(gv)}  "
          f"(0.5*ln D = {0.5*math.log(M):.3f})")
    print(f"  distinct carry values in [{lo_m},{hi_m}): {len(set(C[lo_m:hi_m]))}")
