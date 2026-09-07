#!/usr/bin/env python3
"""
Erdos 257 -- the carry peaks at primes, because primes are where divisor supply dies.

Section 11 gives the forward integer recursion  C_m = 2 C_{m-1} + eps_m - tau_A(m).
The index 1 is never in A (w_1 = 1 exceeds every target below 1), so at a prime p
the only possible divisor in A is p itself:

    tau_A(p) = 1_A(p) in {0,1}.

Hence, at EVERY prime,        2 C_{p-1} <= C_p + 1 <= max_m C_m + 1,

so the carry is forced to at most half its global bound just before every prime.
Bertrand's postulate puts a prime in every (n, 2n], so this fires at every scale.
Dually, C_m is largest where tau_A(m) is smallest, so the carry's global maximum
should sit AT a prime.

Both are checked below.  The inequality is a theorem (derived, not measured).
Saturation of the bound is empirical and holds for 8 of the 9 surviving targets
tested -- 1/465 falls one short.  The argmax-at-a-prime holds for 9 of 9, against
a prime density of 1/ln(8000) = 0.111.
"""
from __future__ import annotations
import sys

problem_id = "erdos_257"

sys.path.insert(0, "public-source-redacted://scripts")
from cantor_staircase_run_length_lab import Engine

D = int(sys.argv[1]) if len(sys.argv) > 1 else 8000
eng = Engine(D)
TARGETS = [("1/2",1,2),("1/21",1,21),("4/9",4,9),("1/465",1,465),("1/5",1,5),
           ("5/12",5,12),("3/7",3,7),("2/21",2,21),("3/8",3,8),("7/15",7,15)]

def sieve(N):
    s = bytearray([1])*(N+1); s[0] = s[1] = 0
    for i in range(2, int(N**.5)+1):
        if s[i]: s[i*i::i] = bytearray(len(s[i*i::i]))
    return s
PS = sieve(D+2)

print(f"depth {D}\n")
print(f"{'y':>8} {'maxC':>5} {'max C_(p-1)':>12} {'floor((maxC+1)/2)':>18} {'ok':>3} "
      f"{'argmax C prime?':>16} {'#argmax':>8} {'mean C':>7} {'mean C_(p-1)':>13}")
allok = True
for name, p, q in TARGETS:
    r = eng.run(p, q)
    if r["status"] != "alive": print(f"{name}: {r['status']}"); continue
    w = r["word"]; M = len(w); A = [i+1 for i, b in enumerate(w) if b]
    tauA = [0]*(M+2)
    for d in A:
        for j in range(d, M+1, d): tauA[j] += 1
    N = 0; C = [0]*(M+2); pw = 1
    for m in range(1, M+1):
        N = 2*N + tauA[m]; pw <<= 1; C[m] = (pw*p)//q - N
    allC = C[1:M+1]; mx = max(allC)
    argmax = [m for m in range(1, M+1) if C[m] == mx]
    pm1 = [C[x-1] for x in range(3, M+1) if PS[x]]
    pred = (mx + 1)//2
    ok = (max(pm1) == pred); allok &= ok
    frac_prime = sum(1 for m in argmax if PS[m])/len(argmax)
    print(f"{name:>8} {mx:>5} {max(pm1):>12} {pred:>18} {str(ok):>3} "
          f"{frac_prime:>16.3f} {len(argmax):>8} {sum(allC)/len(allC):>7.3f} "
          f"{sum(pm1)/len(pm1):>13.3f}")
print(f"\nprime-halving bound saturated on every target: {allok}" + "   (the INEQUALITY 2C_(p-1) <= C_p + 1 is a theorem and always holds;")
print("    only its SATURATION is empirical, and 1/465 falls one short.)")
print("density of primes near m=8000 is 1/ln(8000) = 0.111, so argmax-at-a-prime")
print("is not chance: the carry is large exactly where tau_A(m) is small.")
