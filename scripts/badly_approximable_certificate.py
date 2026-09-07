#!/usr/bin/env python3
"""
Erdos 257 -- a SUFFICIENT condition for survival, and how far rationals are from it.

Section 1: survival at rank n needs |mu_{n-1} - 1/2| >= h_n ~ 2^-n/6, and
mu_{n-1} is the shifted binary expansion of x := F(y) (the greedy support word).
Unwinding, y survives forever iff

    | x - a/2^n |  >=  c * 4^-n     for every n and every odd a,      (*)

i.e. x is not approximable by dyadic rationals to exponent 2.

SUFFICIENT CONDITION.  If x is BADLY APPROXIMABLE -- bounded continued-fraction
partial quotients -- then |x - p/q| >= c(x)/q^2 for ALL rationals p/q, dyadic
included, and (*) holds with c(x) = 1/(K+2) where K = sup partial quotient.  So:

    if F(y) has all partial quotients <= K and 1/(K+2) >= 2/3 * (constant),
    then y is PROVABLY an element of the achievement set.

That is a real certificate and it needs no normality assumption.  Quadratic
irrationals are badly approximable, so h(quadratic irrational) is provably in the
achievement set -- the obstruction is only whether such a value can be rational.

This measures the other direction: compute x = F(y) for rational y to thousands
of bits, run its continued fraction, and report the partial-quotient profile.
The smaller sup a_i, the closer y is to being certifiable.
"""
from __future__ import annotations
import sys, math
from fractions import Fraction

problem_id = "erdos_257"

sys.path.insert(0, "public-source-redacted://scripts")
from cantor_staircase_run_length_lab import Engine

D = int(sys.argv[1]) if len(sys.argv) > 1 else 900
eng = Engine(D)

def cf_of_bits(w, terms):
    """continued fraction of x = sum w_i 2^-i, using the exact dyadic truncation."""
    num = 0
    for b in w: num = 2*num + b
    den = 1 << len(w)
    a = []
    p, q = num, den
    for _ in range(terms):
        if q == 0: break
        a.append(p//q); p, q = q, p - (p//q)*q
    return a[1:]          # drop a_0 = 0

TARGETS = [("1/2",1,2),("1/21",1,21),("4/9",4,9),("1/465",1,465),("1/5",1,5),
           ("5/12",5,12),("3/7",3,7),("2/21",2,21),("1/4",1,4),("7/12",7,12)]
print(f"x = F(y) computed to {D} bits; continued fraction of the dyadic truncation")
print(f"(the last few partial quotients are truncation artefacts and are dropped)\n")
print(f"{'y':>8} {'#terms':>7} {'max a_i':>9} {'at i':>6} {'median':>7} "
      f"{'#a_i>=10':>9} {'#a_i>=50':>9} {'a_1..a_12':>34}")
best = None
for name, p, q in TARGETS:
    r = eng.run(p, q)
    if r["status"] != "alive": print(f"{name:>8}  {r['status']}"); continue
    w = r["word"]
    a = cf_of_bits(w, 4000)
    a = a[:max(1, len(a)-3)]
    if not a: continue
    mx = max(a); srt = sorted(a)
    print(f"{name:>8} {len(a):>7} {mx:>9} {a.index(mx):>6} {srt[len(a)//2]:>7} "
          f"{sum(1 for x in a if x>=10):>9} {sum(1 for x in a if x>=50):>9} "
          f"{str(a[:12]):>34}")
    if best is None or mx < best[0]: best = (mx, name)
print(f"\nsmallest sup a_i among these targets: {best[1]} with {best[0]}")
print("A certificate needs sup a_i bounded FOREVER.  For a.e. real the partial")
print("quotients follow Gauss-Kuzmin (infinite mean), so max over N terms grows")
print("like N -- boundedness has probability 0 and no rational here is close.")
