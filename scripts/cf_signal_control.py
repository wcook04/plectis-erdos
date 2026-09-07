#!/usr/bin/env python3
"""
Erdos 257 -- is the continued-fraction survival signal real, or magnitude bias?

The exhaustive census (denominator_survivor_census.py, q <= 700) reported very
large deviations in survival rate by (CF length, max partial quotient):
|z| up to 11.8.  Before believing that, it must be controlled.

CONFOUND.  Survival depends strongly on the MAGNITUDE of y: the rank-1 gap is
(E-1, 1) = (0.6067, 1), so ~39% of y in (0,1) die at rank 1 alone.  And the
continued fraction encodes magnitude directly -- a_1 = floor(1/y) -- so any CF
cell that concentrates on large y will show a spurious deficit.

CONTROLS (both stratified, Cochran-Mantel-Haenszel pooled):
  (a) stratify by the value of y in NBINS equal bins of (0,1);
  (b) stratify by the greedy prefix b_1..b_K, which pins y inside one cylinder
      of the Cantor structure -- a strictly finer positional control.
A CF signal that survives (b) is arithmetic.  One that vanishes was magnitude.
"""
from __future__ import annotations
import sys, math
from math import gcd

problem_id = "erdos_257"

sys.path.insert(0, "public-source-redacted://scripts")
from cantor_staircase_run_length_lab import Engine

Q = int(sys.argv[1]) if len(sys.argv) > 1 else 700
DEPTH, NBINS, K = 64, 200, 8
eng = Engine(DEPTH)

def cf(p, q):
    a = []
    while q:
        a.append(p // q); p, q = q, p % q
    return a[1:] if a and a[0] == 0 else a

recs = []
for q in range(2, Q + 1):
    for p in range(1, q):
        if gcd(p, q) != 1: continue
        r = eng.run(p, q)
        alive = r["status"] != "dead"
        a = cf(p, q)
        pref = tuple(r["word"][:K]) if len(r["word"]) >= K else ("dead", r["death"])
        recs.append((p / q, alive, (len(a), max(a) if a else 0), pref))
tot = len(recs); surv = sum(1 for r in recs if r[1])
print(f"exhaustive q <= {Q}: {tot} rationals, survive {surv} ({surv/tot:.5f})\n")

print("survival vs magnitude of y (the confound):")
for lo in [i / 10 for i in range(10)]:
    sub = [r for r in recs if lo <= r[0] < lo + 0.1]
    if sub: print(f"   y in [{lo:.1f},{lo+0.1:.1f}): {sum(1 for r in sub if r[1])/len(sub):>7.4f}  (n={len(sub)})")

def cmh(stratkey, label):
    strata = {}
    for y, alive, cfk, pref in recs:
        s = stratkey(y, pref)
        strata.setdefault(s, []).append((cfk, alive))
    rate = {s: sum(1 for _, a in v if a) / len(v) for s, v in strata.items()}
    O, E, V = {}, {}, {}
    for s, v in strata.items():
        pj = rate[s]
        for cfk, alive in v:
            O[cfk] = O.get(cfk, 0) + (1 if alive else 0)
            E[cfk] = E.get(cfk, 0.0) + pj
            V[cfk] = V.get(cfk, 0.0) + pj * (1 - pj)
    n = {}
    for _, _, cfk, _ in recs: n[cfk] = n.get(cfk, 0) + 1
    rows = [(abs((O[c] - E[c]) / math.sqrt(V[c])) if V[c] > 0 else 0.0, c) for c in O if n[c] >= 400]
    rows.sort(reverse=True)
    print(f"\n{label}  ({len(strata)} strata)")
    print(f"   {'len':>4} {'maxPQ':>6} {'n':>7} {'obs':>7} {'exp':>9} {'z':>8}")
    for z, c in rows[:8]:
        sg = 1 if O[c] > E[c] else -1
        print(f"   {c[0]:>4} {c[1]:>6} {n[c]:>7} {O[c]:>7} {E[c]:>9.1f} {sg*z:>8.3f}")
    print(f"   max |z| over {len(rows)} cells = {rows[0][0]:.3f}   "
          f"(expected max |z| under the null with {len(rows)} cells ~ {math.sqrt(2*math.log(len(rows))):.2f})")

cmh(lambda y, pref: 0, "UNCONTROLLED (reproduces the census)")
cmh(lambda y, pref: min(NBINS - 1, int(y * NBINS)), f"(a) stratified by y-value, {NBINS} bins")
cmh(lambda y, pref: pref, f"(b) stratified by greedy prefix b_1..b_{K}")
