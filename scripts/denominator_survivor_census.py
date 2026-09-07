#!/usr/bin/env python3
"""
Erdos 257 -- EXHAUSTIVE survivor census by denominator.

Every previous survey in this corpus sampled random rationals.  This one is
exhaustive: for every reduced p/q with q <= Q it decides survive/die, so any
structure in q is visible rather than averaged away.

Sharp questions it answers:
  * is the survival fraction 1/2 for every q, or are some q anomalous?
  * Mersenne denominators q = 2^k - 1 give 1/q = w_k exactly (finite support) --
    do they behave differently?
  * are there q with NO surviving numerator, or ALL surviving?
  * does survival correlate with the continued-fraction data of p/q?  (The
    Minkowski-? analogy demands this lens: ? maps Q -> Z[1/2] precisely because
    continued fractions of rationals terminate.  Erdos 257 is the claim that the
    Mersenne staircase F maps Q -> Z[1/2].  If the analogy has any content, the
    CF of y should see it.)
"""
from __future__ import annotations
import sys, math, json
from math import gcd
sys.path.insert(0, "public-source-redacted://scripts")
from cantor_staircase_run_length_lab import Engine

Q = int(sys.argv[1]) if len(sys.argv) > 1 else 900
DEPTH = 64
eng = Engine(DEPTH)

def cf(p, q):
    a = []
    while q:
        a.append(p // q); p, q = q, p % q
    return a[1:] if a and a[0] == 0 else a

byq = {}
tot = surv = 0
cf_surv = {}; cf_all = {}
maxq_surv = {}
for q in range(2, Q + 1):
    s = n = 0
    for p in range(1, q):
        if gcd(p, q) != 1: continue
        r = eng.run(p, q)
        n += 1
        alive = (r["status"] == "alive")
        if r["status"] == "PRECISION":
            alive = True   # exact tie => finite representation => in the set
        s += alive
        A = cf(p, q)
        key = (len(A), max(A) if A else 0)
        cf_all[key] = cf_all.get(key, 0) + 1
        if alive: cf_surv[key] = cf_surv.get(key, 0) + 1
    byq[q] = (s, n)
    tot += n; surv += s

print(f"exhaustive census: all reduced p/q with q <= {Q}, depth {DEPTH}")
print(f"total {tot} rationals, survive-to-{DEPTH} {surv} ({surv/tot:.5f})\n")

# per-q survival fraction, z-score against binomial(n, phat)
phat = surv / tot
rows = []
for q, (s, n) in byq.items():
    if n < 8: continue
    z = (s - n * phat) / math.sqrt(n * phat * (1 - phat))
    rows.append((z, q, s, n))
rows.sort()
print("most anomalous denominators (z vs global rate):")
print(f"  {'q':>6} {'survive':>8} {'of':>6} {'frac':>8} {'z':>8}   note")
def note(q):
    t = []
    k = 1
    while (1 << k) - 1 <= q:
        if (1 << k) - 1 == q: t.append(f"q = 2^{k}-1")
        k += 1
    if q % 2 == 0: t.append("even")
    return ", ".join(t)
for z, q, s, n in rows[:6] + rows[-6:]:
    print(f"  {q:>6} {s:>8} {n:>6} {s/n:>8.4f} {z:>8.3f}   {note(q)}")

print("\nMersenne denominators q = 2^k - 1:")
for k in range(2, 14):
    q = (1 << k) - 1
    if q in byq and byq[q][1] >= 4:
        s, n = byq[q]
        print(f"  q = 2^{k}-1 = {q:>6}: {s}/{n} = {s/n:.4f}")

print("\ncontinued-fraction lens: survival rate by (CF length, max partial quotient)")
print(f"  {'len':>4} {'maxPQ':>6} {'count':>8} {'surv frac':>10} {'z':>8}")
items = [(k, v) for k, v in cf_all.items() if v >= 400]
items.sort(key=lambda kv: -kv[1])
for k, v in items[:14]:
    s = cf_surv.get(k, 0)
    z = (s - v * phat) / math.sqrt(v * phat * (1 - phat))
    print(f"  {k[0]:>4} {k[1]:>6} {v:>8} {s/v:>10.4f} {z:>8.3f}")
json.dump({"Q": Q, "total": tot, "survive": surv,
           "byq": {str(k): v for k, v in byq.items()}},
          open("/tmp/e257_census.json", "w"))
print("\nwrote /tmp/e257_census.json")
