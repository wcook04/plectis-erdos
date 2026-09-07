#!/usr/bin/env python3
"""
Erdos 257 -- exhaustive deep-death hunt.  A real falsification test.

The measured failure law is P(death at rank n) = 0.25 * G_n/w_n, i.e. Bernoulli
with summable rate ~ 2^-(n+1).  Under it, the deepest death among N targets is
~ log2(N).  The corpus's largest run was 323,825 RANDOM targets with deepest
rank 16.

This is EXHAUSTIVE, not sampled: every reduced p/q with q <= Q.  At Q = 6000
that is ~10.9M rationals, 34x the corpus's sample, and the null predicts a
deepest death rank of log2(10.9M) = 23.4.

STAKES.  A death at rank >= 32 would be a ~2^-9 event against the null and would
mean the failure process is NOT Bernoulli in the tail -- i.e. late deaths are
enriched, which is what Erdos 257 being TRUE would look like.  Finding none, and
finding the histogram tracking 2^-(n+1) out to the predicted cutoff, is the
strongest evidence available that 257 is false and that the binding difficulty is
certification rather than discovery.

Engine: fixed point with M = 2*DEPTH + 96 bits (3-4 limbs), W table built once.
Every comparison is certified; an undecidable one aborts rather than guessing.
"""
from __future__ import annotations
import sys, math, json
from math import gcd

Q = int(sys.argv[1]) if len(sys.argv) > 1 else 6000
DEPTH = int(sys.argv[2]) if len(sys.argv) > 2 else 44
M = 2*DEPTH + 96
DEEP = 20                      # record every death at or beyond this rank

def w_scaled(n, M):
    J = M // n
    if J == 0: return 0
    if J > 32:
        return (((1 << (J*n)) - 1) // ((1 << n) - 1)) << (M - J*n)
    v = 0
    for j in range(1, J+1): v |= 1 << (M - j*n)
    return v

W = [0]*(DEPTH+2)
for n in range(1, DEPTH+2): W[n] = w_scaled(n, M)
T0 = sum(w_scaled(k, M) for k in range(1, M+1))
TAIL = [0]*(DEPTH+2)
t = T0
for n in range(1, DEPTH+1):
    t -= W[n]; TAIL[n] = t
TERR = M + 2

deaths = {}
deep = []
tot = surv = 0
for q in range(2, Q+1):
    for p in range(1, q):
        if gcd(p, q) != 1: continue
        tot += 1
        rho = (p << M)//q
        err = 1
        d = 0
        for n in range(1, DEPTH+1):
            wn = W[n]
            if rho >= wn + err:
                rho -= wn; err += 1
            else:
                if rho > TAIL[n] + TERR:
                    d = n; break
        if d:
            deaths[d] = deaths.get(d, 0) + 1
            if d >= DEEP: deep.append((d, p, q))
        else:
            surv += 1

print(f"EXHAUSTIVE: all reduced p/q with q <= {Q}, depth {DEPTH}, M = {M} bits")
print(f"total {tot}  alive-at-{DEPTH} {surv} ({surv/tot:.6f})")
print(f"null prediction for deepest death rank: log2({tot}) = {math.log2(tot):.2f}\n")
print(f"{'rank':>5} {'deaths':>10} {'observed frac':>15} {'2^-(n+1)':>12} {'ratio':>8}")
for k in sorted(deaths):
    f = deaths[k]/tot; pred = 2.0**-(k+1)
    print(f"{k:>5} {deaths[k]:>10} {f:>15.8f} {pred:>12.8f} {f/pred:>8.4f}")
print(f"\ndeepest death rank observed: {max(deaths)}")
print(f"deaths at rank >= {DEEP}: {len(deep)}")
for d, p, q in sorted(deep, reverse=True)[:15]:
    print(f"   rank {d:>3}   {p}/{q}")
json.dump({"Q": Q, "depth": DEPTH, "total": tot, "alive": surv,
           "deaths": {str(k): v for k, v in deaths.items()},
           "deep": sorted(deep, reverse=True)[:200]},
          open("/tmp/e257_deep_hunt.json", "w"))
