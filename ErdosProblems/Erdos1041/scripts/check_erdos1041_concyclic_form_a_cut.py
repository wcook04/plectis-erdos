#!/usr/bin/env python3
"""Erdos #1041, producer `concyclic_form_a_cut_objective_below_one`: measurement.

Form A-cut objective for CONCYCLIC zeros, adjacent pairs, common truncation
radius s.  The path  w_i -> s w_i -> s w_{i+1} -> w_{i+1}  has length
2(1-s) + 2 s sin(delta_i/2) <= 2 for EVERY admissible s, so the whole obligation
is containment and

    V = min over adjacent (i,i+1), min over s >= max(tau_i, tau_{i+1}),
        of  max over the chord [s w_i, s w_{i+1}] of |g|,
    tau_j = sup{ t in [0,1] : |g(t w_j)| > 1 }.

V <= 1 for every concyclic configuration would settle Erdos #1041 for ALL
concyclic zeros at EVERY radius rho < 1, since then |f| = rho^n |g| <= rho^n < 1
on the path and the path has length < 2 rho.  The regular n-gon gives V = 1
exactly, in the limit s -> 0 where the path degenerates to the pair of radii of
length exactly 2 -- it is the one path family that reaches this problem's own
extremal configuration.  See ConcyclicAlternation.md section 8, producer P3.

USAGE:  ./repo-python <this file> [seed]        (default seed 7)
Prints one row per degree n = 3..10 and writes fa2.json-style output at the end.
Each row is a MEASUREMENT, not a proof; research_packet negative_results entry 19
applies -- a supremum pinned at a threshold reports one basin.
"""
import math, json, sys
import numpy as np
rng = np.random.default_rng(int(sys.argv[1]) if len(sys.argv) > 1 else 7)

def absg_many(w, Z):
    d = np.abs(Z[..., None] - w)
    return np.exp(np.log(np.maximum(d, 1e-300)).sum(axis=-1))

def taus(w, M=1201):
    t = np.linspace(0, 1, M)
    Z = t[:, None] * w[None, :]                 # (M, n)
    V = absg_many(w, Z)                          # (M, n)
    out = np.zeros(len(w))
    for j in range(len(w)):
        bad = V[:, j] > 1.0
        out[j] = t[np.max(np.where(bad)[0])] if bad.any() else 0.0
    return out

def pair_V(w, i, j, lo, NS=140, MT=161):
    if lo >= 1.0: return np.inf
    s = np.unique(np.concatenate([np.linspace(lo, 1.0, NS),
                                  lo + (1.0 - lo) * np.geomspace(1e-8, 1.0, NS)]))
    tau = np.linspace(0.0, 1.0, MT)
    Z = s[:, None] * (w[i] + tau[None, :] * (w[j] - w[i]))     # (S, MT)
    vals = absg_many(w, Z).max(axis=1)                          # (S,)
    k = int(np.argmin(vals)); best = float(vals[k])
    a = s[max(0, k-1)]; b = s[min(len(s)-1, k+1)]
    for _ in range(6):
        ss = np.linspace(a, b, 60)
        Z = ss[:, None] * (w[i] + tau[None, :] * (w[j] - w[i]))
        vv = absg_many(w, Z).max(axis=1)
        k = int(np.argmin(vv))
        if vv[k] < best: best = float(vv[k])
        a, b = ss[max(0, k-1)], ss[min(59, k+1)]
        if b - a < 1e-14: break
    return best

def V_config(ph):
    p = np.sort(np.asarray(ph) % (2*math.pi)); n = len(p); w = np.exp(1j*p)
    tj = taus(w)
    return min(pair_V(w, i, (i+1) % n, max(tj[i], tj[(i+1) % n])) for i in range(n))

res = {}
for n in [3,4,5,6,7,8,9,10]:
    reg = V_config(2*math.pi*np.arange(n)/n)
    worst, warg, wscale = -np.inf, None, None
    for e in [1e-1,3e-2,1e-2,3e-3,1e-3,1e-4,1e-5,1e-6]:
        for _ in range(14):
            ph = 2*math.pi*np.arange(n)/n + rng.normal(0, e, n)
            v = V_config(ph)
            if v > worst: worst, warg, wscale = v, ph, e
    # short climb from the worst
    ph = np.sort(warg % (2*math.pi)); cur = worst; step = wscale
    for it in range(140):
        cand = np.sort((ph + rng.normal(0, step, n)) % (2*math.pi))
        if np.min(np.diff(np.concatenate([cand, [cand[0]+2*math.pi]]))) < 1e-6: continue
        v = V_config(cand)
        if v > cur: ph, cur = cand, v
        if it % 35 == 34: step *= 0.55
    res[n] = {"regular_ngon_V": reg, "max_V_near_regular": cur,
              "excess_over_1": cur - 1.0, "worst_seed_scale": wscale}
    print(f"n={n:2d}  regular V = {reg:.12f}   adversarial near-regular max V = {cur:.12f}   "
          f"excess = {cur-1:+.3e}   (seed scale {wscale:g})", flush=True)
json.dump(res, open('/private/tmp/claude-501/-Users-willcook-src-ai-workflow/f2eb2a68-8669-4d6d-b7a3-85d0d67005aa/scratchpad/fa2.json','w'), indent=1)
