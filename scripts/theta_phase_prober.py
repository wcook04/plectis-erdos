#!/usr/bin/env python3
"""Theta_L phase prober: near-integer statistics of the short-window
divisor phase  Theta_L(M) = sum_{i=1..L} (tau(M+i)-1) 2^{-i}.

This is the corpus's named missing object (Route R1).  The prober:

1. sieves tau over a window of M;
2. evaluates Theta_L(M) exactly as a scaled integer (scale 2^L) for every
   M in the window;
3. reports the distance-to-integer distribution, the near-hit census at
   several thresholds, and the arithmetic profile (Omega, largest prime
   factor, tau-max) of the closest hits;
4. reports the empirical constant P(dist < t)/t against the Haar null
   (uniform fractional part gives 1; the corpus measured ~2.5 heavy tail).
"""

from __future__ import annotations

import argparse
import json


def main() -> None:
    ap = argparse.ArgumentParser()
    ap.add_argument("--m0", type=int, default=1_000_000)
    ap.add_argument("--count", type=int, default=200_000)
    ap.add_argument("--L", type=int, default=40)
    args = ap.parse_args()
    m0, cnt, L = args.m0, args.count, args.L
    lo, hi = m0, m0 + cnt + L + 2

    tau = [0] * (hi + 2)
    d = 2
    while d <= hi:
        for m in range(d, hi + 1, d):
            tau[m] += 1
        d += 1

    scale = 1 << L
    # rolling window evaluation: Theta_L(M) * scale as integer.
    # Theta_L(M+1) = 2*Theta_L(M) - (tau(M+1)-1) + (tau(M+L+1)-1) * 2^{-L}
    # in scaled ints: T(M) = scale*Theta_L(M);
    # T(M+1) = 2*T(M) - (tau(M+1)-1) + (tau(M+L+1)-1)
    T = 0
    for i in range(1, L + 1):
        T += (tau[m0 + i] - 1) * (1 << (L - i))
    dists = []
    near = {t: 0 for t in (scale >> 6, scale >> 8, scale >> 10,
                            scale >> 12, scale >> 14)}
    hits = []
    for M in range(m0, m0 + cnt):
        frac = T & (scale - 1)
        dist = min(frac, scale - frac)
        dists.append(dist)
        for t in near:
            if dist < t:
                near[t] += 1
        if dist < (scale >> 12):
            hits.append((M, dist))
        tau_next = tau[M + 1] - 1
        tau_far = tau[M + L + 1] - 1
        T = 2 * T - scale * tau_next + tau_far
    n = cnt
    out = {
        "params": vars(args),
        "P_dist_lt": {
            str(t): {"p": round(v / n, 9), "p_over_t": round(v / n * t, 4)}
            for t, v in near.items()
        },
        "median_dist": sorted(dists)[n // 2] / scale,
        "near_hits_below_rel_2^-12": [
            {"M": M, "dist": round(dist / scale, 12)} for M, dist in hits[:40]
        ],
        "near_hit_count": len(hits),
    }
    # arithmetic profile of the 20 closest hits
    hits.sort(key=lambda kv: kv[1])
    prof = []
    for M, dist in hits[:20]:
        om = 0
        mm = M
        p = 2
        lp = 1
        while p * p <= mm:
            while mm % p == 0:
                om += 1
                mm //= p
                lp = max(lp, p)
            p += 1
        if mm > 1:
            om += 1
            lp = max(lp, mm)
        prof.append({"M": M, "dist": round(dist / scale, 12),
                     "Omega": om, "largest_prime": lp,
                     "tau_M": tau[M]})
    out["closest_hits_profile"] = prof
    print(json.dumps(out, indent=1))


if __name__ == "__main__":
    main()
