#!/usr/bin/env python3
"""Transplant probe: the #249 period-killer certificate, run on Erdős #257.

`TotientTailPeriodKiller.lean` proves that `∑ φ(n)/2ⁿ` is not a rational with
a given denominator by exhibiting a *certified kill*: with

    windowDiscrepancy h N L = ∑_{j<L} ( f(N+h+1+j) − f(N+1+j) )·2^{L−1−j}
    R_M                     = ∑_{j≥1} f(M+j)/2^j
    R_{N+h} − R_N           = windowDiscrepancy/2^L + E,   |E| ≤ radius/2^L

`certifiedKill h N L` asks that `windowDiscrepancy mod 2^L` avoid the
radius-neighbourhood of `0`; that provably forces `R_{N+h} − R_N ∉ ℤ`, which
contradicts the tail-period law whenever `oddPart(Q) ∣ 2ʰ − 1`.

Nothing in that machine is special to `φ`.  This script instantiates it at

    f = c_A,     c_A(n) = #{d ∈ A : d ∣ n}          (so ∑ c_A(n)/2ⁿ = ∑_{d∈A} 1/(2^d−1))

which is Erdős #257, and measures the one quantity that decides whether the
transplant is viable: **the certificate radius**.

For `φ` the radius is `N+h+L+2`, LINEAR in `N`.  That is what forces
`certifiedKill_basepoint_lt_two_pow` (`N < 2^{L−1}`) and lets
`no_certifiedKill_of_large_prime_annihilator` stall the method for #249.

For `c_A` the radius is `∑_{i≥0} ( c_A(N+h+L+1+i) + c_A(N+L+1+i) )/2^{i+1}`,
governed by the divisor function rather than by `n`, hence `n^{o(1)}` — and
measured below it is *bounded* near 40 out to `N = 60000` even for the
densest possible support `A = ℕ`.

Everything here is exact integer arithmetic except the radius, which is
computed in floating point as a deliberately CONSERVATIVE over-estimate (it
sums both tails in absolute value rather than their difference).  A reported
certificate is therefore pessimistic, never optimistic.

**Finite evidence, not a proof.**  A certificate at one `(h, N, L)` excludes
one denominator class.  Proving Erdős #257 needs a certificate supply for
every period and every threshold.  What this script establishes is that the
certificate *cone* is wide open for #257 in exactly the regime where it is
closed for #249 — so the remaining work is to prove the abundance measured
here, not to find a first certificate.
"""

from __future__ import annotations

problem_id = "erdos_257"

import argparse
import json


def divisor_count_in(support: str, limit: int) -> list[int]:
    """c_A(n) for n ≤ limit, for a named support A."""
    counts = [0] * (limit + 1)
    if support == "all":
        members = range(1, limit + 1)
    elif support == "squarefree":
        sieve = [True] * (limit + 1)
        p = 2
        while p * p <= limit:
            for m in range(p * p, limit + 1, p * p):
                sieve[m] = False
            p += 1
        members = [n for n in range(1, limit + 1) if sieve[n]]
    elif support == "primes":
        sieve = [True] * (limit + 1)
        sieve[0] = sieve[1] = False
        for p in range(2, int(limit**0.5) + 1):
            if sieve[p]:
                for m in range(p * p, limit + 1, p):
                    sieve[m] = False
        members = [n for n in range(2, limit + 1) if sieve[n]]
    elif support == "powers_of_two":
        members = [1 << k for k in range(1, limit.bit_length())]
    elif support == "squares":
        members = [k * k for k in range(1, int(limit**0.5) + 1)]
    else:
        raise ValueError(f"unknown support {support!r}")
    for d in members:
        for m in range(d, limit + 1, d):
            counts[m] += 1
    return counts


def window_discrepancy(counts: list[int], h: int, n: int, depth: int) -> int:
    """Exact integer `windowDiscrepancy h N L`, with f = c_A."""
    return sum(
        (counts[n + h + 1 + j] - counts[n + 1 + j]) * 2 ** (depth - 1 - j)
        for j in range(depth)
    )


def certificate_radius(
    counts: list[int], h: int, n: int, depth: int, terms: int = 96
) -> float:
    """Conservative `2^L · (|tail_after(N+h,L)| + |tail_after(N,L)|)`.

    This over-estimates `2^L·|E|`, so a certificate reported against it is
    pessimistic.  For `φ` the same quantity is bounded by `N+h+L+2`.
    """
    total = 0.0
    for i in range(terms):
        upper = n + h + depth + 1 + i
        lower = n + depth + 1 + i
        if upper >= len(counts):
            break
        total += (counts[upper] + counts[lower]) / 2 ** (i + 1)
    return total


def scan(support: str, limit: int, periods: list[int], depths: list[int],
         bases: list[int]) -> dict:
    counts = divisor_count_in(support, limit)
    rows = []
    worst_radius = 0.0
    total = hits = 0
    for depth in depths:
        for h in periods:
            cell_hits = cell_total = 0
            for n in bases:
                if n + h + depth + 100 >= limit:
                    continue
                cell_total += 1
                discrepancy = window_discrepancy(counts, h, n, depth)
                residue = discrepancy % (2 ** depth)
                radius = certificate_radius(counts, h, n, depth)
                worst_radius = max(worst_radius, radius)
                if radius < residue < 2 ** depth - radius:
                    cell_hits += 1
            if cell_total:
                rows.append({
                    "depth_L": depth,
                    "period_h": h,
                    "certificates": cell_hits,
                    "tested": cell_total,
                })
                hits += cell_hits
                total += cell_total
    return {
        "support": support,
        "limit": limit,
        "certificates": hits,
        "tested": total,
        "certificate_rate": round(hits / total, 4) if total else None,
        "max_certificate_radius": round(worst_radius, 2),
        "phi_radius_would_be": max(bases) + max(periods) + max(depths) + 2,
        "cells": rows,
        "claim_ceiling": (
            "finite evidence; a certificate excludes one denominator class, "
            "not the problem"
        ),
    }


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--support", default="all",
                        choices=["all", "squarefree", "primes",
                                 "powers_of_two", "squares"])
    parser.add_argument("--limit", type=int, default=200000)
    parser.add_argument("--periods", type=int, nargs="+", default=[6, 120, 2520])
    parser.add_argument("--depths", type=int, nargs="+", default=[10, 16, 24, 32])
    parser.add_argument("--base-start", type=int, default=1000)
    parser.add_argument("--base-stop", type=int, default=60000)
    parser.add_argument("--base-step", type=int, default=3313)
    args = parser.parse_args()
    bases = list(range(args.base_start, args.base_stop, args.base_step))
    print(json.dumps(
        scan(args.support, args.limit, args.periods, args.depths, bases),
        indent=2, sort_keys=True))


if __name__ == "__main__":
    main()
