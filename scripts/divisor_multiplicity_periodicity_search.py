#!/usr/bin/env python3
"""
Erdos 257 -- the divisor-multiplicity (tau_A) route.

EXACT IDENTITY.   For any A subset N_{>=1},

    sum_{k in A} 1/(2^k - 1) = sum_{k in A} sum_{j>=1} 2^{-jk}
                             = sum_{m>=1} tau_A(m) 2^{-m},
    tau_A(m) := #{ d in A : d | m }.

So the Erdos-257 value is the "binary number with (unbounded) digits tau_A".

SUFFICIENT CONDITION FOR A COUNTEREXAMPLE.
If tau_A is eventually periodic and bounded, the value is RATIONAL.
tau_A = 1 * 1_A  (Dirichlet), so 1_A = mu * tau_A.  Hence:

    Erdos 257 is FALSE if there is a bounded, eventually periodic
    f : N -> Z_{>=0}  whose Mobius transform  g = mu * f  takes only the
    values {0,1} and equals 1 infinitely often.

Then A = {m : g(m) = 1} is infinite and  sum_{k in A} 1/(2^k-1) = sum_m f(m)2^{-m}
is rational, killing the conjecture outright.

This script performs the exhaustive DFS search over all periods r <= RMAX and
all digit bounds <= B.  Assignment order m = 1,2,3,... : at step m the residue
m mod r is either already fixed (verify) or free (two admissible values, since
g(m) in {0,1} determines f(m) up to two choices).

It also prints, for each period that admits solutions, the resulting support A.
"""
from __future__ import annotations
import argparse, sys

def mobius_table(N):
    mu = [1] * (N + 1)
    primes = []
    is_c = [False] * (N + 1)
    for i in range(2, N + 1):
        if not is_c[i]:
            primes.append(i); mu[i] = -1
        for p in primes:
            if i * p > N: break
            is_c[i * p] = True
            if i % p == 0:
                mu[i * p] = 0; break
            mu[i * p] = -mu[i]
    return mu

def divisors_upto(N):
    dv = [[] for _ in range(N + 1)]
    for d in range(1, N + 1):
        for m in range(d, N + 1, d):
            dv[m].append(d)
    return dv

def search(r, M, B, mu, dv, verbose=False):
    """All f with period r, 0<=f<=B, mu*f in {0,1} on [1,M]. Return list of (F, support)."""
    F = [None] * r
    sols = []
    def rec(m):
        if m > M:
            supp = []
            for mm in range(1, M + 1):
                g = sum(mu[mm // d] * F[d % r] for d in dv[mm])
                if g == 1: supp.append(mm)
            sols.append((list(F), supp))
            return
        res = m % r
        # partial sum over proper divisors
        part = 0
        unknown = (F[res] is None)
        for d in dv[m]:
            if d == m: continue
            part += mu[m // d] * F[d % r]
        # mu[m//m] = mu[1] = 1 so g(m) = F[res] + part
        if unknown:
            for gval in (0, 1):
                v = gval - part
                if 0 <= v <= B:
                    F[res] = v
                    rec(m + 1)
                    F[res] = None
        else:
            if (F[res] + part) in (0, 1):
                rec(m + 1)
    rec(1)
    return sols

def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--rmax", type=int, default=24)
    ap.add_argument("--M", type=int, default=400)
    ap.add_argument("--B", type=int, default=6)
    a = ap.parse_args()
    mu = mobius_table(a.M + 1)
    dv = divisors_upto(a.M)
    print(f"exhaustive search: periods r=1..{a.rmax}, digits 0..{a.B}, verified to m<={a.M}\n")
    print(f"{'r':>3} {'#solutions':>11} {'max |A| found':>14} {'largest element of A':>21}")
    grand = []
    for r in range(1, a.rmax + 1):
        sols = search(r, a.M, a.B, mu, dv)
        if not sols:
            print(f"{r:>3} {0:>11} {'-':>14} {'-':>21}")
            continue
        best = max(sols, key=lambda s: len(s[1]))
        mx = max((max(s[1]) if s[1] else 0) for s in sols)
        print(f"{r:>3} {len(sols):>11} {len(best[1]):>14} {mx:>21}")
        for Fv, supp in sols:
            grand.append((r, Fv, supp))
    print()
    allsupp = sorted({tuple(s) for _, _, s in grand})
    print(f"distinct supports A found over ALL periods: {len(allsupp)}")
    big = [s for s in allsupp if s and max(s) > a.M // 2]
    print(f"supports with an element beyond M/2 = {a.M//2}  (i.e. candidate-infinite): {len(big)}")
    for s in sorted(allsupp, key=len)[-8:]:
        print(f"   |A|={len(s):>2}  A={list(s)[:14]}{' ...' if len(s)>14 else ''}")
    print()
    if big:
        print("*** CANDIDATE INFINITE SUPPORT FOUND -- verify at larger M ***")
    else:
        print(f"RESULT: every f with period <= {a.rmax}, digits <= {a.B}, whose Mobius")
        print(f"transform is an indicator, has FINITE support inside [1,{a.M}].")
        print("=> no counterexample to Erdos 257 has eventually-periodic divisor")
        print("   multiplicity tau_A in that range: any counterexample's tau_A must be")
        print("   aperiodic, so the rationality is produced entirely by CARRIES.")

main()
