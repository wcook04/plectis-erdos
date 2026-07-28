#!/usr/bin/env python3
# SPDX-FileCopyrightText: 2026 Will Cook
# SPDX-License-Identifier: Apache-2.0
"""Reproduce the #249 Farey-gap denominator bound, and measure what it costs.

The repository formalises a denominator exclusion for `S = sum phi(n)/2^n`: no
rational with denominator at most `79639646646701375323355774875831053` can
equal `S`.  That constant is easy to mistake for a measure of progress.  It is
not one, and this script is the receipt for saying so.

Two things are checked here, with no dependencies beyond the standard library
and no Lean build:

1.  **Correctness.**  The gap certificate is rebuilt from scratch -- totients by
    sieve, the committed residue `V_K`, and the minimal-denominator search --
    and must reproduce, exactly, the two constants hard-coded in
    `Erdos249257/GapFareyBound.lean`.  At small `K` the same answer is confirmed
    by brute force over every denominator.  This is an independent replication
    of the formalised numbers, not a restatement of them.

2.  **Scale.**  The window length `K` is a free parameter.  The bound grows like
    `2^(K/2)`, so the constant records how long the computation was run rather
    than anything about `S`.  The ladder printed at the end makes the cost
    explicit: a bound with thousands of digits is available in a fraction of a
    second.

The underlying argument is the classical Farey/mediant one.  A denominator `q`
fails the certificate exactly when some `m/q` lands in a short window of width
`(K+3)/2^K` around the truncated series, and two unimodular Farey neighbours
bracketing that window force any rational inside it to have denominator at
least `b + d`.  The improvement of this repository's bound over the classical
argument is zero; both are the same computation.

Usage:

    python3 scripts/check_farey_denominator_scaling.py            # verify + ladder
    python3 scripts/check_farey_denominator_scaling.py --verify   # constants only
    python3 scripts/check_farey_denominator_scaling.py --max-k 4000

Exits non-zero if either formalised constant fails to reproduce.
"""

from __future__ import annotations

import argparse
import sys
import time

# The two rungs formalised in Erdos249257/GapFareyBound.lean.
LEAN_RUNGS = {
    120: 248672326362367909,
    240: 79639646646701375323355774875831053,
}

# Committed residues for K = 120, cross-checked against the Lean source.
LEAN_V_120 = 977330308222705062435708544085600126
LEAN_VPRIME_120 = 351897687562210810468098516194744450

DEFAULT_LADDER = (120, 240, 500, 1000, 2000, 4000, 8000, 16000)


def totient_sieve(n: int) -> list[int]:
    """phi(0..n) by sieve."""
    phi = list(range(n + 1))
    for i in range(2, n + 1):
        if phi[i] == i:  # i is prime
            for j in range(i, n + 1, i):
                phi[j] -= phi[j] // i
    return phi


def committed_residue(K: int) -> tuple[int, int]:
    """V_K = (sum_{r=1}^{K} phi(1+r) * 2^(K-r)) mod 2^K, and V' = 2^K - V_K."""
    modulus = 1 << K
    phi = totient_sieve(K + 1)
    V = 0
    for r in range(1, K + 1):
        V += phi[1 + r] << (K - r)
    V %= modulus
    return V, modulus - V


def simplest_between(an: int, ad: int, bn: int, bd: int) -> tuple[int, int]:
    """Smallest-denominator p/q with an/ad <= p/q <= bn/bd, for 0 <= a <= b.

    The Stern-Brocot descent: take the integer part, emit it if the interval
    spans an integer, otherwise invert the fractional parts and recurse.
    """
    fa, fb = an // ad, bn // bd
    if fa < fb:
        return (fa + 1, 1)
    if fa * ad == an:
        return (fa, 1)
    p, q = simplest_between(bd, bn - fb * bd, ad, an - fa * ad)
    return (fa * p + q, p)


def first_failing_denominator(K: int) -> int:
    """Smallest q failing the (N=1, K) gap certificate.

    A denominator fails exactly when some m/q lies in
    `[(V' - H)/2^K, V'/2^K)` with `H = K + 3`, so the first failure is the
    minimal denominator of a rational in that window.
    """
    H = K + 3
    _, vprime = committed_residue(K)
    modulus = 1 << K
    if vprime - H <= 0:
        raise ValueError(f"K={K} is too small: the window straddles zero")
    p, q = simplest_between(vprime - H, modulus, vprime, modulus)
    if p * modulus >= vprime * q:
        raise AssertionError(f"K={K}: search landed on the open right endpoint")
    return q


def brute_first_failure(K: int, limit: int) -> int | None:
    """Independent brute force over every denominator, for small K."""
    H = K + 3
    V, _ = committed_residue(K)
    modulus = 1 << K
    for q in range(1, limit + 1):
        if (q * V) % modulus + q * H >= modulus:
            return q
    return None


def verify() -> bool:
    """Reproduce the formalised constants. Returns True on full agreement."""
    ok = True

    print("Brute force vs Stern-Brocot producer (small windows)")
    for K in (12, 16, 20, 24, 28, 32):
        brute = brute_first_failure(K, 200_000)
        found = first_failing_denominator(K)
        agree = brute == found
        ok &= agree
        print(f"  K={K:<3d} first failure {found:<8d} {'agrees' if agree else 'DISAGREES'}")

    print()
    print("Recomputed bounds vs Erdos249257/GapFareyBound.lean")
    for K, expected in sorted(LEAN_RUNGS.items()):
        start = time.perf_counter()
        bound = first_failing_denominator(K) - 1
        elapsed = time.perf_counter() - start
        match = bound == expected
        ok &= match
        print(f"  K={K}: {'reproduces' if match else 'MISMATCH'} the formalised "
              f"constant [{elapsed:.3f}s]")
        if not match:
            print(f"    recomputed {bound}")
            print(f"    formalised {expected}")

    V, vprime = committed_residue(120)
    residues_ok = (V == LEAN_V_120 and vprime == LEAN_VPRIME_120
                   and V + vprime == 1 << 120)
    ok &= residues_ok
    print(f"  K=120 committed residues V, V' and V + V' = 2^K: "
          f"{'match' if residues_ok else 'MISMATCH'}")
    return ok


def ladder(max_k: int) -> None:
    """Show how the bound and its cost scale with the window length."""
    print()
    print("The window length is a free parameter")
    print(f"  {'K':>6}  {'digits in bound':>16}  {'seconds':>9}")
    sys.setrecursionlimit(max(10_000, max_k * 8))
    for K in DEFAULT_LADDER:
        if K > max_k:
            break
        start = time.perf_counter()
        bound = first_failing_denominator(K) - 1
        elapsed = time.perf_counter() - start
        digits = int(bound.bit_length() * 0.30102999566398114) + 1
        print(f"  {K:>6}  {digits:>16,}  {elapsed:>9.2f}")
    print()
    print("  The bound grows like 2^(K/2) for a cost that stays negligible, so it")
    print("  measures how long the computation was run, not progress on Erdos #249.")
    print("  Erdos #249 remains open; this exclusion is finite at every K.")


def main() -> int:
    parser = argparse.ArgumentParser(
        description="Reproduce and cost the #249 Farey-gap denominator bound.")
    parser.add_argument("--verify", action="store_true",
                        help="only reproduce the formalised constants")
    parser.add_argument("--max-k", type=int, default=16000,
                        help="largest window length in the ladder (default: 16000)")
    args = parser.parse_args()

    ok = verify()
    if not args.verify:
        ladder(args.max_k)

    if not ok:
        print()
        print("FAIL: a formalised constant did not reproduce.", file=sys.stderr)
        return 1
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
