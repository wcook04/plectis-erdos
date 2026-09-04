#!/usr/bin/env python3
"""Erdos 251: the bounded-perturbation countermodel, in exact arithmetic.

Setup (zero-based, matching PrimeGapDyadicTail.lean): g_n = p_{n+1} - p_n with
p_0 = 2, and S = sum_{n>=0} g_n / 2^{n+1}.  For a positive integer M and a
rational r with S < r < S + M put D = (r - S)/M in (0, 1) and let delta_n be the
binary digits of D, delta_n = floor(2^{n+1} D) - 2 floor(2^n D) in {0, 1}.  Then

    g'_n := g_n + M * delta_n      satisfies      sum g'_n / 2^{n+1} = r.

So the actual prime gaps, moved by at most M at every index (and, for M = 2q,
without changing any residue modulo q), have a rational dyadic sum.  Every gap
theorem that is invariant under bounded perturbation (Baker-Harman-Pintz,
Zhang-Maynard bounded gaps, Ford-Green-Konyagin-Maynard-Tao large gaps,
Goldston-Pintz-Yildirim, the prime number theorem, equidistribution modulo any
fixed q) therefore cannot, by itself, prove irrationality.

This probe checks the construction with exact rationals:
  1. the digits delta_n lie in {0,1} and telescope to floor(2^N D)/2^N;
  2. the perturbed partial sums bracket r exactly with the same tail width
     as the unperturbed bracket; sum (g_n + M delta_n)/2^{n+1} over n < N
     equals the unperturbed partial sum plus M floor(2^N D)/2^N;
  3. the perturbed gaps satisfy g_n <= g'_n <= g_n + M, are even beyond n=0
     for even M, keep residues mod M/2, and the perturbed primes satisfy
     p'_n - p_n <= M n;
  4. the digit density of D over the certified prefix is reported (nothing is
     claimed about it);
  5. the sparse-support variant: for any strictly increasing index sequence
     (n_i), the digits of D can be packed into blocks so the perturbation is
     supported on {n_i} with size below 2^{n_{i+1}-n_i}; checked for
     n_i = m*i.
Falsifiers: any digit outside {0,1}; any perturbed partial sum outside the
bracket; any residue change mod M/2; a block coefficient at or above its bound.

Bracket: S is bracketed by the exact prefix through index N with tail bounded
by the Lean-checked p_i <= 1250 (i+1)^4 (prime0_le_polynomial); the digits of
D are certified only where the lower and upper brackets agree.
"""
from __future__ import annotations

import argparse
import json
import math
import sys
sys.set_int_max_str_digits(0)
from fractions import Fraction
from pathlib import Path


def primes_below(limit: int) -> list[int]:
    sieve = bytearray([1]) * limit
    sieve[0] = sieve[1] = 0
    for i in range(2, int(limit ** 0.5) + 1):
        if sieve[i]:
            sieve[i * i::i] = bytearray(len(sieve[i * i::i]))
    return [i for i, v in enumerate(sieve) if v]


def tail_bound(N: int) -> Fraction:
    """Rigorous upper bound on sum_{i>=N} p_i / 2^{i+1} from p_i <= 1250 (i+1)^4.

    For i >= N >= 40 the ratio of consecutive terms is ((i+2)/(i+1))^4 / 2 <= 0.6,
    so the tail is at most the first term over (1 - 0.6) = 2.5 times the first term.
    """
    assert N >= 40
    first = Fraction(1250 * (N + 1) ** 4, 2 ** (N + 1))
    return first * Fraction(5, 2)


def floor_digits(D_lo: Fraction, D_hi: Fraction, count: int) -> tuple[list[int], int]:
    """Binary digits of D certified where floor(2^{n+1} D_lo) == floor(2^{n+1} D_hi)."""
    digits = []
    prev_lo = math.floor(D_lo)
    prev_hi = math.floor(D_hi)
    assert prev_lo == prev_hi == 0
    for n in range(count):
        f_lo = math.floor(D_lo * 2 ** (n + 1))
        f_hi = math.floor(D_hi * 2 ** (n + 1))
        if f_lo != f_hi:
            return digits, n
        d = f_lo - 2 * prev_lo
        digits.append(d)
        prev_lo = f_lo
        prev_hi = f_hi
    return digits, count


def main() -> int:
    ap = argparse.ArgumentParser()
    ap.add_argument("--limit", type=int, default=200000, help="sieve limit for primes")
    ap.add_argument("--M", type=int, default=2)
    ap.add_argument("--r", type=str, default="2", help="rational target r as a/b")
    ap.add_argument("--block", type=int, default=8, help="block length for the sparse variant")
    ap.add_argument("--json", action="store_true")
    args = ap.parse_args()

    M = args.M
    r = Fraction(args.r)
    primes = primes_below(args.limit)
    gaps = [primes[i + 1] - primes[i] for i in range(len(primes) - 1)]
    N = len(gaps)

    # exact bracket for the gap series S = sum g_n / 2^{n+1} = (prime series) - 2
    prefix_gap = sum(Fraction(g, 2 ** (n + 1)) for n, g in enumerate(gaps))
    # tail of the gap series: sum_{n>=N} g_n/2^{n+1} = 2 * tail_prime(N+1) - p_N / 2^{N}... use the
    # crude bound g_n <= p_{n+1} <= 1250 (n+2)^4, i.e. the prime tail bound shifted by one index.
    tail_gap = 2 * tail_bound(N + 1)
    S_lo, S_hi = prefix_gap, prefix_gap + tail_gap
    if not (S_lo < r < S_lo + M):
        print(f"FAIL: r={r} not in (S, S+M) with S in [{float(S_lo)}, {float(S_hi)}]")
        return 1
    D_lo = (r - S_hi) / M
    D_hi = (r - S_lo) / M
    if not (0 < D_lo and D_hi < 1):
        print("FAIL: D not inside (0,1) on the whole bracket")
        return 1

    digits, certified = floor_digits(D_lo, D_hi, N)
    if any(d not in (0, 1) for d in digits):
        print("FAIL: digit outside {0,1}")
        return 1

    # falsifier 1: telescoping identity at every certified prefix length
    for K in (1, 2, 10, 100, min(1000, certified), certified):
        lhs = sum(Fraction(d, 2 ** (n + 1)) for n, d in enumerate(digits[:K]))
        rhs = Fraction(math.floor(D_lo * 2 ** K), 2 ** K)
        if lhs != rhs:
            print(f"FAIL: telescoping identity broken at K={K}")
            return 1

    # falsifier 2: perturbed partial sums bracket r
    pert_gaps = [g + M * d for g, d in zip(gaps[:certified], digits)]
    pert_prefix = sum(Fraction(g, 2 ** (n + 1)) for n, g in enumerate(pert_gaps))
    unpert_prefix = sum(Fraction(g, 2 ** (n + 1)) for n, g in enumerate(gaps[:certified]))
    if pert_prefix != unpert_prefix + M * Fraction(math.floor(D_lo * 2 ** certified), 2 ** certified):
        print("FAIL: perturbed prefix identity")
        return 1
    # r - pert_prefix must be the remaining perturbed tail: between the unperturbed
    # tail and unperturbed tail + M * 2^{-certified}
    rem = r - pert_prefix
    unpert_tail_lo = S_lo - unpert_prefix
    unpert_tail_hi = S_hi - unpert_prefix
    if not (unpert_tail_lo <= rem <= unpert_tail_hi + Fraction(M, 2 ** certified)):
        print("FAIL: remainder outside the perturbed tail bracket")
        return 1

    # falsifier 3: pointwise and residue invariants
    for n, (g, gp) in enumerate(zip(gaps[:certified], pert_gaps)):
        if not (g <= gp <= g + M):
            print(f"FAIL: perturbation size at n={n}")
            return 1
        if M % 2 == 0 and n >= 1 and gp % 2 != 0:
            print(f"FAIL: parity at n={n}")
            return 1
        if M % 2 == 0 and (gp - g) % (M // 2) != 0:
            print(f"FAIL: residue mod M/2 at n={n}")
            return 1
    pert_primes = [2]
    for gp in pert_gaps:
        pert_primes.append(pert_primes[-1] + gp)
    max_drift = max(pp - p for pp, p in zip(pert_primes, primes))
    if max_drift > M * certified:
        print("FAIL: prime drift bound")
        return 1

    ones = sum(digits)
    # sparse-support variant: blocks of length m, coefficient c_i = digits of D in block i
    m = args.block
    nblocks = certified // m
    block_coeffs = []
    for i in range(nblocks):
        c = 0
        for j in range(m):
            c = 2 * c + digits[i * m + j]
        block_coeffs.append(c)
        if not (0 <= c < 2 ** m):
            print("FAIL: block coefficient bound")
            return 1
    # sum_i c_i / 2^{(i+1) m} must equal the digit prefix sum through nblocks*m
    lhs = sum(Fraction(c, 2 ** ((i + 1) * m)) for i, c in enumerate(block_coeffs))
    rhs = sum(Fraction(d, 2 ** (n + 1)) for n, d in enumerate(digits[: nblocks * m]))
    if lhs != rhs:
        print("FAIL: block packing identity")
        return 1

    # BHP-type sanity on the perturbed gaps in the finite window (not a theorem, a check)
    bhp_ok = all(gp <= (pert_primes[n]) ** 0.525 + M for n, gp in enumerate(pert_gaps) if n > 100)
    bounded_gap_hits = sum(1 for gp in pert_gaps[1:] if gp <= 2 + M)

    receipt = {
        "probe_id": "erdos251_bounded_perturbation_countermodel",
        "sieve_limit": args.limit,
        "gap_count": N,
        "M": M,
        "r": str(r),
        "S_bracket_bits": [S_lo.denominator.bit_length(), S_hi.denominator.bit_length()],
        "S_bracket_float": [float(S_lo), float(S_hi)],
        "D_bracket_float": [float(D_lo), float(D_hi)],
        "certified_digits": certified,
        "certified_digit_ones": ones,
        "digit_density_of_ones": ones / certified if certified else None,
        "first_64_digits": "".join(str(d) for d in digits[:64]),
        "max_prime_drift": max_drift,
        "perturbed_partial_sum_float": float(pert_prefix),
        "remainder_float": float(rem),
        "block_length": m,
        "block_count": nblocks,
        "block_coeff_max": max(block_coeffs) if block_coeffs else None,
        "finite_window_bhp_plus_M": bhp_ok,
        "perturbed_gaps_at_most_2_plus_M": bounded_gap_hits,
        "falsifiers_passed": [
            "digits_in_01_and_telescoping",
            "perturbed_prefix_brackets_r",
            "pointwise_size_parity_residue_and_drift",
            "block_packing_identity_and_bound",
        ],
        "claim_boundary": "Finite exact check of an elementary construction; the theorem itself is "
                          "BoundedPerturbationCountermodel.lean. Says nothing about irrationality "
                          "of the actual prime-gap series.",
    }
    out = Path("state/formal_math/probes/erdos251_bounded_perturbation_receipt.json")
    if out.parent.exists():
        out.write_text(json.dumps(receipt, indent=1, ensure_ascii=False) + "\n")
        receipt["receipt_path"] = str(out)
    if args.json:
        print(json.dumps(receipt, indent=1, ensure_ascii=False))
    else:
        for k, v in receipt.items():
            print(f"{k}: {v}")
    print("OK: all falsifiers passed")
    return 0


if __name__ == "__main__":
    sys.exit(main())
