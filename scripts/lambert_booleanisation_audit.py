#!/usr/bin/env python3
"""Exact diagnostic for the Möbius-sign Booleanisation proposal.

All comparisons use fractions.  This program is a computation receipt only;
the decisive no-go is the Lean injectivity theorem cited in the companion note.
"""

from __future__ import annotations

import argparse
import hashlib
import json
from fractions import Fraction


def mobius_up_to(limit: int) -> list[int]:
    """Return μ(0),...,μ(limit) by an exact linear sieve."""
    mu = [0] * (limit + 1)
    mu[1] = 1
    primes: list[int] = []
    is_composite = [False] * (limit + 1)
    for n in range(2, limit + 1):
        if not is_composite[n]:
            primes.append(n)
            mu[n] = -1
        for p in primes:
            if n * p > limit:
                break
            is_composite[n * p] = True
            if n % p == 0:
                mu[n * p] = 0
                break
            mu[n * p] = -mu[n]
    return mu


def weight(n: int) -> Fraction:
    return Fraction(1, (1 << n) - 1)


def frac_receipt(x: Fraction) -> object:
    """Keep large exact fractions reproducible without dumping megabyte JSON."""
    if x.numerator.bit_length() <= 2048 and x.denominator.bit_length() <= 2048:
        return f"{x.numerator}/{x.denominator}"
    num = x.numerator
    payload = (
        (b"-" if num < 0 else b"+")
        + abs(num).to_bytes(max(1, (abs(num).bit_length() + 7) // 8), "big")
        + b"/"
        + x.denominator.to_bytes(max(1, (x.denominator.bit_length() + 7) // 8), "big")
    )
    return {
        "exact_fraction_sha256": hashlib.sha256(payload).hexdigest(),
        "numerator_bits": x.numerator.bit_length(),
        "denominator_bits": x.denominator.bit_length(),
    }


def restricted_greedy_prefix(mu: list[int], horizon: int, depth: int) -> dict[str, object]:
    """Use P's exact finite interval to force N-restricted greedy decisions.

    P lies between its positive-sign partial sum through ``horizon`` and that
    sum plus the full geometric Mersenne tail after the horizon.  A decision is
    reported only when it is forced throughout that rational interval.
    """
    target_lo = sum((weight(n) for n in range(2, horizon + 1) if mu[n] == 1), Fraction())
    target_hi = target_lo + Fraction(1, 1 << (horizon - 1))
    chosen: list[int] = []
    residual_lo, residual_hi = target_lo, target_hi
    ambiguous: int | None = None
    for n in range(2, depth + 1):
        if mu[n] != -1:
            continue
        coin = weight(n)
        if residual_lo >= coin:
            chosen.append(n)
            residual_lo -= coin
            residual_hi -= coin
        elif residual_hi < coin:
            continue
        else:
            ambiguous = n
            break
    allowed_tail_upper = sum(
        (weight(n) for n in range(depth + 1, horizon + 1) if mu[n] == -1),
        Fraction(),
    ) + Fraction(1, 1 << (horizon - 1))
    return {
        "decision_depth": depth,
        "target_interval": [frac_receipt(target_lo), frac_receipt(target_hi)],
        "forced_chosen_negative_indices": chosen,
        "first_ambiguous_negative_index": ambiguous,
        "residual_interval_at_stop": [frac_receipt(residual_lo), frac_receipt(residual_hi)],
        "allowed_negative_tail_upper_after_depth": frac_receipt(allowed_tail_upper),
        "fatal_gap_certified": ambiguous is None and residual_lo > allowed_tail_upper,
    }


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--horizon", type=int, default=256)
    parser.add_argument("--depth", type=int, default=128)
    args = parser.parse_args()
    if args.horizon < 8 or not 2 <= args.depth <= args.horizon:
        raise SystemExit("--horizon must be at least 8")

    mu = mobius_up_to(args.horizon)
    positive = [n for n in range(2, args.horizon + 1) if mu[n] == 1]
    negative = [n for n in range(2, args.horizon + 1) if mu[n] == -1]
    p_sum = sum((weight(n) for n in positive), Fraction())
    n_sum = sum((weight(n) for n in negative), Fraction())
    tail = Fraction(1, 1 << (args.horizon - 1))
    report = {
        "method": "exact Fraction arithmetic; no floating point",
        "horizon": args.horizon,
        "positive_indices_prefix": positive[:32],
        "negative_indices_prefix": negative[:32],
        "mu_6": mu[6],
        "sign_classes_disjoint_through_horizon": not (set(positive) & set(negative)),
        "positive_partial_sum": frac_receipt(p_sum),
        "negative_partial_sum": frac_receipt(n_sum),
        "universal_tail_upper_after_horizon": frac_receipt(tail),
        "positive_total_enclosure": [frac_receipt(p_sum), frac_receipt(p_sum + tail)],
        "negative_total_enclosure": [frac_receipt(n_sum), frac_receipt(n_sum + tail)],
        "restricted_negative_greedy_diagnostic": restricted_greedy_prefix(mu, args.horizon, args.depth),
        "logical_status": (
            "No greedy outcome can certify P as a negative-sign subseries: "
            "the global Mersenne coding is injective and P itself is its "
            "Boolean code. This computation only records exact finite data."
        ),
    }
    print(json.dumps(report, indent=2, sort_keys=True))


if __name__ == "__main__":
    main()
