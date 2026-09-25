#!/usr/bin/env python3
# SPDX-FileCopyrightText: 2026 Will Cook
# SPDX-License-Identifier: Apache-2.0
"""Decide sparse identities among totient-kernel sections at any integer base.

For example::

    python3 scripts/totient_kernel_sparse_normal_form.py --base 12 \
      --term 8:29859840:1 --term 2:10:-1990656

Each term is LEVEL:RESIDUE:INTEGER_COEFFICIENT and represents that integer
times phi(base**LEVEL * n + RESIDUE), with phi(0) = 0. The exact identity
decision follows the all-base integral basis in the #249 short paper,
Theorem "A basis through each finite level" and its integral-coordinate
corollary. This Python implementation is checked against that result; it is
not itself a Lean-verified executable program. An optional bounded witness
search never changes the exact identity decision.
"""

from __future__ import annotations

import argparse
import json
from math import isqrt

Channel = tuple[int, int]


def prime_divisors(n: int) -> tuple[int, ...]:
    """Return the distinct prime divisors of a positive integer."""
    primes: list[int] = []
    divisor = 2
    while divisor <= isqrt(n):
        if n % divisor == 0:
            primes.append(divisor)
            while n % divisor == 0:
                n //= divisor
        divisor += 1 if divisor == 2 else 2
    if n > 1:
        primes.append(n)
    return tuple(primes)


def reduce_channel(base: int, channel: Channel, primes: tuple[int, ...]) -> tuple[Channel, int]:
    """Return its retained coordinate and exact nonnegative multiplier."""
    level, residue = channel
    if level < 0 or residue < 0 or residue >= base**level:
        raise ValueError(f"channel {level}:{residue} lies outside its level")
    if level == 0:
        return (0, 0), 1
    if residue == 0:
        return (1, 0), base ** (level - 1)
    removed = 0
    unit = residue
    while unit % base == 0:
        unit //= base
        removed += 1
    if removed == 0:
        return channel, 1
    multiplier = base**removed
    for prime in primes:
        if unit % prime != 0:
            if multiplier % prime != 0:
                raise ArithmeticError("totient reduction multiplier lost an exact prime factor")
            multiplier = multiplier // prime * (prime - 1)
    return (level - removed, unit), multiplier


def totient(n: int) -> int:
    """Euler's totient with the paper's convention phi(0) = 0."""
    if n == 0:
        return 0
    result = n
    for prime in prime_divisors(n):
        result -= result // prime
    return result


def normalize(
    base: int,
    terms: dict[Channel, int],
    *,
    witness_budget: int = 0,
) -> dict[str, object]:
    """Decide identity from sparse integral coordinates; optionally search for a witness."""
    if base < 2:
        raise ValueError("base must be at least 2")
    if witness_budget < 0:
        raise ValueError("witness budget must be nonnegative")
    primes = prime_divisors(base)
    coordinates: dict[Channel, int] = {}
    relations: dict[Channel, int] = {}
    for channel, coefficient in terms.items():
        retained, multiplier = reduce_channel(base, channel, primes)
        coordinates[retained] = coordinates.get(retained, 0) + coefficient * multiplier
        if retained != channel:
            relations[channel] = coefficient
    coordinates = {channel: coefficient for channel, coefficient in coordinates.items() if coefficient}
    relations = {channel: coefficient for channel, coefficient in relations.items() if coefficient}
    identity = not coordinates
    witness = None
    if identity:
        witness_status = "not_applicable"
    elif witness_budget == 0:
        witness_status = "not_requested"
    else:
        witness_status = "not_found_within_budget"
        for n in range(witness_budget):
            exact_value = sum(
                coefficient * totient(base**level * n + residue)
                for (level, residue), coefficient in terms.items()
            )
            if exact_value:
                witness = {"n": n, "exact_value": exact_value}
                witness_status = "found"
                break

    def rows(items: dict[Channel, int]) -> list[dict[str, int]]:
        return [
            {"level": channel[0], "residue": channel[1], "coefficient": coefficient}
            for channel, coefficient in sorted(items.items())
        ]

    return {
        "base": base,
        "family": "F_j,r(n) = phi(base**j * n + r), phi(0) = 0",
        "identity": identity,
        "canonical_coefficients": rows(coordinates),
        "relation_coefficients": rows(relations),
        "counterexample": witness,
        "witness_status": witness_status,
        "witness_budget": witness_budget,
        "authority": "paper/249/erdos-249-binary-totient-series.tex, all-base basis and integral-coordinate corollary",
    }


def parse_term(raw: str) -> tuple[Channel, int]:
    try:
        level, residue, coefficient = (int(part) for part in raw.split(":"))
    except ValueError as exc:
        raise argparse.ArgumentTypeError("term must be LEVEL:RESIDUE:INTEGER_COEFFICIENT") from exc
    return (level, residue), coefficient


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__.splitlines()[0])
    parser.add_argument("--base", type=int, required=True)
    parser.add_argument("--term", type=parse_term, action="append", required=True)
    parser.add_argument("--witness-budget", type=int, default=0, metavar="COUNT")
    args = parser.parse_args()
    terms: dict[Channel, int] = {}
    for channel, coefficient in args.term:
        terms[channel] = terms.get(channel, 0) + coefficient
    try:
        result = normalize(args.base, terms, witness_budget=args.witness_budget)
    except ValueError as exc:
        parser.error(str(exc))
    print(json.dumps(result, indent=2))
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
