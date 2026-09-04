#!/usr/bin/env python3
"""Erdos 68: the prime-grid producer is bounded by the carry certificate's depth.

Upstream analytic state
-----------------------
`cofinal_prime_grid_nonterminality` is a priority-1 producer:

> For cofinally many primes `p`, prove that the least `(p-1)!^(-1)` grid point
> strictly above `H_p` is not equal to the target series `S`.

Two finite denominator exclusions landed in this packet on the same day, from
unrelated routes:

* `kempner_index_denominator_exclusion` -- any displayed denominator `q`
  satisfies `q` not dividing `299999!`;
* `certified_continued_fraction_denominator_exclusion` -- `q > 2^39991`, above
  `10^12039`.

Probe
-----
The producer is an instance of "S is not this explicit rational". If `S = G_p`
then `S = k/(p-1)!`, so its reduced denominator `q` divides `(p-1)!`. Each
exclusion therefore discharges the producer over an explicit initial range:

* Kempner: for `p - 1 <= 299999`, `(p-1)!` divides `299999!`, so `q | (p-1)!`
  would give `q | 299999!`, which is excluded. Hence `G_p != S`.
* Continued fraction: for `(p-1)! <= 2^39991`, `q | (p-1)!` would force
  `q <= (p-1)! <= 2^39991`, contradicting `q > 2^39991`.

This computes where each range ends and which is operative.

The consequence is not just a number. The Kempner exclusion comes from a single
certified non-unit carry at index `m`, so the discharge extends to `p <= m`
whenever the GMP carry certificate is run to depth `m`. **The producer is not an
independent open problem; it is a corollary of the carry certificate's depth.**
Extending that certificate extends the producer mechanically, and what remains
genuinely open is only the cofinal tail.

Predeclared falsifier
---------------------
If the continued-fraction range had exceeded the Kempner range, the operative
bound would be the one with no dependence on the carry certificate, and the
linkage claimed above would be wrong.

Claim boundary
--------------
A derivation from two landed exclusions plus the arithmetic of where their
ranges end. It discharges an explicit initial range of a cofinal producer; it
does not prove the producer, and Erdos 68 remains open.
"""

from __future__ import annotations

import argparse
import json
import math

KEMPNER_INDEX = 299999          # q does not divide 299999!
CF_BOUND_BITS = 39991           # q > 2^39991


def largest_prime_at_most(limit: int) -> int:
    if limit < 2:
        return 0
    sieve = bytearray([1]) * (limit + 1)
    sieve[0] = sieve[1] = 0
    for value in range(2, int(limit ** 0.5) + 1):
        if sieve[value]:
            sieve[value * value :: value] = bytearray(
                len(sieve[value * value :: value]))
    for candidate in range(limit, 1, -1):
        if sieve[candidate]:
            return candidate
    return 0


def cf_range() -> tuple[int, int]:
    """Largest `n` with `n! <= 2^CF_BOUND_BITS`, and its decimal size."""
    target = CF_BOUND_BITS * math.log(2)
    n, total = 1, 0.0
    while True:
        n += 1
        total += math.log(n)
        if total > target:
            previous = total - math.log(n)
            return n - 1, int(previous / math.log(10))


def run() -> dict:
    cf_index, cf_digits = cf_range()
    cf_prime_limit = cf_index + 1
    kempner_prime_limit = KEMPNER_INDEX + 1
    operative = ("kempner" if kempner_prime_limit > cf_prime_limit
                 else "continued_fraction")
    return {
        "producer": "cofinal_prime_grid_nonterminality",
        "reduction": ("S = G_p forces S = k/(p-1)!, so the reduced denominator q "
                      "divides (p-1)!"),
        "kempner": {
            "exclusion": f"q does not divide {KEMPNER_INDEX}!",
            "discharges_primes_up_to": kempner_prime_limit,
            "largest_prime_discharged": largest_prime_at_most(kempner_prime_limit),
            "reason": (f"for p-1 <= {KEMPNER_INDEX}, (p-1)! divides {KEMPNER_INDEX}!, "
                       f"so q | (p-1)! would give q | {KEMPNER_INDEX}!"),
        },
        "continued_fraction": {
            "exclusion": f"q > 2^{CF_BOUND_BITS}",
            "largest_factorial_index_within_bound": cf_index,
            "that_factorial_decimal_digits": cf_digits,
            "discharges_primes_up_to": cf_prime_limit,
            "largest_prime_discharged": largest_prime_at_most(cf_prime_limit),
            "reason": (f"for (p-1)! <= 2^{CF_BOUND_BITS}, q | (p-1)! would force "
                       f"q <= 2^{CF_BOUND_BITS}"),
        },
        "operative_bound": operative,
        "linkage": (
            "The Kempner exclusion comes from a single certified non-unit carry at "
            "index m, so the discharge extends to p <= m whenever the GMP carry "
            "certificate is run to depth m. The producer is a corollary of the carry "
            "certificate's depth rather than an independent open problem; extending "
            "the certificate extends it mechanically, and only the cofinal tail is "
            "genuinely open."),
    }


def main() -> int:
    argparse.ArgumentParser().parse_args()
    print(json.dumps(run(), indent=2, default=str))
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
