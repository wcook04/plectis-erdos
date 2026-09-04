#!/usr/bin/env python3
"""Exact endpoint prime-pole scan for Erdős #68.

For every prime q up to the requested bound, compute n! modulo q^3 for
2 <= n < q.  At the largest observed q-adic exponent e of n!-1, form

    C_q = sum (((n!-1)/q^e) mod q)^(-1) mod q.

The finite prime-pole theorem says C_q is the exact obstruction to survival of
the complete q^e factor in the reduced factorial-gap prefix denominator.  This
probe is finite evidence and a falsifier for the formal statement; it does not
infer anything q-adically about the infinite real tail.
"""

from __future__ import annotations

import argparse
import json
from dataclasses import dataclass


def primes_through(limit: int) -> list[int]:
    sieve = bytearray(b"\x01") * (limit + 1)
    if limit >= 0:
        sieve[0] = 0
    if limit >= 1:
        sieve[1] = 0
    for p in range(2, int(limit**0.5) + 1):
        if sieve[p]:
            sieve[p * p : limit + 1 : p] = b"\x00" * (((limit - p * p) // p) + 1)
    return [p for p in range(2, limit + 1) if sieve[p]]


@dataclass(frozen=True)
class Hit:
    n: int
    exponent: int
    cofactor_mod_q: int


def endpoint_prime_pole(q: int) -> dict:
    modulus = q**3
    fact = 1
    hits: list[Hit] = []
    maximum_exponent = 0
    for n in range(2, q):
        fact = (fact * n) % modulus
        difference = (fact - 1) % modulus
        if difference % q:
            continue
        if difference % (q * q):
            exponent = 1
            cofactor = (difference // q) % q
        elif difference:
            exponent = 2
            cofactor = (difference // (q * q)) % q
        else:
            raise RuntimeError(
                f"q={q}, n={n}: valuation at least three; increase the modular precision"
            )
        maximum_exponent = max(maximum_exponent, exponent)
        hits.append(Hit(n, exponent, cofactor))

    maximal = [hit for hit in hits if hit.exponent == maximum_exponent]
    inverses = [pow(hit.cofactor_mod_q, -1, q) for hit in maximal]
    residue = sum(inverses) % q
    return {
        "q": q,
        "maximum_exponent": maximum_exponent,
        "maximal_hits": [hit.n for hit in maximal],
        "cofactors_mod_q": [hit.cofactor_mod_q for hit in maximal],
        "inverse_cofactors_mod_q": inverses,
        "principal_residue_mod_q": residue,
        "full_prime_power_survives": residue != 0,
    }


def run(max_prime: int) -> dict:
    rows = [endpoint_prime_pole(q) for q in primes_through(max_prime) if q >= 5]
    cancellations = [row for row in rows if row["principal_residue_mod_q"] == 0]
    q139 = endpoint_prime_pole(139)
    q2593 = endpoint_prime_pole(2593)
    falsifiers = {
        "q=139 exact maximal hits": q139["maximal_hits"] == [69, 122, 137],
        "q=139 exact cofactors": q139["cofactors_mod_q"] == [6, 49, 73],
        "q=139 principal residue cancels": q139["principal_residue_mod_q"] == 0,
        "q=2593 exact maximal hits": q2593["maximal_hits"] == [349, 2243, 2591],
        "q=2593 exact cofactors": q2593["cofactors_mod_q"] == [1508, 1566, 1678],
        "q=2593 principal residue cancels": q2593["principal_residue_mod_q"] == 0,
    }
    return {
        "probe": "erdos68_prime_pole_scan",
        "range": {"minimum_prime": 5, "maximum_prime": max_prime},
        "prime_count": len(rows),
        "nonzero_principal_residue_count": len(rows) - len(cancellations),
        "zero_principal_residue_count": len(cancellations),
        "cancellations": cancellations,
        "falsifiers": falsifiers,
        "all_falsifiers_pass": all(falsifiers.values()),
        "claim_boundary": (
            "Exact finite modular computation. A nonzero principal residue is a "
            "local denominator-survival certificate, not a cofinal lower-cylinder "
            "escape theorem and not an irrationality proof."
        ),
    }


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__.splitlines()[0])
    parser.add_argument("--max-prime", type=int, default=5000)
    args = parser.parse_args()
    result = run(args.max_prime)
    print(json.dumps(result, indent=2))
    return 0 if result["all_falsifiers_pass"] else 1


if __name__ == "__main__":
    raise SystemExit(main())
