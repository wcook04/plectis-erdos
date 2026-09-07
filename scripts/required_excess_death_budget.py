#!/usr/bin/env python3
"""Erdos 257: how much must the arithmetic deviate from the measure heuristic?

The achievement set ``C`` has Lebesgue measure exactly 1 inside ``[0, E]``,
``E = 1.60669515...`` (section 1).  So of the ``floor(qE) ~ 1.607 q`` lattice
points ``p/q`` in ``(0, E)``, a measure heuristic predicts

    deaths    ~ q (E - 1) = 0.6067 q,
    survivors ~ q |C|     = q.

Erdos 257 asserts that the ONLY rationals in ``C`` are the finite Mersenne
sums.  This script counts those exactly, and the count is essentially zero,
so the theorem demands roughly ``q`` MORE deaths than the measure heuristic
gives -- an excess equal to the entire surviving population.

Exact count of finite sums.  Let ``x = sum_{a in F} 1/(2^a - 1) = p/q`` in
lowest terms with ``F`` finite, and let ``a`` in ``F`` be maximal for
divisibility inside ``F``.  Let ``r`` be a primitive prime divisor of
``2^a - 1`` (one exists for every ``a`` except ``a = 1`` and ``a = 6``, by
Bang's theorem).  Writing ``x = N / prod_{b in F} (2^b - 1)`` with
``N = sum_{a in F} prod_{b != a} (2^b - 1)``, every term of ``N`` except the
``a`` term carries the factor ``2^a - 1`` and so vanishes mod ``r``, while the
``a`` term is a product of ``2^b - 1`` with ``r`` dividing none of them.
Hence ``r`` does not divide ``N`` and therefore ``r | q``.  For prime ``q``
this forces ``r = q`` and ``a = ord_q(2)``.  Every element of ``F`` divides a
divisibility-maximal element, so

    F  is a subset of  {1, 2, 3, 6} union {d : d divides ord_q(2)},

which is small enough to enumerate completely.  The reduced denominator is
then computed exactly for each candidate; no heuristic enters.

The deaths a proof must supply live at depth beyond ``log_4 q``, where the
per-level budget from the measure is ``sum_{n > D} 2^(n-1) q gamma_n ~ (q/3)
2^-D``.  Section 4d/4b measured the deaths and found them matching the
measure prediction with no excess at all down to depth ``2.5 x 10^4``.  The
number this script reports is therefore the exact size of the arithmetic
conspiracy Erdos 257 requires -- stated, not assumed.

Companion analysis: ErdosProblems/Erdos257/SupportWordStructureLab.md
"""

from __future__ import annotations

import argparse
import hashlib
import json
from fractions import Fraction
from itertools import combinations
from typing import Any


def canonical_sha256(payload: Any) -> str:
    return hashlib.sha256(
        json.dumps(payload, separators=(",", ":"), sort_keys=True).encode()
    ).hexdigest()


def order_of_two(q: int) -> int | None:
    m = q
    while m % 2 == 0:
        m //= 2
    if m == 1:
        return None
    r, k = 2 % m, 1
    while r != 1:
        r = (2 * r) % m
        k += 1
        if k > 4 * m:
            return None
    return k


def divisors(n: int) -> list[int]:
    out = []
    i = 1
    while i * i <= n:
        if n % i == 0:
            out.append(i)
            if i != n // i:
                out.append(n // i)
        i += 1
    return sorted(out)


def prime_factors(n: int) -> list[int]:
    out = []
    d = 2
    while d * d <= n:
        if n % d == 0:
            out.append(d)
            while n % d == 0:
                n //= d
        d += 1
    if n > 1:
        out.append(n)
    return out


def is_prime(n: int) -> bool:
    if n < 2:
        return False
    if n % 2 == 0:
        return n == 2
    i = 3
    while i * i <= n:
        if n % i == 0:
            return False
        i += 2
    return True


def finite_sums_with_denominator(q: int, cap: int, E: Fraction) -> dict[str, Any]:
    e = order_of_two(q)
    if e is None:
        return {"q": q, "status": "power_of_two_denominator", "count": 0,
                "note": "every finite Mersenne sum has odd denominator, so a "
                        "power-of-two denominator admits none at all"}
    # Search space, prime or composite.  For a divisibility-maximal a in F and
    # r a primitive prime divisor of 2^a - 1, the argument above gives r | q,
    # hence a = ord_r(2) for some prime r | q.  Adding the two Bang exceptions
    # a in {1, 6}, every element of F divides one of those exponents:
    #
    #   F  subset  union of div(a) over a in {1,6} u {ord_r(2) : r | q prime}.
    #
    # For prime q this collapses to {1,2,3,6} u div(ord_q(2)).  The set is a
    # SUPERSET of the true constraint, so enumerating it and computing each
    # reduced denominator exactly keeps the count exact.
    exps = {1, 6}
    for r in prime_factors(q):
        if r == 2:
            continue
        o = order_of_two(r)
        if o is not None:
            exps.add(o)
    cand = sorted({d for a in exps for d in divisors(a)})
    # The cost is 2^|cand| subsets, not the size of the largest exponent:
    # 2^5003 - 1 is a cheap big integer.  Cap the SET SIZE.
    if len(cand) > cap:
        return {
            "q": q,
            "status": "candidate_set_too_large",
            "order_of_two": e,
            "candidate_size": len(cand),
            "cap": cap,
            "note": "F is contained in {1,2,3,6} u div(ord_q(2)); this set has "
                    "too many elements to enumerate exhaustively, so the exact "
                    "count was not attempted rather than guessed",
        }
    hits = []
    for k in range(1, len(cand) + 1):
        for F in combinations(cand, k):
            x = sum((Fraction(1, 2**a - 1) for a in F), Fraction(0))
            if x <= 0 or x >= E:
                continue
            if x.denominator == q:
                hits.append({"F": list(F), "x": f"{x.numerator}/{x.denominator}"})
    return {
        "q": q,
        "status": "exact",
        "order_of_two": e,
        "prime_factors": prime_factors(q),
        "candidate_exponents": cand,
        "subsets_enumerated": 2 ** len(cand) - 1,
        "count": len(hits),
        "examples": hits[:6],
    }


def main() -> None:
    ap = argparse.ArgumentParser()
    ap.add_argument(
        "--denominators", type=str, default="97,101,127,257,509,997,1009,2053,4099,10007"
    )
    ap.add_argument("--cap", type=int, default=20)
    ap.add_argument("--write", type=str, default=None)
    args = ap.parse_args()

    E = sum((Fraction(1, 2**k - 1) for k in range(1, 400)), Fraction(0))
    rows = []
    for t in args.denominators.split(","):
        q = int(t)
        row = finite_sums_with_denominator(q, args.cap, E)
        lattice = int(E * q)
        row["lattice_points_in_(0,E)"] = lattice
        row["measure_predicted_deaths"] = float(q * (E - 1))
        row["measure_predicted_survivors"] = q
        if row.get("status") == "exact":
            row["erdos257_required_survivors"] = row["count"]
            row["required_excess_deaths"] = q - row["count"]
            row["required_excess_as_fraction_of_survivors"] = (
                (q - row["count"]) / q if q else None
            )
        rows.append(row)

    payload = {
        "schema": "erdos257_required_excess_death_budget_v1",
        "parameters": vars(args),
        "erdos_borwein_E": float(E),
        "source": {
            "script": "formal_math/erdos257_period_noncollapse/scripts/"
            "required_excess_death_budget.py",
            "analysis": "formal_math/erdos257_period_noncollapse/ErdosProblems/"
            "Erdos257/SupportWordStructureLab.md",
        },
        "rows": rows,
    }
    payload["payload_sha256"] = canonical_sha256(payload)
    text = json.dumps(payload, indent=2, sort_keys=True, default=str)
    if args.write:
        with open(args.write, "w", encoding="utf-8") as h:
            h.write(text + "\n")
        print(f"wrote {args.write} sha256={payload['payload_sha256']}")
    else:
        print(text)


if __name__ == "__main__":
    main()
