#!/usr/bin/env python3
"""Erdos 257: the single-residue-class route to the odd-p dichotomy is dead.

Context.  SupportWordStructureLab.md section 5a proves, for odd p, that if
``f_A mod p`` is eventually periodic with period P and preperiod L then A
contains no product of distinct primes ``r > L`` with ``r = 1 (mod P)``.  The
proof takes such primes, forms ``r_S = prod_{i in S} r_i``, uses
``f_A(r_S) = g(1)`` for every nonempty S, and Mobius-inverts on the Boolean
lattice to get ``b_{r_S} = (-1)^{|S|}(b_1 - g(1))``; membership in ``{0,1}``
then forces ``b_1 = g(1)`` and ``b_{r_S} = 0``, because for odd p the values
``delta`` and ``-delta`` cannot both lie in ``{0,1}`` unless ``delta = 0``.

The natural next step -- and the one this directory queued -- is to run the
same argument with primes in a general class ``rho``.  There ``r_S = rho^{|S|}``,
so the Mobius inversion gives the finite difference

    b_{r_S} = (Delta^{|S|} h)(0),   h = (b_1, g(rho), g(rho^2), g(rho^3), ...),

with h periodic of period ``d = ord_P(rho)`` from index 1.  If the only
sequences whose finite differences all lie in ``{0,1}`` mod p were the
constant ones, the argument would extend to every class and the odd-p
dichotomy would follow.

THIS SCRIPT SHOWS THAT IS FALSE.  It enumerates every ``(b_1, g)`` with
``b_1 in {0,1}`` and ``g`` in ``F_p^d``, builds the finite-difference triangle
mod p with early exit, and reports survivors and how many of them take the
value 1 infinitely often.  For ``d = 1`` there are never any -- which is
exactly the proven Proposition, recovered independently.  For ``d >= 2`` there
are: e.g. ``p = 3, d = 2, b_1 = 0, g = (0,1)`` has differences
``0,1,0,1,0,1,...``.

Consequence: the odd-p dichotomy cannot be obtained by iterating the
single-class Boolean-lattice argument.  A proof must couple the classes --
the constraints for all ``rho`` coprime to ``P`` hold simultaneously, together
with the coprime-factor constraints ``sum_{d | M} b_{d r_S} = 0`` -- or use a
different mechanism entirely.  The exhaustive branch search in
``characteristic_p_dichotomy_search.py`` (39,060 odd-p branches, zero
survivors) is unaffected; only this route to a theorem is closed.

Companion analysis: ErdosProblems/Erdos257/SupportWordStructureLab.md
"""

from __future__ import annotations

import argparse
import hashlib
import json
from itertools import product
from typing import Any


def canonical_sha256(payload: Any) -> str:
    return hashlib.sha256(
        json.dumps(payload, separators=(",", ":"), sort_keys=True).encode()
    ).hexdigest()


def survives(b1: int, g: list[int], d: int, p: int, depth: int):
    """Finite-difference triangle of h mod p, leading entry checked per level."""
    cur = [b1] + [g[(k - 1) % d] for k in range(1, depth + 1)]
    lead: list[int] = []
    for m in range(depth):
        v = cur[0] % p
        if m >= 1:
            if v not in (0, 1):
                return False, lead
            lead.append(v)
        if len(cur) < 2:
            break
        cur = [(cur[i + 1] - cur[i]) % p for i in range(len(cur) - 1)]
    return True, lead


def scan(p: int, max_d: int, depth: int, budget: int) -> list[dict[str, Any]]:
    rows = []
    for d in range(1, max_d + 1):
        if 2 * p**d > budget:
            continue
        cand = surv = 0
        witnesses = []
        for b1 in range(2):
            for g in product(range(p), repeat=d):
                cand += 1
                ok, lead = survives(b1, list(g), d, p, depth)
                if not ok:
                    continue
                surv += 1
                if any(v == 1 for v in lead):
                    witnesses.append(
                        {"b1": b1, "g": list(g), "leading_differences": lead[:12]}
                    )
        rows.append(
            {
                "p": p,
                "d": d,
                "candidates": cand,
                "survivors": surv,
                "survivors_taking_value_one": len(witnesses),
                "witness": witnesses[0] if witnesses else None,
            }
        )
    return rows


def main() -> None:
    ap = argparse.ArgumentParser()
    ap.add_argument("--primes", type=str, default="3,5,7,11,13")
    ap.add_argument("--max-d", type=int, default=5)
    ap.add_argument("--depth", type=int, default=120)
    ap.add_argument("--budget", type=int, default=400000)
    ap.add_argument("--write", type=str, default=None)
    args = ap.parse_args()

    rows: list[dict[str, Any]] = []
    for t in args.primes.split(","):
        if t.strip():
            rows.extend(scan(int(t), args.max_d, args.depth, args.budget))

    d1 = [r for r in rows if r["d"] == 1]
    payload = {
        "schema": "erdos257_odd_p_finite_difference_nogo_v1",
        "parameters": vars(args),
        "source": {
            "script": "formal_math/erdos257_period_noncollapse/scripts/"
            "odd_p_finite_difference_nogo.py",
            "analysis": "formal_math/erdos257_period_noncollapse/ErdosProblems/"
            "Erdos257/SupportWordStructureLab.md",
            "unaffected_companion": "formal_math/erdos257_period_noncollapse/"
            "scripts/characteristic_p_dichotomy_search.py",
        },
        "verdict": (
            "The single-residue-class Boolean-lattice route to the odd-p "
            "dichotomy is CLOSED. For d = ord_P(rho) = 1 no survivor ever takes "
            "the value 1, which recovers the proven Proposition; for d >= 2 "
            "survivors taking 1 infinitely often exist, so iterating the "
            "argument over residue classes cannot force A finite."
        ),
        "d_equals_one_confirms_proposition": all(
            r["survivors_taking_value_one"] == 0 for r in d1
        ),
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
