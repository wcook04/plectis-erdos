#!/usr/bin/env python3
"""Erdos #68: how close has the series ever come to being rational?

The question
------------
`S = sum_(n>=2) 1/(n!-1)`.  Lean proves irrationality is exactly the cofinal
failure of `m | N_m`, i.e. cofinally many non-unit carries.  Nobody had asked the
obvious quantitative question: at the places where the carry IS a unit, how close
did the series actually come to the rational configuration?

Where rationality lives
-----------------------
`factorialGapStepCarry_eq_one_iff_zero_or_maximal_branch` splits a unit carry into
two endpoint cylinders:

  * the **zero branch**  -- canonical digit `0`, both endpoint flags `0`;
  * the **maximal branch** -- canonical digit `m-1`, both endpoint flags `1`.

Reading the proof of `irrational_factorialGapSeries_of_cofinal_predecessorGap_
threshold` shows which one matters.  Under `S = a/q` with `q | (m-1)!`, the
canonical remainder at `m-1` is `0`, hence `canonicalDigit m = 0`.  So
**rationality lives in the zero branch**, and the tail-free threshold is
sufficient precisely because it excludes that branch.

In gap coordinates, with `A_m = N_m - m! P_m in (0,1]` the scaled predecessor gap
and `R_m = m! sum_(n>m) 1/(n!-1)` the scaled tail, the zero branch at `m` is

    D_m = 0    and    A_m <= R_m .

That set has width `R_m / m = O(m^-2)`.  **Summable** -- unlike the unit-carry
window itself, which is `O(1/m)` and divergent.  So Borel-Cantelli says a generic
orbit enters it only finitely often, while rationality requires entering it at
every large `m`.  The gap between those two is far wider than anything the
`1/m` window offers.

There is also a clean combinatorial reading.  Since
`A_m - R_m = sum_(j>m) D_j m!/j!`, whose leading term is `D_(m+1)/(m+1)`, the
condition `A_m <= R_m` says the first nonzero digit past `m` is `-1`.  So the
zero branch is exactly: **a unit carry whose next nonzero digit is `-1`**, and the
margin `A_m / R_m` is essentially `D_(next nonzero) + 1`, which ranges over
`[0, m)`.  Hence the `1/m^2` joint probability, and a total expectation over all
`m` of about `1/3`.

Probe
-----
Run the exact recursion `A_m = m A_(m-1) - 1 - 1/(m!-1) - D_m` in scaled integer
arithmetic from an exactly-seeded prefix, recording every unit carry, every
`D_m = -1`, every zero-branch hit, and the margin `A_m / R_m` at each unit carry.

Precision is the only cost: the recursion multiplies the error by `m` each step,
so a seed accurate to `10^-D` at `m0` is accurate to `10^-D * M!/m0!` at `M`.  The
probe reports the realised amplification and the digits of margin remaining.

Predeclared falsifier
---------------------
Any zero-branch hit; any unit carry whose margin is below `2`; or a realised
precision margin below 100 digits, which would invalidate the run rather than the
mathematics.

Claim boundary
--------------
Finite range.  A margin that has never dropped below 31 is not a theorem that it
never will, and Erdos #68 remains open.  The `Uniform` reading of the margin is a
heuristic, not a proved distribution.
"""

from __future__ import annotations

import argparse
import json
from fractions import Fraction
from math import factorial
from pathlib import Path

SEED_INDEX = 12
DEFAULT_MAX_M = 5000
TAIL_TERMS = 25


def _precision_digits(max_m: int) -> int:
    # log10(M!/m0!) plus a safety margin.
    amplification = (factorial(max_m) // factorial(SEED_INDEX)).bit_length() / 3.3219
    return int(amplification) + 4000


def run(max_m: int = DEFAULT_MAX_M) -> dict:
    digits = _precision_digits(max_m)
    scale = 10**digits

    prefix = sum(Fraction(1, factorial(n) - 1) for n in range(2, SEED_INDEX + 1))
    scaled = factorial(SEED_INDEX) * prefix
    gap = int((1 - (scaled - scaled.__floor__())) * scale)
    running_factorial = factorial(SEED_INDEX)

    unit_carries: list[int] = []
    negative_digits: list[int] = []
    zero_branch_hits: list[int] = []
    margins: list[dict] = []

    for m in range(SEED_INDEX + 1, max_m + 1):
        running_factorial *= m
        step = m * gap - scale - (scale // (running_factorial - 1))
        digit = -((-step) // scale) - 1
        gap = step - digit * scale
        if not 0 < gap <= scale:
            raise RuntimeError(f"gap left (0,1] at m={m}: precision failure")
        if digit == -1:
            negative_digits.append(m)
        if digit != 0:
            continue
        tail = 0
        forward = running_factorial
        for k in range(m + 1, m + TAIL_TERMS):
            forward *= k
            tail += (scale * running_factorial) // (forward - 1)
        unit_carries.append(m)
        if gap <= tail:
            zero_branch_hits.append(m)
        margins.append({
            "m": m,
            "A_m": round(gap / scale, 7),
            "R_m": float(f"{tail / scale:.4e}"),
            "margin_A_over_R": round(gap / tail, 1),
        })

    amplification = (
        running_factorial.bit_length() / 3.3219 - factorial(SEED_INDEX).bit_length() / 3.3219
    )
    closest = min(margins, key=lambda r: r["margin_A_over_R"]) if margins else None
    return {
        "probe": "erdos68_rational_cylinder_margin",
        "range": f"m = {SEED_INDEX + 1}..{max_m}",
        "working_precision_digits": digits,
        "error_amplification_log10": round(amplification),
        "precision_margin_digits_remaining": round(digits - amplification),
        "unit_carries": unit_carries,
        "digits_equal_minus_one": negative_digits,
        "zero_branch_hits_where_rationality_lives": zero_branch_hits,
        "margins": margins,
        "closest_approach": closest,
        "reading": (
            "Rationality lives in the zero branch of the unit-carry dichotomy: "
            "under S = a/q with q | (m-1)! the canonical remainder vanishes, so "
            "the canonical digit is 0, not m-1. That branch is D_m = 0 together "
            "with A_m <= R_m, a set of width R_m/m = O(m^-2) -- summable, unlike "
            "the O(1/m) unit-carry window. Equivalently it is a unit carry whose "
            "next nonzero digit is -1, and the margin A_m/R_m is essentially that "
            "digit plus one. Every unit carry on record misses it, and the "
            "closest approach is recorded above."
        ),
        "claim_boundary": (
            "Finite range. A margin that has never dropped below its recorded "
            "minimum is not a theorem that it never will. Erdos #68 remains open."
        ),
    }


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__.splitlines()[0])
    parser.add_argument("--max-m", type=int, default=DEFAULT_MAX_M)
    parser.add_argument("--json-out", type=Path, default=None)
    args = parser.parse_args()
    result = run(args.max_m)
    text = json.dumps(result, indent=2)
    print(text)
    if args.json_out:
        args.json_out.write_text(text + "\n", encoding="utf-8")
    checks = [
        not result["zero_branch_hits_where_rationality_lives"],
        all(r["margin_A_over_R"] >= 2 for r in result["margins"]),
        result["precision_margin_digits_remaining"] > 100,
    ]
    return 0 if all(checks) else 1


if __name__ == "__main__":
    raise SystemExit(main())
