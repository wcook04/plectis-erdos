#!/usr/bin/env python3
"""The half-cutoff greedy window and strict-core midpoint audit for `1/2 ∈ 𝒜`.

`BooleanMobiusCofinalExactRows.lean` carries this chain, already Lean:

    CofinalEvenHalfCutoffCoreSafety
      → cofinalHalfCutoffGreedyWindows_of_evenCoreSafety
      → CofinalHalfCutoffGreedyWindows                            (line 49)
      → exactLocalMersenneHalfRow_of_halfCutoffGreedyWindow       (line 106)
      → CofinalExactLocalMersenneHalfRows                         (line 41)
      → (line 432)  (1 / 2 : ℝ) ∈ mersenneAchievementSet

and `HalfCutLocator.positiveMersenneSupportValue_coe_finset_ne_half` says no
finite support equals `1/2`.  So `1/2 ∈ 𝒜` is an INFINITE rational
reciprocal-Mersenne subseries, i.e. **Erdős #257 refuted**.

Everything above the first line is proved.  The whole remaining gap is the
single integer inequality at the top, one instance per `M`:

    integerGreedyRemainder (localMersenneWeights M (M/2)) (2^(M-1) - 1)
        <  2 ^ (M - M/2)

with `localMersenneWeights M R = [ 2^M / (2^d - 1) : d = 2 … R ]` (natural
division, increasing `d`) and `integerGreedyRemainder` the plain take-if-it-
fits greedy residue.  This script evaluates that inequality exactly.

## Why it is not trivial

Greedy over a weight list leaves a residue below the LAST weight, here
`w_k = 2^M / (2^k - 1)` with `k = M/2`.  But `w_k ≥ 2^(M-k)` always, because
`2^M/(2^k - 1) > 2^(M-k)`.  So the standard greedy bound gives `r < w_k`
while the producer needs `r < 2^(M-k) ≤ w_k`.  The gap is exactly one unit
at the margin — e.g. `M = 10`, `k = 5`: `w_k = 33`, cap `= 32`.  The
inequality is therefore sharp, and the measured worst ratio `r / cap` runs
to `0.9997`.  Any proof must be tight; no slack argument will do.

## The adjacent strict-core target

For an even endpoint `M = 2R`, the nonterminating-binary target is

    H = 2^(2R-1) - 1.

After greedy ranks `2,...,R-1`, write the strict-core remainder as `A_R`.
The terminal coins are the midpoint coin `2^R+1` and the complete binary
bank of capacity `2^R-1`.  Consequently every `A_R <= 2^(R+1)` is absorbed,
except that `A_R = 2^R` leaves quotient defect one from `H` (equivalently
half-carry two from the adjacent target `2^(2R-1)`).  That defect is harmless
for the closed-set limit.

This observation is valid but conditional.  The claimed strict-core bound
`A_R <= 2^(R+1)` is exactly the still-open coarse producer
`CofinalEvenHalfCutoffCoreBound` when required cofinally.  This script audits
the bound separately from its already-proved consumer.  It also reports the
weaker terminal corridor condition `A_R <= 2^(R+1) + 2R - 1`, equivalent to
the optimally repaired terminal carry being at most `2R`.  Neither finite
audit is promoted to an all-depth theorem.

## Status

Finite evidence, not a proof.  No failure has been found; the residue
appears equidistributed in `[0, cap)`, which is what a proof has to explain.
"""

from __future__ import annotations

problem_id = "erdos_257"

import argparse
import json


def window(m: int) -> tuple[int, int]:
    """Return (greedy remainder, cap) for endpoint `m`."""
    k = m // 2
    remainder = (1 << (m - 1)) - 1
    for d in range(2, k + 1):
        weight = (1 << m) // ((1 << d) - 1)
        if weight <= remainder:
            remainder -= weight
    return remainder, 1 << (m - k)


def even_strict_core(r: int) -> int:
    """Return `A_R` for target `2^(2R-1)-1` and ranks `2,...,R-1`."""
    remainder = (1 << (2 * r - 1)) - 1
    for d in range(2, r):
        weight = (1 << (2 * r)) // ((1 << d) - 1)
        if weight <= remainder:
            remainder -= weight
    return remainder


def repaired_terminal_defect(r: int, core: int) -> int:
    """Defect from `H` after midpoint and the complete upper binary bank."""
    midpoint = (1 << r) + 1
    remainder = core - midpoint if midpoint <= core else core
    bank_capacity = (1 << r) - 1
    return max(0, remainder - bank_capacity)


def strict_core_audit(core_through: int) -> dict:
    bound_failures = []
    corridor_failures = []
    midpoint_hits = []
    tightest = []
    max_carry = (0, None)

    for r in range(3, core_through + 1):
        core = even_strict_core(r)
        bound = 1 << (r + 1)
        corridor_bound = bound + 2 * r - 1
        defect = repaired_terminal_defect(r, core)
        carry = defect + 1

        if core > bound:
            bound_failures.append({"R": r, "excess": core - bound})
        if core > corridor_bound:
            corridor_failures.append(
                {"R": r, "excess": core - corridor_bound}
            )
        if core == 1 << r:
            midpoint_hits.append(r)
        tightest.append((core / bound, r, bound - core, carry))
        if carry > max_carry[0]:
            max_carry = (carry, r)

    tightest.sort(reverse=True)
    return {
        "rows_tested": max(0, core_through - 2),
        "max_R": core_through,
        "attachment_bound": "A_R <= 2^(R+1)",
        "attachment_bound_failures": bound_failures[:10],
        "attachment_bound_holds_for_every_tested_R": not bound_failures,
        "exact_midpoint_hits": midpoint_hits[:20],
        "exact_midpoint_hit_count": len(midpoint_hits),
        "linear_corridor_bound": "A_R <= 2^(R+1) + 2R - 1",
        "linear_corridor_failures": corridor_failures[:10],
        "linear_corridor_holds_for_every_tested_R": not corridor_failures,
        "maximum_repaired_terminal_carry": {
            "carry": max_carry[0],
            "R": max_carry[1],
        },
        "tightest_attachment_bound_rows": [
            {
                "R": r,
                "ratio": round(ratio, 9),
                "bound_minus_A_exact_if_small": (
                    margin if margin.bit_length() <= 63 else None
                ),
                "bound_minus_A_bit_length": margin.bit_length(),
                "repaired_terminal_carry": carry,
            }
            for ratio, r, margin, carry in tightest[:10]
        ],
        "claim_ceiling": (
            "finite evidence only; cofinal/all-depth control of A_R remains "
            "the open producer"
        ),
    }


def scan(endpoints: list[int], core_through: int) -> dict:
    failures = []
    tightest = []
    for m in endpoints:
        remainder, cap = window(m)
        if remainder >= cap:
            failures.append({"M": m, "remainder_minus_cap": remainder - cap})
        if m >= 8:
            tightest.append((remainder / cap, m, cap - remainder))
    tightest.sort(reverse=True)
    return {
        "endpoints_tested": len(endpoints),
        "max_endpoint": max(endpoints),
        "failures": failures,
        "holds_for_every_tested_endpoint": not failures,
        "tightest": [
            {"M": m, "ratio": round(r, 6), "cap_minus_remainder": deficit}
            for r, m, deficit in tightest[:10]
        ],
        "min_cap_minus_remainder": min(d for _, _, d in tightest) if tightest else None,
        "consumer_chain": (
            "CofinalHalfCutoffGreedyWindows -> ExactLocalMersenneHalfRow -> "
            "CofinalExactLocalMersenneHalfRows -> 1/2 in mersenneAchievementSet "
            "-> infinite rational subseries -> Erdos 257 refuted"
        ),
        "claim_ceiling": (
            "finite evidence; the producer is a universally quantified "
            "inequality and no scan proves it"
        ),
        "strict_core_midpoint_audit": strict_core_audit(core_through),
    }


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--dense-through", type=int, default=400,
                        help="test every M from 2 up to this")
    parser.add_argument("--sparse-through", type=int, default=4000)
    parser.add_argument("--sparse-step", type=int, default=7)
    parser.add_argument(
        "--core-through",
        type=int,
        default=2000,
        help="audit every even strict-core row R=3,...,this value",
    )
    args = parser.parse_args()
    endpoints = list(range(2, args.dense_through))
    endpoints += list(range(args.dense_through, args.sparse_through + 1,
                            args.sparse_step))
    print(json.dumps(scan(endpoints, args.core_through), indent=2,
                     sort_keys=True))


if __name__ == "__main__":
    main()
