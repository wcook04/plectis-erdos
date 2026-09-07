#!/usr/bin/env python3
"""Erdős #257 via `1/2`, reduced to one sentence with no index in it.

## The chain, all of it already Lean

`GreedyAchievementSet.half_mem_mersenneAchievementSet_of_skipped_dyadicCap`
(line 1431) is landed:

    (∀ n, rank n+1 skipped → greedyMersenneRemainder (1/2) n ≤ (1/2)^(n+1))
      →  (1/2 : ℝ) ∈ mersenneAchievementSet

and `HalfCutLocator.positiveMersenneSupportValue_coe_finset_ne_half` (243)
says no finite support equals `1/2`.  So that hypothesis yields an infinite
rational reciprocal-Mersenne subseries: **Erdős #257 refuted.**

## Collapsing the hypothesis

Write `R` for a greedy residual and `V = 1/R`.  With `X = 2^(n+1)`:

    rank n+1 skipped  ⟺  V > X - 1
    dyadic cap at n   ⟺  V ≥ X

so the cap fails exactly when `V ∈ (X-1, X)` — strictly between a Mersenne
number and the next power of two, an open interval containing no integer.

Three reductions, each checked below.

**(1) Failure can only occur at the last skip of a run.**  `V` is constant
while skipping.  If `V < 2^(n+1)` then `2^(n+2) - 1 > V`, so rank `n+2` is
taken.  The failing rank is therefore always immediately followed by a take.

**(2) The index drops out.**  The take fires at the least `m` with
`2^m - 1 ≥ V`, so the cap at the last skip `n = m-2` says `V ∉ (2^(m-1)-1,
2^(m-1))`.  Quantifying over runs instead of ranks:

>   **PRODUCER.  For every greedy Mersenne residual `R` of `1/2`,
>   `⌊1/R⌋ + 1` is not a power of two.**

No `n`, no cap, no greedy bookkeeping.  Its truth refutes Erdős #257.

**(3) Parity.**  `1/2` keeps exactly one factor of two: writing `R = p/q`
reduced, `p` is odd, `q` is even and `v₂(q) = 1` at every step.  Hence in a
failure `q = pX - j` with `j` even, so `p ≥ 3`: a unit-numerator residual can
never fail.  Measured, `p = 1` for the first six distinct residuals.

## Measured

`--ranks 600`: 280 distinct residuals, **zero** with `⌊1/R⌋ + 1` a power of
two; zero parity violations; `v₂(q) = 1` throughout.  The exact clearance
`D/p` with `D = q - p(2^(n+1) - 1)` — the cap is `D/p ≥ 1` — has minimum
exactly `1`, attained only at the trivial start `R = 1/2`, and grows past
`10^20` by `n = 68`.

Finite evidence, not a proof.  The producer is universally quantified.
"""

from __future__ import annotations

problem_id = "erdos_257"

import argparse
import json
from fractions import Fraction


def is_power_of_two(value: int) -> bool:
    return value > 0 and value & (value - 1) == 0


def rung_ladder(ranks: int) -> dict:
    """All four rungs in the single coordinate D/p, and the weakest producer.

    With `R = p/q` reduced and `X = 2^(n+1)`, put `D = q - p(X-1)`.  Then
    `D/p = q/p - 2^(n+1) + 1` and every condition is a threshold on it:

        skip                D/p > 0
        HOLE-FREE (exact)   D/p >= theta,  theta = 2/3 - (2/63)2^-(n+1) + O(4^-n)
        PRODUCER            D/p >= 2/3            <- weakest sufficient
        two-channel         D/p >= (2X+1)/(3X+1)  <- landed consumer, line 1412
        dyadic              D/p >= 1              <- landed consumer, line 1431

    The producer is one integer inequality, `3q + p >= 3p*2^(n+1)`, and it
    implies hole-freeness because `theta < 2/3` is already proved
    (`HalfGreedyFatalGap`).
    """
    residual = Fraction(1, 2)
    failures, worst, skipped = [], None, 0
    for n in range(ranks):
        weight = Fraction(1, 2 ** (n + 1) - 1)
        if weight <= residual:
            residual -= weight
            continue
        skipped += 1
        p, q = residual.numerator, residual.denominator
        x = 1 << (n + 1)
        if not (3 * q + p >= 3 * p * x):
            failures.append(n)
        ratio = Fraction(q - p * (x - 1), p)
        worst = ratio if worst is None else min(worst, ratio)
    return {
        "producer": "3q + p >= 3p * 2^(n+1) at every skipped rank",
        "skipped_ranks": skipped,
        "producer_failures": failures,
        "min_D_over_p": float(worst) if worst is not None else None,
        "threshold": "2/3",
        "slack_at_tightest": (float(worst) - 2 / 3) if worst is not None else None,
        "theta_asymptotic": "theta(m) = 2/3 - (2/63)*2^-m + O(4^-m)",
        "warning": (
            "do not check theta < 2/3 numerically with a short tail: the "
            "truncation error is the size of the gap and flips the sign"
        ),
    }


def scan(ranks: int) -> dict:
    residual = Fraction(1, 2)
    distinct: list[tuple[int, int]] = []
    failures = []
    parity_violations = 0
    two_adic = set()
    clearances = []
    opening = []
    pending_skip = None

    for n in range(ranks):
        p, q = residual.numerator, residual.denominator
        if p % 2 == 0 or q % 2 == 1:
            parity_violations += 1
        value, rest = 0, q
        while rest % 2 == 0:
            rest //= 2
            value += 1
        two_adic.add(value)

        if not distinct or distinct[-1] != (p, q):
            distinct.append((p, q))
            floor_recip = q // p
            if is_power_of_two(floor_recip + 1):
                failures.append({"rank": n, "floor_one_over_R": floor_recip})
            if len(opening) < 10:
                opening.append({
                    "numerator": p,
                    "floor_one_over_R": floor_recip,
                    "plus_one_is_power_of_two": is_power_of_two(floor_recip + 1),
                })

        weight = Fraction(1, 2 ** (n + 1) - 1)
        if weight <= residual:
            if pending_skip is not None:
                m, last = pending_skip
                deficit = last.denominator - last.numerator * (2 ** (m + 1) - 1)
                clearances.append(Fraction(deficit, last.numerator))
            pending_skip = None
            residual -= weight
        else:
            pending_skip = (n, residual)

    worst = min(clearances) if clearances else None
    return {
        "ranks": ranks,
        "distinct_residuals": len(distinct),
        "producer": "for every greedy residual R of 1/2, floor(1/R) + 1 is not a power of two",
        "producer_failures": failures,
        "producer_holds": not failures,
        "parity_violations": parity_violations,
        "two_adic_valuations_of_denominator": sorted(two_adic),
        "runs_measured": len(clearances),
        "min_clearance_D_over_p": float(worst) if worst is not None else None,
        "clearance_note": "cap is D/p >= 1 with D = q - p(2^(n+1) - 1)",
        "opening_residuals": opening,
        "consumer": (
            "GreedyAchievementSet.half_mem_mersenneAchievementSet_of_skipped_"
            "dyadicCap (1431) -> 1/2 in mersenneAchievementSet; with "
            "HalfCutLocator.positiveMersenneSupportValue_coe_finset_ne_half "
            "(243) the support is infinite, refuting Erdos 257"
        ),
        "rung_ladder": rung_ladder(ranks),
        "claim_ceiling": "finite evidence; the producer is universally quantified",
    }


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--ranks", type=int, default=600)
    args = parser.parse_args()
    print(json.dumps(scan(args.ranks), indent=2, sort_keys=True))


if __name__ == "__main__":
    main()
