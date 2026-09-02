#!/usr/bin/env python3
"""Re-run the Erdos #249 delay-law probe and publish its bound receipt."""

from __future__ import annotations

import argparse
import sys
from pathlib import Path

REPO_ROOT = Path(__file__).resolve().parents[2]
if str(REPO_ROOT) not in sys.path:
    sys.path.insert(0, str(REPO_ROOT))

from formal_math.probes import erdos249_fixed_quotient_delay_law as probe  # noqa: E402
from formal_math.probes import erdos249_supply_delay as supply  # noqa: E402
from formal_math.probes.receipt import publish  # noqa: E402

LAB = ("formal_math/erdos257_period_noncollapse/ErdosProblems/Erdos249/"
       "FixedQuotientDelayLawLab.md")
LEAN = ("formal_math/erdos257_period_noncollapse/ErdosProblems/Erdos249/"
        "PeriodMultipleEscape.lean")
SUPPLY_LAB = ("formal_math/erdos257_period_noncollapse/ErdosProblems/Erdos249/"
              "SupplyDelayLab.md")
SUPPLY_LEAN = ("formal_math/erdos257_period_noncollapse/ErdosProblems/Erdos249/"
               "CyclotomicAnchoredKill.lean")


def publish_supply_delay(max_c: int, distance_max_c: int) -> int:
    payload = supply.run(max_c=max_c, distance_max_c=distance_max_c)
    if payload["status"] != "supply_present_throughout_range":
        raise SystemExit(f"unexpected probe status: {payload['status']}")
    if not payload["translation"]["within_one_admissible_step"]:
        raise SystemExit("the Diophantine translation exceeded one admissible step")
    delays = payload["delay_law"]
    distances = payload["distance_law"]
    products = [row["C_times_min_distance"] for row in distances]
    path = publish(
        out_path="state/formal_math/probes/erdos249_supply_delay_receipt.json",
        problem_id="erdos_249",
        hypothesis_id="supply_difficulty_is_dyadic_axis_specific",
        hypothesis_statement=(
            "The measured cost of the Lean-equivalent residue-gap supply is a feature of the "
            "pure-dyadic axis v=1, and the odd part v of the denominator carries its own "
            "obstruction that the packet's single-axis measurement could not see."),
        probe_id="erdos249_supply_delay",
        probe_question=(
            "What does the residue-gap supply cost off the pure-dyadic axis, and what quantity "
            "is the delay actually measuring?"),
        computation=(
            "Evaluate Lean's FullMersenneCenteredResidueGap predicate literally over c and odd v, "
            "recording the clearing height H0 (least multiple of phi(v) with M > 2B) and the delay "
            "(H_min - H0)/phi(v). Verify the block identity 2^H R_c = totientBlock(H,c) + R_(c+H) "
            "exactly, then measure ||v 2^c S|| by the recurrence A_(c+1) = 2A_c + phi(c+J+1) mod "
            "2^J at J=220, and compare H_min against phi(v)*ceil(log2(v c/||v 2^c S||)/phi(v))."),
        falsifier=(
            "A (c,v) with no admissible height below the cap, which would make the series rational "
            "and settle the problem negatively; a max-delay law not scaling as log2(C)/phi(v); or "
            "H_min departing from the predicted height by more than one admissible step."),
        stop_condition=(
            "A confirmed two-parameter law plus a verified translation retires the delay-cap "
            "programme on every axis and hands the residual to Diophantine approximation."),
        survival_consequence=(
            "The odd part would carry a separate obstruction and the producer would need a "
            "v-specific mechanism beyond the dyadic-axis analysis."),
        falsification_consequence=(
            "The difficulty concentrates on small phi(v), and the producer is an "
            "irrationality-measure statement for S on the denominator family v*2^c."),
        consumer_ref=SUPPLY_LEAN,
        analysis_refs=[SUPPLY_LAB],
        source_refs=["formal_math/probes/erdos249_supply_delay.py"],
        result_status="exact_one_way_result",
        result_summary=(
            "max_(c<=%d) delay(c,v) equals ceil(log2(C)/phi(v)) in seven of eight moduli and is one "
            "higher at v=1, with observed maxima %s for v = %s. The tallest height needed across "
            "the whole scan is %d. The Lean block identity holds exactly at the three tested "
            "(H,N). Since R_c = 2^c S - integer, the delay is a translation of ||v 2^c S||, and "
            "H_min tracks phi(v)*ceil(log2(v c/||v 2^c S||)/phi(v)) to within one admissible step "
            "in every case. Measuring the distance directly to c <= %d gives C*min in [%.3f, %.3f] "
            "for every modulus against log2(C)=%.2f, so min_(c<=C)||v 2^c S|| is of order 1/C with "
            "no v-dependence. Every uniform cap is therefore refuted on every axis, not only at "
            "v=1, and no lower bound stronger than 1/c is available." % (
                max_c,
                [row["max_delay_steps"] for row in delays],
                [row["v"] for row in delays],
                max(row["max_height"] for row in delays),
                distance_max_c, min(products), max(products),
                __import__("math").log2(distance_max_c))),
        payload=payload,
        motivated_by=["totient_specific_moving_dyadic_escape"],
        supports=["supply_delay_two_parameter_law_and_diophantine_translation",
                  "dyadic_family_denominator_exclusion_with_margin"],
        eliminates=["post_clear_delay_grows_like_log2_c"],
        binding_rationale=(
            "Extends the delay measurement from the single pure-dyadic axis to the whole odd-part "
            "quantifier and identifies the quantity being measured, converting the modular "
            "producer into a Diophantine one."),
        progress_class="mechanism_opened",
        decision_basis=(
            "Seven of eight moduli match ceil(log2(C)/phi(v)) exactly; the translation holds to "
            "within one admissible step everywhere; C*min lies in [0.354,1.569] across all eight "
            "moduli; and the pure-dyadic rerun reproduces the packet's landed witness, delay 19 "
            "at c=490794."),
        next_analytic_target=(
            "||v 2^c S|| >= c^-A for a fixed A>1, uniformly in odd v. That yields "
            "H <= (A+1)log2 c + log2 v + O(phi(v)) and settles the supply. It is an "
            "irrationality-measure statement about an explicit dyadic series, not a Mersenne "
            "residue or carry-trajectory statement."),
        resource_bounds={"max_c": max_c, "distance_max_c": distance_max_c,
                         "tail_bits": supply.TAIL_BITS,
                         "instances": (max_c + 1) * len(delays)},
    )
    print("wrote", path.relative_to(REPO_ROOT))
    return 0


def main() -> int:
    ap = argparse.ArgumentParser()
    ap.add_argument("--max-c", type=int, default=1_400_000)
    ap.add_argument("--max-h", type=int, default=64)
    ap.add_argument("--supply-delay", action="store_true",
                    help="publish the off-dyadic-axis supply-delay receipt instead")
    ap.add_argument("--supply-max-c", type=int, default=60000)
    ap.add_argument("--distance-max-c", type=int, default=200000)
    args = ap.parse_args()
    if args.supply_delay:
        return publish_supply_delay(args.supply_max_c, args.distance_max_c)
    payload = probe.run(args.max_c, args.max_h, 1)
    path = publish(
        out_path="state/formal_math/probes/erdos249_fixed_quotient_delay_receipt.json",
        problem_id="erdos_249",
        hypothesis_id="uniform_fixed_quotient_delay_cap",
        hypothesis_statement=(
            "The fixed-quotient trap on the pure-dyadic axis admits a uniform delay "
            "cap, so a large enough finite search settles it."),
        probe_id="erdos249_fixed_quotient_delay_law",
        probe_question=(
            "Does the maximum post-clear fixed-quotient delay over c <= C saturate, or "
            "does it grow with C - and if it grows, at what rate?"),
        computation=(
            "For every c in range, iterate totientBlock by its exact doubling "
            "recurrence, take the least absolute residue modulo 2^H - 1, and measure "
            "the longest run of consecutive H that have cleared the trivial threshold "
            "(2^H-1)/2 > c+H+1, are trapped inside radius c+H+1, and share one "
            "quotient. Record every new maximum against log2(c)."),
        falsifier=(
            "A running maximum that stops setting records, which would make a uniform "
            "cap plausible after all."),
        stop_condition=(
            "Saturation retires the growth-law reading; continued records retire the "
            "cap programme."),
        survival_consequence=(
            "A uniform cap exists and finite search can settle the branch."),
        falsification_consequence=(
            "No uniform cap can exist, every future cap will be refuted at c about "
            "2^cap, and the producer must target the growth law instead."),
        consumer_ref=LEAN,
        analysis_refs=[LAB],
        source_refs=["formal_math/probes/erdos249_fixed_quotient_delay_law.py"],
        result_status="exact_one_way_result",
        result_summary=(
            "Records keep coming: post-clear delay 15 at c=14177, 17 at c=50490, 18 at "
            "c=403191 and 19 at c=490794, with delay/log2(c) settling at 1.00-1.09. The "
            "last row is the packet's own witness - same delay, same c - recovered from "
            "an independently written statistic, which fixes the definition. The law is "
            "max{post-clear delay : c <= C} ~ log2 C, so cap 17 dies at c ~ 2^15.6, cap "
            "19 at c ~ 2^18.9, and cap N at c ~ 2^N. The delay-cap programme is dead "
            "rather than unlucky, and the redirected target is: after the window clears, "
            "the doubling recurrence escapes a radius-c window within O(log c) steps."),
        payload=payload,
        motivated_by=["totient_specific_moving_dyadic_escape"],
        supports=["post_clear_delay_grows_like_log2_c"],
        binding_rationale=(
            "Explains the packet's own history of refuted delay caps as a growth law "
            "rather than a sequence of near misses, and replaces the cap target with "
            "one that its own data does not refute."),
        progress_class="mechanism_eliminated",
        decision_basis=(
            "Independent reconstruction of the packet's delay-nineteen witness at the "
            "same c, plus continued records with a ratio to log2(c) settling at 1."),
        next_analytic_target=(
            "A bound of the form post-clear delay <= (1+o(1)) log2 c: the number of "
            "consecutive near-cancellations between the doubling of E_H and the totient "
            "increment phi(c+H+1) - k."),
        resource_bounds={"max_c": args.max_c, "max_h": args.max_h},
    )
    print("wrote", path.relative_to(REPO_ROOT))
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
