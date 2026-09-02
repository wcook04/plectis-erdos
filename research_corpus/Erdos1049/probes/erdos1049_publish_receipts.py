#!/usr/bin/env python3
"""Re-run the Erdos #1049 window-divisor probe and publish its bound receipt."""

from __future__ import annotations

import argparse
import sys
from pathlib import Path

REPO_ROOT = Path(__file__).resolve().parents[2]
if str(REPO_ROOT) not in sys.path:
    sys.path.insert(0, str(REPO_ROOT))

from formal_math.probes import erdos1049_window_divisor_supply as probe  # noqa: E402
from formal_math.probes.receipt import publish  # noqa: E402

LAB = ("formal_math/erdos257_period_noncollapse/ErdosProblems/Erdos1049/"
       "WindowDivisorSupplyLab.md")
PRIOR_LAB = ("formal_math/erdos257_period_noncollapse/ErdosProblems/Erdos1049/"
             "QAperyTailDenominatorLab.md")
LEAN = ("formal_math/erdos257_period_noncollapse/ErdosProblems/Erdos1049/"
        "QAperyTailDenominator.lean")


def main() -> int:
    ap = argparse.ArgumentParser()
    ap.add_argument("--max-start", type=int, default=14)
    args = ap.parse_args()
    payload = probe.run(args.max_start)
    path = publish(
        out_path="state/formal_math/probes/erdos1049_window_divisor_receipt.json",
        problem_id="erdos_1049",
        hypothesis_id="step_one_window_divisor_exists_and_is_source_supported",
        hypothesis_statement=(
            "For cofinally many starts s a moving divisor exists across the exact "
            "window of width 3s^2 + 5s + 3, and each newly appearing prime divides the "
            "source denominator 3^s - 2^s at its first start."),
        probe_id="erdos1049_window_divisor_supply",
        probe_question=(
            "Does the step-1 predicate hold start by start, and is the divisor "
            "source-supported in the first-appearance sense?"),
        computation=(
            "Build the primitive q-Apery rows from the exact Fraction recurrence to "
            "index 677, take the gcd of the denominator coordinates across each exact "
            "window [s, s + 3s^2 + 5s + 3], factor it, and test each newly appearing "
            "prime against 3^s - 2^s. The row generator is anchored against the prior "
            "lab's 211 | B_j for 5 <= j <= 255."),
        falsifier=(
            "A start whose window gcd is 1. If such starts are cofinal, step 1 as "
            "stated is false and the target must change again."),
        stop_condition=(
            "Cofinal empty windows retire step 1; the probe deliberately does not "
            "extend the row cutoff hunting for new tail primes, which the prior lab "
            "states would not change the mathematical status."),
        survival_consequence=(
            "Step 1 is not the weak link: the residual on this route is a proof of what "
            "the computation shows rather than another change of target."),
        falsification_consequence=(
            "The window formulation joins the fixed-tail formulation as refuted, and "
            "the route needs a third target."),
        consumer_ref=LEAN,
        analysis_refs=[LAB, PRIOR_LAB],
        source_refs=["formal_math/probes/erdos1049_window_divisor_supply.py"],
        result_status="exact_one_way_result",
        result_summary=(
            "677 rows; starts 0..14. Only s = 0, 1, 2, 4 have window gcd 1 - the "
            "earliest starts - and every start in the upper half of the range carries a "
            "divisor, which is where cofinality lives. The divisor set grows with s: "
            "19 at s=3, 211 at s=5, 71*211 at s=7, +1009 at s=9, +331 at s=11, +29927 "
            "at s=13, +463 at s=14. The source-support law is exact on first "
            "appearance, seven out of seven: 19|19, 211|211, 71|2059, 1009|19171, "
            "331|175099, 29927|1586131, 463|4766585."),
        payload=payload,
        motivated_by=["three_halves_pade_height_gap"],
        supports=["window_divisor_supply_and_first_appearance_law"],
        binding_rationale=(
            "Evaluates the step-1 predicate the prior lab named but never tested, and "
            "makes the source-support claim exact by testing first appearance rather "
            "than inherited membership."),
        progress_class="mechanism_opened",
        decision_basis=(
            "Every start in the cofinality half carries a divisor, and every newly "
            "appearing prime divides 3^s - 2^s at its first start."),
        next_analytic_target=(
            "Show that for every large s the prime p_s dividing 3^s - 2^s selected at "
            "first appearance has no loss block meeting [s, s + 3s^2 + 5s + 3] - a "
            "comparison of ord_p(3/2) against a quadratic window."),
        resource_bounds={"max_start": args.max_start, "rows_built": payload["rows_built"]},
    )
    print("wrote", path.relative_to(REPO_ROOT))
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
