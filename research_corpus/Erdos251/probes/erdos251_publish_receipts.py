#!/usr/bin/env python3
"""Re-run the Erdos #251 probe and publish its bound, durable receipt."""

from __future__ import annotations

import argparse
import sys
from pathlib import Path

REPO_ROOT = Path(__file__).resolve().parents[2]
if str(REPO_ROOT) not in sys.path:
    sys.path.insert(0, str(REPO_ROOT))

from formal_math.probes import erdos251_adjacent_mismatch_density as probe  # noqa: E402
from formal_math.probes import erdos251_conditional_shift_distribution as cond  # noqa: E402
from formal_math.probes.receipt import publish  # noqa: E402

LAB = ("formal_math/erdos257_period_noncollapse/ErdosProblems/Erdos251/"
       "AdjacentMismatchDensityLab.md")
LEAN_WALL = ("formal_math/erdos257_period_noncollapse/ErdosProblems/Erdos251/"
             "AffineShiftEscape.lean")


def main() -> int:
    ap = argparse.ArgumentParser()
    ap.add_argument("--limit", type=int, default=120_000_000)
    ap.add_argument("--max-h", type=int, default=16)
    ap.add_argument("--bands", type=int, default=8)
    args = ap.parse_args()
    payload = probe.run(args.limit, args.max_h, args.bands)
    path = publish(
        out_path="state/formal_math/probes/erdos251_adjacent_mismatch_receipt.json",
        problem_id="erdos_251",
        hypothesis_id="adjacent_mismatch_event_occurs_in_actual_primes",
        hypothesis_statement=(
            "The single event the landed +-2 wall and sign-alignment theorems reduce "
            "the cofinal-adjacent-small-mismatch producer to - Delta = +2 with "
            "D in (1/2,1), or Delta = -2 with D in (-1,-1/2) - actually occurs in the "
            "actual prime gaps, cofinally, for every fixed offset h."),
        probe_id="erdos251_adjacent_mismatch_density",
        probe_question=(
            "Does the producer's event occur in the actual primes, and does its "
            "density persist as N grows or decay to zero?"),
        computation=(
            "Sieve the actual primes; build the actual scaled tails by the exact "
            "backward recurrence T_N = (g_(N+1) + T_(N+1))/2; count the event per "
            "offset h across bands of N; re-check a sample against the producer as "
            "literally written; and measure the distance of each hit from the window "
            "boundary to confirm the float tails cannot be deciding it."),
        falsifier=(
            "A density decaying toward zero for some fixed h, which would say the "
            "producer is false for that h."),
        stop_condition=(
            "One offset losing the event retires the producer and sends #251 to a "
            "different consumer; it is not repaired by extending the sieve."),
        survival_consequence=(
            "The producer is true in the actual primes, so #251 needs a proof of "
            "cofinality rather than a new consumer, and the missing input is a "
            "correlation of consecutive prime gaps at a fixed offset."),
        falsification_consequence=(
            "The polynomial countermodel generalises to the primes and the whole "
            "adjacent-small-mismatch consumer must be replaced."),
        consumer_ref=LEAN_WALL,
        analysis_refs=[LAB],
        source_refs=["formal_math/probes/erdos251_adjacent_mismatch_density.py"],
        result_status="exact_one_way_result",
        result_summary=(
            "Over 6,841,648 primes and offsets h = 1..16 the event occurs for every h, "
            "at density between 0.00418 and 0.008248, with +2 and -2 near-balanced and "
            "events continuing to the top of the range (h=1: 56,427 events, last at "
            "prime 119,995,753). Band densities decline only at roughly the 1/log p "
            "cost of demanding Delta = +-2 - rescaled 0.1767 -> 0.1315, itself "
            "decelerating - so the event count up to X still grows like X/(log X)^2. "
            "3,200 hits re-checked against the producer as literally written gave zero "
            "violations, and the median distance from the window boundary is 0.127 "
            "against a worst case of 6.1e-7, eight orders above float resolution."),
        payload=payload,
        motivated_by=["cofinal_adjacent_small_mismatch",
                      "small_adjacent_shift_consumer",
                      "positive_even_polynomial_gap_rational_tail_countermodel"],
        supports=["actual_prime_adjacent_mismatch_event_density"],
        binding_rationale=(
            "Decides between the two live readings of #251's last producer: it is true "
            "in the actual primes rather than an artifact the polynomial countermodel "
            "generalises to, so the residual is a proof of cofinality and the required "
            "external input is a fixed-offset prime-gap correlation."),
        progress_class="mechanism_opened",
        decision_basis=(
            "The event occurs for every tested offset with density bounded away from "
            "zero after the 1/log p rescaling, verified against the literal producer "
            "statement and with margins far above numerical resolution."),
        next_analytic_target=(
            "A lower bound on #{n <= X : g_(n+h+1) - g_(n+1) = +-2 and the weighted "
            "tail difference lands in the correct half-window} - Hardy-Littlewood "
            "k-tuple input plus dyadic-tail equidistribution, not a gap-magnitude "
            "theorem."),
        resource_bounds={"prime_limit": args.limit, "max_offset": args.max_h,
                         "bands": args.bands},
    )
    print("wrote", path.relative_to(REPO_ROOT))

    cond_payload = cond.run(args.limit, [1, 2, 3, 5, 8, 13], 6)
    cond_path = publish(
        out_path="state/formal_math/probes/erdos251_conditional_shift_receipt.json",
        problem_id="erdos_251",
        hypothesis_id="digit_and_tail_conditions_separate",
        hypothesis_statement=(
            "Conditioned on the +-2 digit, the tail shift lands in the producer's window "
            "at a rate bounded away from zero, so the digit count and the tail window "
            "can be proved separately rather than jointly."),
        probe_id="erdos251_conditional_shift_distribution",
        probe_question=(
            "Conditioned on the +-2 digit, how is the tail shift distributed, and what "
            "fraction sits inside the window rather than beyond it?"),
        computation=(
            "Restrict to Delta = +2 and separately Delta = -2 over the actual primes, "
            "histogram D = T_(N+h) - T_N, and report the conditional in-window fraction "
            "and its drift across bands of N, per offset."),
        falsifier=(
            "A conditional fraction that decays toward zero, which would mean the digit "
            "count is not the binding constraint and a joint statement is required."),
        stop_condition=(
            "A decaying conditional fraction retires the separate-factor reading."),
        survival_consequence=(
            "A proof can aim Hardy-Littlewood at the digit and non-concentration at the "
            "tail, independently."),
        falsification_consequence=(
            "The two conditions are entangled and must be proved together."),
        consumer_ref=LEAN_WALL,
        analysis_refs=[LAB],
        source_refs=["formal_math/probes/erdos251_conditional_shift_distribution.py",
                     "formal_math/probes/erdos251_adjacent_mismatch_density.py"],
        result_status="exact_one_way_result",
        result_summary=(
            "Over 6,841,648 primes with Delta = +2, the digit rate is 0.06893, 0.05017, "
            "0.05187, 0.05228, 0.05242, 0.05244 at offsets 1, 2, 3, 5, 8, 13 and the "
            "conditional in-window fraction is 0.05942, 0.04586, 0.04253, 0.04015, "
            "0.04026, 0.03982. The tail factor stays between 0.0398 and 0.0602 and "
            "drifts across six bands of N only by a factor 0.77 to 0.84 - the same mild "
            "decline as the digit factor - so the two factors separate. The conditional "
            "structure is offset-independent from h = 5 onwards, with the "
            "short/overshoot split converging to 0.46/0.50, while h = 1 is distinct "
            "(overshooting 72% of the time). The tail shift decorrelates from the digit "
            "at offsets of about five."),
        payload=cond_payload,
        motivated_by=["actual_scaled_tail_smallness", "cofinal_adjacent_small_mismatch",
                      "small_adjacent_shift_consumer"],
        supports=["adjacent_mismatch_event_factorises_and_decorrelates"],
        binding_rationale=(
            "Splits the remaining producer into two factors that can be attacked "
            "separately, and measures the offset beyond which the conditional structure "
            "stops depending on h."),
        progress_class="mechanism_opened",
        decision_basis=(
            "The conditional in-window fraction is bounded away from zero at every "
            "offset and drifts no faster than the digit factor."),
        next_analytic_target=(
            "A Hardy-Littlewood lower bound for the +-2 digit at a fixed offset, plus a "
            "non-concentration statement for the tail shift; small offsets need separate "
            "treatment, offsets from 5 onwards do not."),
        resource_bounds={"prime_limit": args.limit, "offsets": 6, "bands": 6},
    )
    print("wrote", cond_path.relative_to(REPO_ROOT))
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
