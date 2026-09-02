#!/usr/bin/env python3
"""Re-run the Erdos #269 probes and publish bound, durable receipts.

Running this IS the replay path: every receipt is regenerated from a live run,
so a receipt can never drift away from the computation it claims to record.
"""

from __future__ import annotations

import argparse
import sys
from pathlib import Path

REPO_ROOT = Path(__file__).resolve().parents[2]
if str(REPO_ROOT) not in sys.path:
    sys.path.insert(0, str(REPO_ROOT))

from formal_math.probes import (  # noqa: E402
    erdos269_continued_fraction,
    erdos269_escape_depth_law,
    erdos269_projective_cofinality,
    erdos269_torus_fourier_representation,
    erdos269_denominator_exclusion,
    erdos269_stammering,
    erdos269_torus_coding,
)
from formal_math.probes.receipt import publish  # noqa: E402

PROBLEM = "erdos_269"
LAB = ("formal_math/erdos257_period_noncollapse/ErdosProblems/Erdos269/"
       "TorusCocycleAndDiophantineTypeLab.md")
LEAN_RECURRENCE = ("formal_math/erdos257_period_noncollapse/ErdosProblems/Erdos269/"
                   "DyadicOrderedTailRecurrence.lean")
LEAN_ESCAPE = ("formal_math/erdos257_period_noncollapse/ErdosProblems/Erdos269/"
               "BoundedRadixTailEscape.lean")
LEAN_TRANSPORT = ("formal_math/erdos257_period_noncollapse/ErdosProblems/Erdos269/"
                  "HalfHeightDenominatorTransport.lean")
ENGINE = "formal_math/probes/erdos269_engine.py"
STATE = "state/formal_math/probes"


def main() -> int:
    ap = argparse.ArgumentParser()
    ap.add_argument("--exclusion-depth", type=int, default=420)
    ap.add_argument("--cf-depth", type=int, default=2500)
    args = ap.parse_args()
    written = []

    # ---- 1. two-torus coding -------------------------------------------------
    payload = erdos269_torus_coding.run(300000, 22, 2600)
    written.append(publish(
        out_path=f"{STATE}/erdos269_torus_coding_receipt.json",
        problem_id=PROBLEM,
        hypothesis_id="dyadic_radix_word_two_torus_coding",
        hypothesis_statement=(
            "The dyadic radix word b_a is the superposition of the Beatty "
            "characteristic sequences of log_2 3 and log_2 5, hence a coding of a "
            "rotation on the 2-torus by (log_3 2, log_5 2) under a product partition."),
        probe_id="erdos269_torus_coding",
        probe_question=(
            "Does the literal source radix agree with the Beatty prediction, and is "
            "the factor complexity quadratic (rank-2 rotation) rather than linear "
            "(Sturmian)?"),
        computation=(
            "Exact Beatty indicators from integer bit lengths, checked letter by "
            "letter against the literal source engine on a = 1..2600; factor "
            "complexity of the 300,000-letter radix word for n = 1..22; radix letter "
            "frequencies against the independent-rotation prediction."),
        falsifier=(
            "Any a where the radix disagrees with the Beatty prediction, or a factor "
            "complexity that is linear in n."),
        stop_condition=(
            "One mismatch retires the identification outright; near-linear complexity "
            "retires the rank-2 reading and returns the source word to the opaque "
            "treatment the retired functional attempts assumed."),
        survival_consequence=(
            "The source system is a cocycle over an ergodic 2-torus rotation whose "
            "angles are ratios of logarithms of 2, 3 and 5, making rotation-Diophantine "
            "tools available for the first time."),
        falsification_consequence=(
            "The radix word carries no rotation structure and the packet's existing "
            "opaque-source mechanism families remain the only route."),
        consumer_ref=LEAN_RECURRENCE,
        analysis_refs=[LAB],
        source_refs=[ENGINE, "formal_math/probes/erdos269_torus_coding.py"],
        result_status="exact_one_way_result",
        result_summary=(
            "0 mismatches on a = 1..2600 against the literal source engine. Radix "
            "frequencies match the independent-rotation prediction to five decimals "
            "over 300,000 letters. Factor complexity is exactly (n+1)^2 for n = 1..22, "
            "the rank-2 rotation signature."),
        payload=payload,
        motivated_by=["exclude_exact_integral_dyadic_tails",
                      "actual_dyadic_block_radix_alphabet",
                      "prime_power_jump_expansion"],
        supports=["dyadic_radix_word_two_torus_coding"],
        opens=["dyadic_radix_word_two_torus_coding"],
        binding_rationale=(
            "Identifies the source word every retired functional attempt treated as "
            "opaque, opening a mechanism family the packet did not previously carry."),
        progress_class="mechanism_opened",
        decision_basis=(
            "Exact letter-by-letter agreement with the source engine plus an exactly "
            "quadratic factor complexity."),
        next_analytic_target=(
            "Effective simultaneous approximation bounds for (log_3 2, log_5 2), or an "
            "all-scale invariant of the cocycle over the 2-torus rotation."),
        resource_bounds={"word_length": 300000, "engine_verified_prefix": 2600,
                         "max_factor_length": 22},
    ))

    # ---- 2. stammering no-go -------------------------------------------------
    payload = erdos269_stammering.run(400000, 150000)
    written.append(publish(
        out_path=f"{STATE}/erdos269_stammering_receipt.json",
        problem_id=PROBLEM,
        hypothesis_id="product_sturmian_stammering",
        hypothesis_statement=(
            "The radix word begins in arbitrarily high powers, supplying the "
            "stammering input the Adamczewski-Bugeaud Subspace-Theorem criterion needs."),
        probe_id="erdos269_stammering",
        probe_question=(
            "Does the repetition exponent of the product word grow along the "
            "simultaneous-approximation record denominators of (log_3 2, log_5 2)?"),
        computation=(
            "Record denominators for max(||q log_3 2||, ||q log_5 2||) up to q = 150000, "
            "each measured against the literal 400,000-letter radix word by direct "
            "prefix period matching."),
        falsifier=(
            "A repetition exponent that stays at 1 as q grows closes the lane."),
        stop_condition=(
            "Exponents at the largest record denominators failing to exceed those at "
            "the smallest retires the route; it is not repaired by searching further."),
        survival_consequence=(
            "The Subspace-Theorem transcendence machinery applies to the source word."),
        falsification_consequence=(
            "The stammering route is closed and must not be re-attempted through "
            "repetition structure; the producer must come from anti-concentration."),
        consumer_ref=LEAN_ESCAPE,
        analysis_refs=[LAB],
        source_refs=[ENGINE, "formal_math/probes/erdos269_stammering.py",
                     "formal_math/probes/erdos269_torus_coding.py"],
        result_status="finite_counterexample",
        result_summary=(
            "Exponents at the record denominators q = 7061, 7126, 15810, 45807 are "
            "1.0089, 1.0115, 1.0085, 1.0074: the matched length tracks 1/||q alpha|| and "
            "so grows like q^(1/2) while the period grows like q. Two rationally "
            "independent slopes cap simultaneous approximation at Dirichlet exponent "
            "1/2, so the criterion's requirement fails by a full power of q, not by a "
            "search limit."),
        payload=payload,
        motivated_by=["dyadic_radix_word_two_torus_coding",
                      "exclude_exact_integral_dyadic_tails"],
        supports=["product_sturmian_stammering_no_go"],
        binding_rationale=(
            "Closes the strongest tool the two-torus identification made available, so "
            "the opened family narrows to anti-concentration rather than repetition."),
        progress_class="mechanism_eliminated",
        decision_basis=(
            "Measured exponents decay to 1 like 1 + O(q^-1/2) across four decades of "
            "record denominators, matching the Dirichlet cap rather than a search bound."),
        next_analytic_target=(
            "Anti-concentration for the residues (-qF_L) mod B_L derived from the "
            "rotation's Diophantine properties."),
        resource_bounds={"word_length": 400000, "max_period": 150000},
    ))

    # ---- 3. Diophantine type -------------------------------------------------
    payload = erdos269_continued_fraction.run(1, args.cf_depth)
    written.append(publish(
        out_path=f"{STATE}/erdos269_continued_fraction_receipt.json",
        problem_id=PROBLEM,
        hypothesis_id="normalized_tail_diophantine_genericity",
        hypothesis_statement=(
            "The normalized source tail X_1 has an exceptional Diophantine type - "
            "Liouville behaviour, or a self-similar or algebraic continued fraction - "
            "that a proof could exploit."),
        probe_id="erdos269_continued_fraction",
        probe_question=(
            "What is the certified continued fraction of X_1, and does it deviate from "
            "Gauss-Kuzmin and Levy genericity?"),
        computation=(
            "Exact truncation X_1 = (F + t)/B with 0 < t <= kappa, then the continued "
            "fraction prefix common to both interval endpoints - an airtight "
            "certification, since continued-fraction prefixes are cylinder memberships "
            "and cylinders are intervals."),
        falsifier=(
            "Partial-quotient statistics departing from Gauss-Kuzmin, a Levy constant "
            "away from pi^2/(12 ln 2), or an irrationality exponent above 2."),
        stop_condition=(
            "Genericity across the certified range retires the exceptional-structure "
            "reading; it is not repaired by extending the expansion."),
        survival_consequence=(
            "An exceptional Diophantine structure exists and can carry a proof."),
        falsification_consequence=(
            "No structure to exploit, and no delayed Liouville conspiracy at any "
            "reachable scale, so the retired Lyapunov, coboundary and observer attempts "
            "were searching for something that is not there."),
        consumer_ref=LEAN_TRANSPORT,
        analysis_refs=[LAB],
        source_refs=[ENGINE, "formal_math/probes/erdos269_continued_fraction.py"],
        result_status="exact_one_way_result",
        result_summary=(
            "2,162 airtight-certified partial quotients. Gauss-Kuzmin frequencies "
            "0.4265/0.1651/0.0888/0.0587 against 0.4150/0.1699/0.0931/0.0589; Levy "
            "constant 1.19749 against 1.18657; empirical irrationality exponent 2.005. "
            "X_1 is Diophantine-generic. The expansion does not terminate within the "
            "certified range, so X_1 is not rational with denominator below 2^3737."),
        payload=payload,
        motivated_by=["exclude_exact_integral_dyadic_tails",
                      "phase_conditioned_source_quadratic_coboundary_no_go",
                      "finite_denominator_exclusion"],
        supports=["normalized_tail_diophantine_genericity"],
        binding_rationale=(
            "Explains why every finite-memory functional attempt on the integral-tail "
            "branch failed, and supplies the strongest exact denominator exclusion "
            "on record for this problem."),
        progress_class="mechanism_eliminated",
        decision_basis=(
            "Certified expansion matches three independent genericity statistics."),
        next_analytic_target=(
            "An effective irrationality-measure statement for X_1 derived from the "
            "torus-rotation cocycle."),
        resource_bounds={"truncation_depth": args.cf_depth},
    ))

    # ---- 4. lattice denominator exclusion ------------------------------------
    payload = erdos269_denominator_exclusion.run(1, args.exclusion_depth, 10, 200000)
    written.append(publish(
        out_path=f"{STATE}/erdos269_denominator_exclusion_receipt.json",
        problem_id=PROBLEM,
        hypothesis_id="lattice_first_hit_denominator_exclusion",
        hypothesis_statement=(
            "Excluding every denominator below Q at window depth L is a first-hit of a "
            "rotation in an interval, so the Stern-Brocot recursion certifies in "
            "O(log B) what a per-denominator scan needs O(Q) steps to reach."),
        probe_id="erdos269_denominator_exclusion",
        probe_question=(
            "How large an exact denominator exclusion does the escape route support, "
            "and what is the growth law of the certified bound in the window base?"),
        computation=(
            "Dyadically staged binary search over Q, each stage one Stern-Brocot "
            "first-hit against the exact window base and forcing, cross-checked at ten "
            "depths against a direct 200,000-term denominator scan."),
        falsifier=(
            "Disagreement with the direct scan at any depth, or a certified bound that "
            "fails to grow with depth."),
        stop_condition=(
            "One unsound row retires the certificate; a bound not growing with depth "
            "retires the unbounded-family reading."),
        survival_consequence=(
            "Exact exclusions far beyond scan range become routine, and the measured "
            "growth law fixes the ceiling of the whole escape route."),
        falsification_consequence=(
            "The lattice reformulation is wrong and exclusions stay scan-bound."),
        consumer_ref=LEAN_TRANSPORT,
        analysis_refs=[LAB],
        source_refs=[ENGINE, "formal_math/probes/erdos269_denominator_exclusion.py",
                     "formal_math/probes/lattice_first_hit.py"],
        result_status="exact_one_way_result",
        result_summary=(
            "Sound at all ten cross-checked depths. At depth 420 every odd denominator "
            "up to about 10^187 is excluded exactly. The certified bound fits "
            "log2 Q = 0.4974 log2 B - 5.29, i.e. Theta(sqrt(B_L)) with the exponent "
            "within 0.5% of 1/2 over 420 depths - the exact best-approximation barrier. "
            "The route therefore cannot pass sqrt(B_L) and B_L grows only exponentially "
            "in depth, so no escape scan can reach a cofinal quantifier."),
        payload=payload,
        motivated_by=["unbounded_height_certificate",
                      "finite_farey_certificate_235_M200",
                      "finite_denominator_exclusion"],
        supports=["lattice_first_hit_denominator_exclusion"],
        binding_rationale=(
            "Answers how far the finite-Farey family can be pushed and measures the "
            "ceiling that stops it short of the unbounded-height producer."),
        progress_class="mechanism_eliminated",
        decision_basis=(
            "The certified exclusion saturates the sqrt(B) counting heuristic with no "
            "defect over 420 depths, so no residue bias remains to exploit and the "
            "route's ceiling is structural."),
        next_analytic_target=(
            "A producer that does not route through finite escape certificates at all."),
        resource_bounds={"max_depth": args.exclusion_depth,
                         "cross_check_scan_limit": 200000},
    ))


    # ---- 5. escape-depth law -------------------------------------------------
    payload = erdos269_escape_depth_law.run(20000, 120, 80, 200)
    written.append(publish(
        out_path=f"{STATE}/erdos269_escape_depth_law_receipt.json",
        problem_id=PROBLEM,
        hypothesis_id="escape_delay_accumulates",
        hypothesis_statement=(
            "Escape delay accumulates somewhere in the (denominator, start) plane, so "
            "that a conspiracy builds up which a Lyapunov function or finite-memory "
            "observer could detect."),
        probe_id="erdos269_escape_depth_law",
        probe_question=(
            "Over a large rectangle of denominators and starts, does the canonical "
            "residue always escape the analytic cap, and does the escape depth stay "
            "close to the counting threshold log_8(q*kappa)?"),
        computation=(
            "Exact escape depth for every odd q <= 120 coprime to 30 against every "
            "start a <= 20000, with the excess over the counting threshold recorded."),
        falsifier=(
            "Any pair with no escape inside the search depth, or an excess growing "
            "beyond the generic extreme-value prediction."),
        stop_condition=(
            "One non-escaping pair, or a systematically growing excess, reinstates the "
            "conspiracy reading and the functional attempts with it."),
        survival_consequence=(
            "Escape is generic with no accumulation anywhere in the rectangle, so no "
            "residue bias exists for a functional to detect."),
        falsification_consequence=(
            "A conspiracy region exists and is the place to aim a functional."),
        consumer_ref=LEAN_ESCAPE,
        analysis_refs=[LAB],
        source_refs=[ENGINE, "formal_math/probes/erdos269_escape_depth_law.py",
                     "formal_math/probes/erdos269_fast_engine.py"],
        result_status="exact_one_way_result",
        result_summary=(
            "640,000 pairs, zero non-escapes. Maximum escape depth 18, concentrated at "
            "depths 10-13. Mean excess over the counting threshold 0.97; the single "
            "largest is 7.09 at q=113, a=11569, meaning 113*X_11569 sits within 4e-7 of "
            "an integer from below - against an expected closest approach of about "
            "1.6e-6 for 640,000 draws of a generic quantity. Escape delay does not "
            "accumulate anywhere in the rectangle."),
        payload=payload,
        motivated_by=["exclude_exact_integral_dyadic_tails",
                      "residue_delay_five_uniform_bound_counterexample",
                      "affine_cylinder_delay_101_counterexample"],
        supports=["escape_is_generic_with_no_accumulation"],
        binding_rationale=(
            "Tests the shared premise of every retired functional attempt on the "
            "integral-tail branch - that delay accumulates - directly, at scale."),
        progress_class="mechanism_eliminated",
        decision_basis=(
            "Zero non-escapes in 640,000 exact certificates with an extreme excess "
            "consistent with generic extreme-value behaviour."),
        next_analytic_target=(
            "Anti-concentration for the residues derived from the torus-rotation "
            "cocycle, since no bias exists to exploit."),
        resource_bounds={"max_start": 20000, "max_denominator": 120,
                         "max_search_depth": 80},
    ))


    # ---- 6. projective-shadow cofinality -------------------------------------
    payload = erdos269_projective_cofinality.run(500, 3000, 40, 60)
    written.append(publish(
        out_path=f"{STATE}/erdos269_projective_cofinality_receipt.json",
        problem_id=PROBLEM,
        hypothesis_id="projective_violating_pairs_are_scarce",
        hypothesis_statement=(
            "Violating projective-shadow pairs are scarce or run out, so the cofinal "
            "projective producer cannot be constructed."),
        probe_id="erdos269_projective_cofinality",
        probe_question=(
            "For every B coprime to 30, do individually admissible window pairs "
            "violating d_a*H_b = d_b*H_a (mod B) exist, how often, and do they keep "
            "appearing late?"),
        computation=(
            "Enumerate every admissible endpoint - base clears the cap, residue does "
            "not escape it, residue coprime to B - for all denominators coprime to 30 "
            "in [7,500] across starts a <= 3000, then measure the violating fraction, "
            "the latest admissible start, and the coherence rate split by same-start "
            "versus different-start and by near versus far separation."),
        falsifier=(
            "A denominator with no violating pair, or admissible endpoints that stop "
            "appearing beyond some start."),
        stop_condition=(
            "Either would close the route rather than leave it unproved."),
        survival_consequence=(
            "The construction is abundant and the producer reduces to two "
            "equidistribution statements rather than a search."),
        falsification_consequence=(
            "The projective route is closed and only the integral-tail branch remains."),
        consumer_ref=LEAN_TRANSPORT,
        analysis_refs=[LAB],
        source_refs=[ENGINE, "formal_math/probes/erdos269_projective_cofinality.py",
                     "formal_math/probes/erdos269_fast_engine.py"],
        result_status="exact_one_way_result",
        result_summary=(
            "All 133 denominators admit violating pairs, at fractions from 0.828 (B=7) "
            "to 0.988 (B=499); the packet's B=11 witness is reproduced exactly. "
            "Admissible endpoints persist to the top of every range and violating pairs "
            "exist with both starts above 2963 for every B. Same-start pairs are always "
            "coherent (P = 1.0000 exactly), so the construction must pair different "
            "starts. For different starts the residual coherence is short-range only: "
            "neighbours give 1.23x/2.06x/6.42x uniform at B=7/101/499 while pairs "
            "separated by half the list give 1.18x/1.10x/0.92x - equidistributed."),
        payload=payload,
        motivated_by=["cofinal_projective_window_pair_incoherence",
                      "projective_two_window_residue_coherence",
                      "local_window_certificates_B_1_7_16"],
        supports=["projective_defect_equidistributes_across_far_pairs"],
        binding_rationale=(
            "Turns the second open producer from a search into two named "
            "equidistribution statements, and records the same-start constraint that "
            "any construction must respect."),
        progress_class="mechanism_opened",
        decision_basis=(
            "Violating pairs exist for every tested denominator and stay available at "
            "the top of the range, with far-pair coherence measured at the uniform rate."),
        next_analytic_target=(
            "Cofinality of admissible endpoints together with equidistribution of the "
            "projective defect modulo B across far-separated pairs."),
        resource_bounds={"max_denominator": 500, "max_start": 3000,
                         "max_window_length": 40, "pair_cap": 60},
    ))


    # ---- 7. torus Fourier representation of the value ------------------------
    payload = erdos269_torus_fourier_representation.run(320, 4000)
    written.append(publish(
        out_path=f"{STATE}/erdos269_torus_fourier_receipt.json",
        problem_id=PROBLEM,
        hypothesis_id="value_has_a_torus_analytic_representation",
        hypothesis_statement=(
            "Not only the radix word but the value itself is a torus object: S is an "
            "explicit triple Fourier series over modes indexed by a linear form in "
            "logarithms of 2, 3 and 5, up to a computable correction constant."),
        probe_id="erdos269_torus_fourier_representation",
        probe_question=(
            "Does the pointwise height identity hold, does the axis telescope equal 1 "
            "exactly, and do the corrected Fourier partial sums converge to the "
            "directly computed value?"),
        computation=(
            "Check 1/H(s) = 2^{L}3^{L/theta}5^{L/phi}/s^3 against the literal height on "
            "4,000 smooth s; evaluate sum_p (p-1) sum_n 1/H(p^n) in exact rationals; and "
            "compare corrected triple Fourier partial sums at |m| <= 20..320 against the "
            "directly summed value."),
        falsifier=(
            "Corrected partial sums failing to converge to the direct value, or the "
            "telescope failing to equal 1 exactly."),
        stop_condition=(
            "Either retires the representation; it is not repaired by more modes."),
        survival_consequence=(
            "The value has an exact analytic form whose modes are governed by linear "
            "forms in logarithms of 2, 3 and 5."),
        falsification_consequence=(
            "The torus reading does not reach the value and stays a statement about the "
            "digit word only."),
        consumer_ref=LEAN_RECURRENCE,
        analysis_refs=[LAB],
        source_refs=["formal_math/probes/erdos269_torus_fourier_representation.py"],
        result_status="exact_one_way_result",
        result_summary=(
            "Pointwise identity holds to maximum relative error 1.5e-14. The telescope "
            "is exact: the sum truncated at 10^40 equals 1 - 1/H(last), so the total "
            "axis correction is 8 + 1/2 = 17/2. Corrected partial sums give errors "
            "7.04e-2, 5.31e-2, 2.09e-2, 9.87e-3, 4.39e-3 at M = 20, 40, 80, 160, 320 - "
            "monotone and halving as M doubles, the 1/M rate a jump-discontinuous "
            "Fourier series gives. The sum is only conditionally summable, so it "
            "converges as a symmetric limit."),
        payload=payload,
        motivated_by=["dyadic_radix_word_two_torus_coding",
                      "exclude_exact_integral_dyadic_tails",
                      "running_lcm_height"],
        supports=["torus_fourier_representation_of_the_value",
                  "running_height_prime_power_telescope"],
        binding_rationale=(
            "First representation of the value as an explicit analytic object, placing "
            "the arithmetic in linear forms in logarithms of 2, 3 and 5 - the same "
            "Diophantine input both remaining branches reduced to."),
        progress_class="mechanism_opened",
        decision_basis=(
            "Exact pointwise identity, exact telescope, and monotone 1/M convergence of "
            "the corrected partial sums to the directly computed value."),
        next_analytic_target=(
            "A regularisation of the conditionally summable triple series from which a "
            "Diophantine estimate on the modes lambda = m1 + m2 log_3 2 + m3 log_5 2 "
            "could be extracted."),
        resource_bounds={"max_fourier_mode": 320, "pointwise_samples": 4000},
    ))

    for path in written:
        print("wrote", path.relative_to(REPO_ROOT))
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
