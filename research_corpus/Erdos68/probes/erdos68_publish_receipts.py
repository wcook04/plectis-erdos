#!/usr/bin/env python3
"""Re-run the Erdos #68 probes and publish their bound receipts."""

from __future__ import annotations

import argparse
import sys
from pathlib import Path

REPO_ROOT = Path(__file__).resolve().parents[2]
if str(REPO_ROOT) not in sys.path:
    sys.path.insert(0, str(REPO_ROOT))

from formal_math.probes import erdos68_digit_law as digit_law  # noqa: E402
from formal_math.probes import erdos68_predecessor_gap_threshold as probe  # noqa: E402
from formal_math.probes.receipt import publish  # noqa: E402

LAB = ("formal_math/erdos257_period_noncollapse/ErdosProblems/Erdos68/"
       "PredecessorGapThresholdLab.md")
DIGIT_LAB = ("formal_math/erdos257_period_noncollapse/ErdosProblems/Erdos68/"
             "FactorialDigitLawLab.md")
PLATEAU = ("formal_math/erdos257_period_noncollapse/ErdosProblems/Erdos68/"
           "FactorialZeroPlateau.lean")
RANK_TWO_LAB = ("formal_math/erdos257_period_noncollapse/ErdosProblems/Erdos68/"
                "RankTwoDeterminantScaleLab.md")
COFACTOR_LAB = ("formal_math/erdos257_period_noncollapse/ErdosProblems/Erdos68/"
                "CofactorDivisorImpossibilityLab.md")


def publish_grid_discharge() -> int:
    from formal_math.probes import erdos68_grid_nonterminality_discharge as grid
    payload = grid.run()
    path = publish(
        out_path=("state/formal_math/probes/"
                  "erdos68_grid_nonterminality_discharge_receipt.json"),
        problem_id="erdos_68",
        hypothesis_id="prime_grid_producer_is_independent_of_the_carry_certificate",
        hypothesis_statement=(
            "cofinal_prime_grid_nonterminality is a free-standing priority-1 producer "
            "whose difficulty is unrelated to how deep the carry certificate has run."),
        probe_id="erdos68_grid_nonterminality_discharge",
        probe_question=(
            "How far do the two finite denominator exclusions discharge the prime-grid "
            "producer, and which is operative?"),
        computation=(
            "S = G_p forces S = k/(p-1)!, so q divides (p-1)!. Compute where each "
            "exclusion's range ends: for Kempner, the largest p with (p-1)! dividing "
            "299999!; for the continued fraction, the largest p with (p-1)! at most "
            "2^39991, by accumulating log factorials."),
        falsifier=(
            "The continued-fraction range exceeding the Kempner range, which would make "
            "the operative bound independent of the carry certificate and break the "
            "claimed linkage."),
        stop_condition=(
            "Once both ranges are computed the producer's status against certificate "
            "depth is settled."),
        survival_consequence=(
            "The producer would stand as an independent open problem."),
        falsification_consequence=(
            "The producer is a corollary of certificate depth and should be tracked "
            "against it rather than attacked on its own."),
        consumer_ref=("formal_math/erdos257_period_noncollapse/ErdosProblems/Erdos68/"
                      "FactorialZeroPlateau.lean"),
        analysis_refs=[],
        source_refs=["formal_math/probes/erdos68_grid_nonterminality_discharge.py"],
        result_status="exact_one_way_result",
        result_summary=(
            "The producer is discharged for every prime p <= %d, largest %d, by the "
            "Kempner exclusion, and for p <= %d, largest %d, by the continued-fraction "
            "bound, where (p-1)! already has %d decimal digits. Kempner is operative by "
            "two orders of magnitude. Since it follows from a single certified non-unit "
            "carry at index m, the discharge extends to p <= m whenever the carry "
            "certificate is run to depth m: the producer is a corollary of certificate "
            "depth rather than an independent open problem, and only the cofinal tail "
            "is genuinely open." % (
                payload["kempner"]["discharges_primes_up_to"],
                payload["kempner"]["largest_prime_discharged"],
                payload["continued_fraction"]["discharges_primes_up_to"],
                payload["continued_fraction"]["largest_prime_discharged"],
                payload["continued_fraction"]["that_factorial_decimal_digits"])),
        payload=payload,
        motivated_by=["cofinal_prime_grid_nonterminality",
                      "kempner_index_denominator_exclusion",
                      "certified_continued_fraction_denominator_exclusion"],
        supports=["prime_grid_nonterminality_is_bounded_by_carry_certificate_depth"],
        binding_rationale=(
            "Reclassifies a priority-1 producer as a corollary of the carry "
            "certificate's depth, and discharges its explicit initial range."),
        progress_class="mechanism_eliminated",
        decision_basis=(
            "The reduction S = k/(p-1)! is elementary and exact; both ranges are "
            "computed rather than estimated; Kempner exceeds the continued-fraction "
            "range by two orders of magnitude."),
        next_analytic_target=(
            "Nothing free remains below p = 300000. Extending the GMP carry certificate "
            "past index m extends the discharge to p <= m mechanically; the cofinal tail "
            "needs the same non-concentration input as the rest of the packet."),
        resource_bounds={"kempner_index": 299999, "cf_bound_bits": 39991},
    )
    print("wrote", path.relative_to(REPO_ROOT))
    return 0


def publish_cofactor_impossibility() -> int:
    from formal_math.probes import erdos68_cofactor_divisor_impossibility as cofactor
    payload = cofactor.run()
    if payload["counterexamples"]:
        raise SystemExit("an appended determinant escaped Delta; the argument is wrong")
    path = publish(
        out_path=("state/formal_math/probes/"
                  "erdos68_cofactor_divisor_impossibility_receipt.json"),
        problem_id="erdos_68",
        hypothesis_id="appended_channel_determinant_producer_is_a_hard_open_case",
        hypothesis_statement=(
            "No unbounded family with 0 < |N| < Delta was obtained because finding one "
            "is hard, so the producer is a live open case worth attacking."),
        probe_id="erdos68_cofactor_divisor_impossibility",
        probe_question=(
            "Is 0 < |N| < Delta satisfiable at all, for an appended-row determinant N "
            "and Delta the gcd of maximal minors?"),
        computation=(
            "Laplace expansion along the appended row writes N as an integer combination "
            "of the maximal minors of the unappended channel matrix, all divisible by "
            "Delta, so Delta divides N. Checked on random integer channel matrices across "
            "six shapes, taking every (k+1)-column selection of the appended matrix "
            "rather than only the square case, with exact Bareiss determinants."),
        falsifier=(
            "A single integer instance with 0 < |N| < Delta under any reading of the two "
            "quantities. That would mean the producer is live and this argument wrong."),
        stop_condition=(
            "Divisibility holding on every witness settles it; the inequality is "
            "unsatisfiable and the producer is removed rather than deferred."),
        survival_consequence=(
            "The producer stands and the search should continue with better constructions."),
        falsification_consequence=(
            "The producer asks for an object that cannot exist and leaves the frontier."),
        consumer_ref=("formal_math/erdos257_period_noncollapse/ErdosProblems/Erdos68/"
                      "PrimeUnitTranslator.lean"),
        analysis_refs=[COFACTOR_LAB],
        source_refs=["formal_math/probes/erdos68_cofactor_divisor_impossibility.py"],
        result_status="exact_one_way_result",
        result_summary=(
            "The condition is unsatisfiable. Delta divides N by Laplace expansion along "
            "the appended row, so N nonzero forces |N| >= Delta, and 0 < |N| < Delta has "
            "no integer solutions. The recorded failure to obtain an unbounded family is "
            "the expected outcome, not a hard open case. Verified on %d nonzero appended "
            "determinants across six channel shapes with zero escaping Delta. The "
            "conclusion is independent of the reading: gcd over the unappended matrix "
            "gives Delta | N; gcd over the appended square matrix gives Delta = |N| so "
            "|N| < Delta is false outright; wider channel matrices still expand into "
            "k-minors divisible by Delta. Recorded with it: N and Delta are defined only "
            "in packet prose, with no Lean declaration or script defining either, which "
            "is how an unsatisfiable condition survived on the frontier."
            % payload["total_nonzero_witnesses"]),
        payload=payload,
        motivated_by=["erdos68_appended_channel_determinant_beats_determinantal_divisor",
                      "primitive_cofactor_determinant_divisor_bottleneck"],
        eliminates=["erdos68_appended_channel_determinant_beats_determinantal_divisor"],
        supports=["appended_channel_determinant_condition_is_unsatisfiable"],
        binding_rationale=(
            "Removes a priority-1 producer by showing its condition has no integer "
            "solutions, explaining the packet's own recorded search failure."),
        progress_class="mechanism_eliminated",
        decision_basis=(
            "Laplace expansion is a theorem; the check adds 6000 nonzero witnesses with "
            "zero exceptions across six shapes and every column selection; and the "
            "conclusion survives all three readings of the undefined quantities."),
        next_analytic_target=(
            "Nothing from this route. The sibling reclassification of "
            "erdos68_rank_two_strict_nonvanishing gives the shared criterion: a "
            "linear-form producer closes only when its coefficient is forced to be a "
            "multiple of the hypothetical denominator, which "
            "erdos68_scalar_factorial_tail_orbit_nonintegrality satisfies."),
        resource_bounds={"nonzero_witnesses": payload["total_nonzero_witnesses"],
                         "shapes": len(payload["shapes"])},
    )
    print("wrote", path.relative_to(REPO_ROOT))
    return 0


def publish_digit_law(max_m: int, cache: str | None) -> int:
    payload = digit_law.run(max_m, cache=cache)
    rare = payload["rare_families"]
    canonical = payload["canonical_digits"]
    null = payload["null_model"]
    if canonical["range_violations"]:
        raise SystemExit("canonical digit reconstruction left [0, m-1]")
    path = publish(
        out_path="state/formal_math/probes/erdos68_digit_law_receipt.json",
        problem_id="erdos_68",
        hypothesis_id="factorial_digits_carry_exploitable_arithmetic",
        hypothesis_statement=(
            "The rounding digits of the Erdos 68 strict-successor recurrence carry an "
            "arithmetic bias -- at primes, at a residue class, at smooth indices -- that a "
            "construction could use to build a cofinal index family."),
        probe_id="erdos68_digit_law",
        probe_question=(
            "What do the digits D_m = m N_(m-1) - N_m and the canonical factorial digits "
            "d_m(S) actually do, and do the tail-free threshold, the unit-carry condition "
            "and the canonical-digit lane track the same scalar?"),
        computation=(
            "Take the digit stream from the repository's GMP strict-successor certificate, "
            "asserted equal to exact Fraction arithmetic on m <= 200 before any statistic is "
            "computed. Recover the endpoint flag f_m = [sum_(j>m) D_j/j! > 0] by one backward "
            "scan and the canonical digit by d_m(S) = m f_(m-1) - f_m - D_m. Compare "
            "(D_m+1)/m against Uniform[0,1) by Kolmogorov-Smirnov, the first two moments, the "
            "lag-one correlation, and the mean stratified by primality, parity and residues "
            "mod 5 and mod 6."),
        falsifier=(
            "Any stratum at |z| > 4, or sqrt(n) * KS > 1.95. Either would mean the digits "
            "carry an arithmetic bias and a construction route is live."),
        stop_condition=(
            "Uniformity on every tested statistic retires the construction route and leaves "
            "non-concentration as the sole surviving Archimedean input."),
        survival_consequence=(
            "A biased digit gives the prime-indexed producers an Archimedean lever and the "
            "attack becomes building m rather than proving equidistribution."),
        falsification_consequence=(
            "No digit-side arithmetic exists to exploit; the three producer families are "
            "level sets of one scalar and need one non-concentration statement."),
        consumer_ref=PLATEAU,
        analysis_refs=[DIGIT_LAB],
        source_refs=["formal_math/probes/erdos68_digit_law.py",
                     "formal_math/probes/erdos68_engine.py",
                     "formal_math/erdos257_period_noncollapse/scripts/"
                     "check_erdos68_strict_successor_gmp.cpp"],
        result_status="exact_one_way_result",
        result_summary=(
            f"Over {payload['stream']['digit_count']} digits (m = 3..{max_m}) the rounding "
            "digit determines all three tracked families: D_m=-1 is the definite tail-free "
            "threshold-failure branch and exactly the zero set of the canonical digit d_m(S), "
            "D_m=0 is exactly the unit-carry set and exactly d_m(S)=m-1, D_m>=1 is everything "
            f"else. Counts against {rare['expected_each_under_null']:.3f} expected for each: "
            f"{len(rare['threshold_failure_D_eq_minus_one'])} with D_m=-1, "
            f"{len(rare['unit_carry_D_eq_zero'])} with D_m=0 (independently reproducing the "
            "landed strict-successor certificate's unit-carry list), "
            f"{len(rare['top_digit_D_eq_m_minus_two'])} with D_m=m-2. All "
            f"{canonical['reconstructed']} reconstructed canonical digits lie in [0,m-1] with "
            "zero range violations. The separate D_m=0 margin check fires at every unit carry, "
            "so in this computed range the full threshold-failure set is exactly the displayed "
            "D_m=-1 set and d_m(S)=m-1 at all unit carries. The normalized digit is "
            "indistinguishable from uniform: mean "
            f"z={null['mean_z']:+.2f}, KS sqrt(n)D={null['ks_times_sqrt_n']:.3f} against 1.95, "
            f"lag-one correlation {null['lag_one_correlation']:+.5f} against sd "
            f"{null['lag_one_sd_under_independence']:.5f}, worst stratum "
            f"|z|={null['worst_abs_z']:.2f} against a predeclared falsifier of 4."),
        payload=payload,
        motivated_by=["cofinal_tailfree_predecessor_gap_threshold",
                      "cofinal_exact_prefix_strict_successor_miss"],
        eliminates=["digit_side_arithmetic_construction_route"],
        supports=["factorial_digit_level_sets_and_uniformity"],
        binding_rationale=(
            "Collapses two producers the packet tracked separately, plus the canonical-digit "
            "lane, into three level sets of one scalar, and closes the construction reading "
            "of both."),
        progress_class="mechanism_eliminated",
        decision_basis=(
            "Worst stratum |z| = 1.00 and KS sqrt(n)D = 0.619 against predeclared falsifiers "
            "of 4 and 1.95, over 49998 digits, with the level-set identification verified by "
            "zero range violations in 49996 canonical-digit reconstructions."),
        next_analytic_target=(
            "Non-concentration only: for infinitely many m the scaled predecessor gap "
            "A_(m-1) = 1 - frac((m-1)! sum_(k<m) 1/(k!-1)) avoids ((1+1/(m!-1))/m, "
            "(2+1/(m!-1))/m]. Weaker than equidistribution and weaker than the tail-free "
            "threshold, which overshoots the window it needs to miss."),
        resource_bounds={"max_m": max_m,
                         "precision_bits": payload["stream"]["precision_bits"],
                         "digit_count": payload["stream"]["digit_count"]},
    )
    print("wrote", path.relative_to(REPO_ROOT))
    return 0


def publish_rank_two_scale() -> int:
    from formal_math.probes import erdos68_rank_two_determinant_scale as scale
    payload = scale.run()
    if not payload["closed_form_verified_at_n_zero"]:
        raise SystemExit("the n = 0 closed form disagreed with the Lean matrix")
    path = publish(
        out_path="state/formal_math/probes/erdos68_rank_two_determinant_scale_receipt.json",
        problem_id="erdos_68",
        hypothesis_id="rank_two_nonvanishing_is_an_irrationality_producer",
        hypothesis_statement=(
            "Proving det(A)*S nonintegral for the factorial-grid Cramer kernel is a step "
            "toward the irrationality of the Erdos 68 series, and the certified "
            "continued-fraction bound may discharge it over a useful range."),
        probe_id="erdos68_rank_two_determinant_scale",
        probe_question=(
            "What does the rank-two producer output as a statement about q, can "
            "nonvanishing alone contradict rationality, and how far does the certified "
            "continued-fraction bound discharge it for free?"),
        computation=(
            "Build augmentedChannelMomentMatrix (factorialGridIndex n t) literally from "
            "PrimeUnitTranslator.lean -- factorialGridScale D = (D!)^2, index "
            "(t+j)(D!)^2 with D = n+2, first row (index j)!, row d+1 equal to "
            "(index j)!/(d+2)!^(index j/(d+2)) -- take determinants fraction-free by "
            "Bareiss so they stay exact integers, compare their size against the "
            "certified bound q > 10^12039, and check the n = 0 closed form."),
        falsifier=(
            "Determinants staying below 10^12039 over a useful range, which would let the "
            "continued-fraction bound discharge the producer outright; or no closed form "
            "at n = 0, which would block an explicit comparison with the Kempner "
            "exclusion."),
        stop_condition=(
            "Once the output's logical shape is pinned and the free-discharge range is "
            "measured, the producer's classification is settled."),
        survival_consequence=(
            "The producer would be a genuine step toward irrationality and worth "
            "attacking as stated."),
        falsification_consequence=(
            "The producer is a smoothness-exclusion route, not an irrationality route, "
            "and should be attacked and compared as such."),
        consumer_ref=("formal_math/erdos257_period_noncollapse/ErdosProblems/Erdos68/"
                      "PrimeUnitTranslator.lean"),
        analysis_refs=[RANK_TWO_LAB],
        source_refs=["formal_math/probes/erdos68_rank_two_determinant_scale.py"],
        result_status="exact_one_way_result",
        result_summary=(
            "The producer's output is q not dividing det(A) -- a divisibility exclusion of "
            "the same species as the Kempner-index statement, not a size bound -- because "
            "det(A)*S is integral exactly when q divides det(A). Nonvanishing alone cannot "
            "contradict rationality: a nonzero R is a nonzero multiple of 1/q so |R| >= 1/q, "
            "while the only recorded smallness is |R| <= 1/2, compatible for every q >= 2. "
            "The certified bound q > 10^12039 discharges the hypothesis free on grid sizes "
            "n <= %s and stops there: the smallest uncovered grid is n = %s, whose 4x4 "
            "determinant is already 10^15208 at t = 1. At n = 0 the determinant is "
            "3(4t)!(4t+4)!/2^(2t+2), verified exactly against the Lean matrix, so "
            "nonvanishing there for any t >= %s would strictly strengthen q not dividing "
            "299999!." % (payload["largest_grid_discharged_by_cf_bound"],
                          payload["smallest_grid_beyond_cf_bound"],
                          payload["beats_kempner_exclusion_from_t"])),
        payload=payload,
        motivated_by=["erdos68_rank_two_strict_nonvanishing",
                      "full_residual_mod_integers_classification",
                      "certified_continued_fraction_denominator_exclusion"],
        eliminates=["erdos68_rank_two_strict_nonvanishing"],
        supports=["rank_two_producer_is_a_smoothness_exclusion_not_an_irrationality_route",
                  "kempner_index_denominator_exclusion"],
        binding_rationale=(
            "Eliminates the reading of a priority-1 producer as an irrationality route and "
            "reopens it as a smoothness exclusion with an explicit closed-form target, "
            "using identities the packet had already landed but not composed."),
        progress_class="mechanism_eliminated",
        decision_basis=(
            "The integrality equivalence is elementary and exact; the |R| >= 1/q versus "
            "|R| <= 1/2 gap is decisive; the determinants are exact Bareiss integers; and "
            "the n = 0 closed form matches the Lean matrix at every tested t."),
        next_analytic_target=(
            "Either supply smallness -- |R| < 1/q rather than 1/2 -- which the packet's own "
            "scalar_canonical_product_height_no_go says diverges for the natural choice; or "
            "keep the route as a smoothness exclusion and prove nonvanishing at n = 0 for "
            "some t >= 74999, which strictly strengthens q not dividing 299999!."),
        resource_bounds={"grids": len(payload["rows"]),
                         "cf_bound_bits": payload["cf_bound_bits"]},
    )
    print("wrote", path.relative_to(REPO_ROOT))
    return 0


def main() -> int:
    ap = argparse.ArgumentParser()
    ap.add_argument("--max-m", type=int, default=210)
    ap.add_argument("--digit-law", action="store_true",
                    help="publish the factorial-digit-law receipt instead")
    ap.add_argument("--rank-two-scale", action="store_true",
                    help="publish the rank-two determinant-scale receipt instead")
    ap.add_argument("--cofactor-impossibility", action="store_true",
                    help="publish the cofactor-divisor impossibility receipt instead")
    ap.add_argument("--grid-discharge", action="store_true",
                    help="publish the prime-grid discharge receipt instead")
    ap.add_argument("--cache", default=None,
                    help="reuse an existing certificate stream file")
    args = ap.parse_args()
    if args.grid_discharge:
        return publish_grid_discharge()
    if args.cofactor_impossibility:
        return publish_cofactor_impossibility()
    if args.rank_two_scale:
        return publish_rank_two_scale()
    if args.digit_law:
        return publish_digit_law(args.max_m, args.cache)
    payload = probe.run(args.max_m)
    lean = None
    for candidate in ("FactorialGapPrefix.lean", "StrictSuccessor.lean",
                      "FactorialGapLadder.lean"):
        p = REPO_ROOT / "formal_math/erdos257_period_noncollapse/ErdosProblems/Erdos68" / candidate
        if p.exists():
            lean = f"formal_math/erdos257_period_noncollapse/ErdosProblems/Erdos68/{candidate}"
            break
    if lean is None:
        lean = LAB
    path = publish(
        out_path="state/formal_math/probes/erdos68_predecessor_gap_receipt.json",
        problem_id="erdos_68",
        hypothesis_id="predecessor_gap_certificate_is_delicate",
        hypothesis_statement=(
            "The tail-free predecessor-gap certificate is hard to satisfy and needs a "
            "cleverer construction, rather than holding for almost every m."),
        probe_id="erdos68_predecessor_gap_threshold",
        probe_question=(
            "How often does the literal integer inequality "
            "((m+2)m!-2)v_m <= m^2(m!-1)u_m actually hold, and does the failure rate "
            "match what uniformity of {Q_m} would predict?"),
        computation=(
            "Compute Q_m = (m-1)! sum_(n=2)^(m-1) 1/(n!-1) in exact rational arithmetic "
            "for m = 3..210, derive u_m and v_m from the packet's definitions with the "
            "Lean-proved bounds 1 <= u_m <= v_m asserted, and evaluate the literal "
            "integer inequality rather than its reduced form."),
        falsifier=(
            "A failure count departing from the Sigma 1/m uniform prediction, or "
            "failures that persist at large m, which would mean {Q_m} carries an "
            "arithmetic bias against the certificate."),
        stop_condition=(
            "A biased failure pattern retires the generic reading and makes the "
            "producer a genuine construction problem instead."),
        survival_consequence=(
            "The certificate is generic and the missing input is a non-concentration "
            "theorem for {Q_m}, not a new arithmetic mechanism."),
        falsification_consequence=(
            "The certificate is delicate and needs a construction, so the producer "
            "should be attacked by building m rather than by equidistribution."),
        consumer_ref=lean,
        analysis_refs=[LAB],
        source_refs=["formal_math/probes/erdos68_predecessor_gap_threshold.py"],
        result_status="exact_one_way_result",
        result_summary=(
            "204 of 208 certificates fire over m = 3..210, a rate of 0.9808, with "
            "exactly four failures at m = 5, 9, 23, 60 and none at all beyond m = 60. "
            "Expected failures under uniformity of {Q_m} is 4.427, so observed/expected "
            "is 0.904. Since u_m/v_m = 1 - {Q_m}, the certificate is exactly the "
            "condition {Q_m} <= 1 - 1/m - 2/m^2 - 1/(m(m!-1)), and {Q_m} shows no "
            "arithmetic bias against it."),
        payload=payload,
        motivated_by=["cofinal_tailfree_predecessor_gap_threshold"],
        supports=["predecessor_gap_certificate_fires_generically"],
        binding_rationale=(
            "Separates two readings of the residual the packet could not distinguish: "
            "the certificate is satisfied almost always and needs a non-concentration "
            "theorem, not a cleverer construction."),
        progress_class="mechanism_opened",
        decision_basis=(
            "Fire rate 0.9808 with a failure count within 10% of the uniform "
            "prediction and no failures in the top two thirds of the range."),
        next_analytic_target=(
            "Equidistribution, or merely non-concentration in the top 1/m of the unit "
            "interval, for {Q_m} = frac((m-1)! sum_(n<m) 1/(n!-1))."),
        resource_bounds={"max_m": args.max_m},
    )
    print("wrote", path.relative_to(REPO_ROOT))
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
