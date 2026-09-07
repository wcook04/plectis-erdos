import ErdosProblems.Erdos251.OrderLatticeDiagonal
import ErdosProblems.Erdos251.PaperCoreR7
import ErdosProblems.Erdos251.PaperTailBoundsR7
import ErdosProblems.Erdos251.PaperFiniteCertificatesR7
import ErdosProblems.Erdos251.PaperNonconcentrationR7
import ErdosProblems.Erdos251.PaperBoundedCarryR7
import ErdosProblems.Erdos251.PaperSparseCouplingR7

/-!
# Main round-7 proof-source build target

This file is not a receipt: it has not been run in the return environment.
It deliberately excludes PaperLargeCertificateR7, whose million-index
kernel sieve is a separate, potentially expensive target.

The supplied ResidueFeedbackCore remains its original uncompiled candidate;
this build does not misrepresent it as a proof of the full sparse theorem.
-/

#print axioms ErdosProblems.Erdos251.irrational_initial_iff_all_lcmDiagonal_nonintegral
#print axioms ErdosProblems.Erdos251.PaperR7.polynomial_countermodel
#print axioms ErdosProblems.Erdos251.PaperR7.infinite_prime_gap_identity
#print axioms ErdosProblems.Erdos251.PaperR7.irrationality_reformulation
#print axioms ErdosProblems.Erdos251.PaperR7.block_identity
#print axioms ErdosProblems.Erdos251.PaperR7.real_block_identity
#print axioms ErdosProblems.Erdos251.PaperR7.rationality_classification
#print axioms ErdosProblems.Erdos251.PaperR7.eventual_integral_positive_shift
#print axioms ErdosProblems.Erdos251.PaperR7.real_signed_two_window
#print axioms ErdosProblems.Erdos251.PaperR7.affine_circularity_bundle
#print axioms ErdosProblems.Erdos251.PaperR7.rational_small_pair_bundle
#print axioms ErdosProblems.Erdos251.PaperR7.real_small_pair_bundle
#print axioms ErdosProblems.Erdos251.PaperR7.real_small_pair_prime_endpoint
#print axioms ErdosProblems.Erdos251.PaperR7.prime_gaps_not_eventually_periodic
#print axioms ErdosProblems.Erdos251.PaperR7.actual_free_pair_criterion
#print axioms ErdosProblems.Erdos251.PaperR7.rational_bounded_perturbation
#print axioms ErdosProblems.Erdos251.PaperR7.explicit_remainder_certificate
#print axioms ErdosProblems.Erdos251.PaperR7.cofinal_escape_of_finite_truncation
#print axioms ErdosProblems.Erdos251.PaperR7.irrational_prime_series_of_finite_truncation
#print axioms ErdosProblems.Erdos251.PaperR7.finite_small_pair
#print axioms ErdosProblems.Erdos251.PaperR7.denominator_floor_both
#print axioms ErdosProblems.Erdos251.PaperR7.finite_perturbation_stability
#print axioms ErdosProblems.Erdos251.PaperR7.prime_perturbation_of_nonconcentration
#print axioms ErdosProblems.Erdos251.PaperR7.small_mismatch_zeroDensity_of_nonconcentration
#print axioms ErdosProblems.Erdos251.PaperR7.bounded_recurring_values_countermodel
#print axioms ErdosProblems.Erdos251.PaperR7.block_test_sum_difference_le
#print axioms ErdosProblems.Erdos251.PaperR7.block_event_count_difference_le
