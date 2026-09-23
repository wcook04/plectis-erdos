import ErdosProblems.Erdos1049.PaperR20.SourcePadeCorrection
import ErdosProblems.Erdos1049.PaperR20.LambertPolynomialPartLimit

/-!
# Evaluated source Padé identities

This module begins the analytic passage from the unconditional bivariate Padé
identity.  It records the exact clearing balance and evaluates that identity
at zero and at every numerator root.  These are unconditional polynomial
consequences; no rational-kernel decomposition or target remainder is assumed.
-/

namespace ErdosProblems.Erdos1049.PaperR20

open Finset Polynomial
open scoped BigOperators

noncomputable section

/-- The source choices of `d` and `e` satisfy the exponent balance used by
`momentRationalKernel_clear`, for every `m`, including `m=0,1`. -/
theorem sourceQuotient_clearing_balance (m : ℕ) :
    (∑ j ∈ range (m + 1), (m + 1 + j)) + sourceQuotientClearD m =
      4 * (∑ j ∈ range m, (j + 1)) + sourceQuotientClearE m := by
  have hm := PaperR12.twice_choose_two_nat m
  have hms := PaperR12.twice_choose_two_nat (m + 1)
  have hde := sourceQuotientClearD_sub_E m
  have hL : ∑ j ∈ range (m + 1), (m + 1 + j) = (m + 1) * (m + 1) + (m + 1).choose 2 := by
    rw [Finset.sum_add_distrib, Finset.sum_const, Finset.card_range, smul_eq_mul,
      Finset.sum_range_id, Nat.choose_two_right]
  have hR : ∑ j ∈ range m, (j + 1) = m.choose 2 + m := by
    rw [Finset.sum_add_distrib, Finset.sum_const, Finset.card_range, smul_eq_mul, mul_one,
      Finset.sum_range_id, Nat.choose_two_right]
  rw [← Nat.choose_two_right] at hde
  have hsq : (m + 1) * (m + 1) = m * m + 2 * m + 1 := by ring
  rw [hL, hR]
  omega

/-- The cleared source numerator vanishes at the origin. -/
theorem evalBivariate_clearedMomentNumeratorPoly_zero
    (m : ℕ) (p : ℝ) :
    evalBivariate
        (clearedMomentNumeratorPoly m (sourceQuotientClearE m)) p 0 = 0 := by
  simp [clearedMomentNumeratorPoly, evalBivariate]

/-- The cleared source numerator vanishes at each of its literal numerator
roots `p^(s+1)`, `s<m`. -/
theorem evalBivariate_clearedMomentNumeratorPoly_at_source_root
    (m s : ℕ) (hs : s < m) (p : ℝ) :
    evalBivariate
        (clearedMomentNumeratorPoly m (sourceQuotientClearE m))
        p (p ^ (s + 1)) = 0 := by
  have hfactor :
      ∏ j ∈ range m, (p ^ (j + 1) - p ^ (s + 1)) = 0 := by
    apply Finset.prod_eq_zero (mem_range.mpr hs)
    simp
  have hX : parameterEval p X = p := by simp [parameterEval]
  simp only [clearedMomentNumeratorPoly, evalBivariate_mul, evalBivariate_pow,
    evalBivariate_X, evalBivariate_prod, evalBivariate_sub, evalBivariate_C,
    map_pow, hX, hfactor, mul_zero]

/-- Evaluation at zero of the unconditional source partial-fraction identity.
This is the raw polynomial equation from which constant cancellation is
obtained by evaluating the displayed products. -/
theorem sourcePade_partial_fraction_at_zero (m : ℕ) (p : ℝ) :
    evalBivariate
      (sourceClearedQuotientPoly m * clearedMomentDenominatorPoly m +
        residueCertificatePoly m (sourceQuotientClearD m)
          (fun k => sourceResiduePoly m k.val)) p 0 = 0 := by
  rw [← sourcePade_partial_fraction_identity m]
  exact evalBivariate_clearedMomentNumeratorPoly_zero m p

/-- Evaluation at every numerator root of the unconditional source
partial-fraction identity.  After the zero-evaluation cancellation and division
by the nonzero denominator, this is exactly the `hzero` input of
`kernelZero_correction_identity`. -/
theorem sourcePade_partial_fraction_at_numerator_root
    (m s : ℕ) (hs : s < m) (p : ℝ) :
    evalBivariate
      (sourceClearedQuotientPoly m * clearedMomentDenominatorPoly m +
        residueCertificatePoly m (sourceQuotientClearD m)
          (fun k => sourceResiduePoly m k.val))
      p (p ^ (s + 1)) = 0 := by
  rw [← sourcePade_partial_fraction_identity m]
  exact evalBivariate_clearedMomentNumeratorPoly_at_source_root m s hs p

#print axioms sourceQuotient_clearing_balance
#print axioms sourcePade_partial_fraction_at_zero
#print axioms sourcePade_partial_fraction_at_numerator_root

end
end ErdosProblems.Erdos1049.PaperR20
