import ErdosProblems.Erdos1049.PaperR20.SourcePadePoleEvaluation
import Mathlib.Algebra.Polynomial.Roots

/-!
# Unconditional all-index Padé partial fraction identity

The generating function determines the polynomial quotient through reversal at
infinity.  The remaining polynomial has degree at most `m`.  Its values at the
`m+1` distinct denominator roots are the explicit source residues, so root
counting identifies it with the residue certificate.
-/

namespace ErdosProblems.Erdos1049.PaperR20

open Finset Polynomial
open scoped BigOperators

noncomputable section

private def sourceOuterNumeratorCore (m : ℕ) : BivariatePolynomial :=
  X ^ (m + 1) * ∏ j ∈ range m, (C ((X : ℤ[X]) ^ (j + 1)) - X)

private def sourceOuterQuotientCore (m : ℕ) : BivariatePolynomial :=
  ∑ l ∈ range (m + 1), C (sourceInfinityTriangularCoeff m l) * X ^ (m - l)

private theorem natDegree_linear_le (a : ParameterPolynomial) :
    (C a - (X : BivariatePolynomial)).natDegree ≤ 1 := by
  exact (natDegree_sub_le _ _).trans (by simp)

private theorem natDegree_prod_linear_le (n shift : ℕ) :
    (∏ j ∈ range n,
      (C ((X : ParameterPolynomial) ^ (shift + j)) - X : BivariatePolynomial)).natDegree ≤ n := by
  calc
    _ ≤ ∑ j ∈ range n,
        (C ((X : ParameterPolynomial) ^ (shift + j)) - X : BivariatePolynomial).natDegree :=
      natDegree_prod_le _ _
    _ ≤ ∑ _j ∈ range n, 1 := Finset.sum_le_sum fun j hj => natDegree_linear_le _
    _ = n := by simp

private theorem natDegree_sourceOuterQuotientCore_le (m : ℕ) :
    (sourceOuterQuotientCore m).natDegree ≤ m := by
  unfold sourceOuterQuotientCore
  refine natDegree_sum_le_of_forall_le (range (m + 1))
    (fun l => C (sourceInfinityTriangularCoeff m l) * X ^ (m - l)) ?_
  intro l hl
  exact (natDegree_C_mul_le _ _).trans
    ((natDegree_X_pow_le (m - l)).trans (Nat.sub_le m l))

private theorem reflect_prod_C_sub_X (n shift : ℕ) :
    (∏ j ∈ range n,
      (C ((X : ParameterPolynomial) ^ (shift + j)) - X : BivariatePolynomial)).reflect n =
      (-1 : BivariatePolynomial) ^ n *
        ∏ j ∈ range n,
          (1 - C ((X : ParameterPolynomial) ^ (shift + j)) * X) := by
  induction n with
  | zero => simp
  | succ n ih =>
      rw [Finset.prod_range_succ, Finset.prod_range_succ]
      rw [reflect_mul _ _ (natDegree_prod_linear_le n shift)
        (natDegree_linear_le ((X : ParameterPolynomial) ^ (shift + n)))]
      rw [ih, reflect_sub, reflect_C, reflect_one_X]
      ring

private theorem reflect_sourceOuterQuotientCore (m : ℕ) :
    (sourceOuterQuotientCore m).reflect m = sourceInfinityQuotientPoly m := by
  ext n : 1
  simp only [sourceOuterQuotientCore, sourceInfinityQuotientPoly,
    coeff_reflect, finset_sum_coeff, coeff_C_mul_X_pow]
  by_cases hn : n ≤ m
  · rw [revAt_le hn]
    apply Finset.sum_congr rfl
    intro b hb
    have hb' : b ≤ m := Nat.le_of_lt_succ (Finset.mem_range.mp hb)
    by_cases hnb : n = b
    · subst hnb
      simp
    · rw [if_neg hnb, if_neg (show ¬(m - n = m - b) by omega)]
  · have hmn : m < n := Nat.lt_of_not_ge hn
    rw [revAt_eq_self_of_lt hmn]
    apply Finset.sum_congr rfl
    intro b hb
    have hb' : b ≤ m := Nat.le_of_lt_succ (Finset.mem_range.mp hb)
    rw [if_neg (show ¬(n = m - b) by omega), if_neg (show ¬(n = b) by omega)]

private theorem reflect_sourceOuterNumeratorCore (m : ℕ) :
    (sourceOuterNumeratorCore m).reflect (2 * m + 1) =
      (-1 : BivariatePolynomial) ^ m * sourceInfinityNumeratorPoly m := by
  unfold sourceOuterNumeratorCore sourceInfinityNumeratorPoly
  have hshift :
      (∏ j ∈ range m,
        (C ((X : ParameterPolynomial) ^ (j + 1)) - X : BivariatePolynomial)) =
        ∏ j ∈ range m,
          (C ((X : ParameterPolynomial) ^ (1 + j)) - X : BivariatePolynomial) :=
    Finset.prod_congr rfl fun j _ => by rw [Nat.add_comm j 1]
  have hshift' :
      (∏ j ∈ range m,
        (1 - C ((X : ParameterPolynomial) ^ (j + 1)) * X : BivariatePolynomial)) =
        ∏ j ∈ range m,
          (1 - C ((X : ParameterPolynomial) ^ (1 + j)) * X : BivariatePolynomial) :=
    Finset.prod_congr rfl fun j _ => by rw [Nat.add_comm j 1]
  have hprod := natDegree_prod_linear_le m 1
  have hx : (X ^ (m + 1) : BivariatePolynomial).natDegree ≤ m + 1 :=
    natDegree_X_pow_le _
  rw [hshift, hshift', show 2 * m + 1 = (m + 1) + m by omega,
    reflect_mul _ _ hx hprod, reflect_monomial,
    revAt_le (show m + 1 ≤ m + 1 by omega), Nat.sub_self, pow_zero, one_mul,
    reflect_prod_C_sub_X]

private theorem reflect_cleared_denominator (m : ℕ) :
    (clearedMomentDenominatorPoly m).reflect (m + 1) =
      (-1 : BivariatePolynomial) ^ (m + 1) *
        sourceInfinityDenominatorPoly m := by
  simpa [clearedMomentDenominatorPoly, sourceInfinityDenominatorPoly]
    using reflect_prod_C_sub_X (m + 1) (m + 1)

private theorem natDegree_sourceOuterNumeratorCore_le (m : ℕ) :
    (sourceOuterNumeratorCore m).natDegree ≤ 2 * m + 1 := by
  unfold sourceOuterNumeratorCore
  have hshift :
      (∏ j ∈ range m,
        (C ((X : ParameterPolynomial) ^ (j + 1)) - X : BivariatePolynomial)) =
        ∏ j ∈ range m,
          (C ((X : ParameterPolynomial) ^ (1 + j)) - X : BivariatePolynomial) :=
    Finset.prod_congr rfl fun j _ => by rw [Nat.add_comm j 1]
  rw [hshift]
  exact natDegree_mul_le.trans (by
    have hp := natDegree_prod_linear_le m 1
    have hx := natDegree_X_pow_le (R := ParameterPolynomial) (m + 1)
    omega)

private theorem natDegree_cleared_denominator_le (m : ℕ) :
    (clearedMomentDenominatorPoly m).natDegree ≤ m + 1 := by
  simpa [clearedMomentDenominatorPoly] using
    natDegree_prod_linear_le (m + 1) (m + 1)

private theorem natDegree_source_core_residual_le (m : ℕ) :
    (sourceOuterNumeratorCore m +
      sourceOuterQuotientCore m * clearedMomentDenominatorPoly m).natDegree ≤
        2 * m + 1 := by
  apply (natDegree_add_le _ _).trans
  apply max_le
  · exact natDegree_sourceOuterNumeratorCore_le m
  · exact natDegree_mul_le.trans (by
      have hq := natDegree_sourceOuterQuotientCore_le m
      have hd := natDegree_cleared_denominator_le m
      omega)

private theorem natDegree_le_of_reflect_X_pow_dvd
    (P : BivariatePolynomial) (m : ℕ)
    (hdeg : P.natDegree ≤ 2 * m + 1)
    (hdvd : (X : BivariatePolynomial) ^ (m + 1) ∣ P.reflect (2 * m + 1)) :
    P.natDegree ≤ m := by
  rw [natDegree_le_iff_coeff_eq_zero]
  intro n hmn
  by_cases hn : n ≤ 2 * m + 1
  · let l := 2 * m + 1 - n
    have hl : l < m + 1 := by dsimp [l]; omega
    have hz := (Polynomial.X_pow_dvd_iff.mp hdvd) l hl
    rw [coeff_reflect, revAt_le (show l ≤ 2 * m + 1 by dsimp [l]; omega)] at hz
    have hrev : 2 * m + 1 - l = n := by dsimp [l]; omega
    simpa [hrev] using hz
  · exact coeff_eq_zero_of_natDegree_lt (lt_of_le_of_lt hdeg (Nat.lt_of_not_ge hn))

private theorem reflect_source_core_residual (m : ℕ) :
    (sourceOuterNumeratorCore m +
        sourceOuterQuotientCore m * clearedMomentDenominatorPoly m).reflect
        (2 * m + 1) =
      (-1 : BivariatePolynomial) ^ m *
        (sourceInfinityNumeratorPoly m -
          sourceInfinityDenominatorPoly m * sourceInfinityQuotientPoly m) := by
  rw [reflect_add, reflect_sourceOuterNumeratorCore]
  rw [show 2 * m + 1 = m + (m + 1) by omega,
    reflect_mul _ _ (natDegree_sourceOuterQuotientCore_le m)
      (natDegree_cleared_denominator_le m),
    reflect_sourceOuterQuotientCore, reflect_cleared_denominator]
  ring

private theorem natDegree_source_core_residual_at_most (m : ℕ) :
    (sourceOuterNumeratorCore m +
      sourceOuterQuotientCore m * clearedMomentDenominatorPoly m).natDegree ≤ m := by
  apply natDegree_le_of_reflect_X_pow_dvd _ m
    (natDegree_source_core_residual_le m)
  rw [reflect_source_core_residual]
  exact dvd_mul_of_dvd_right
    (source_infinity_polynomial_remainder_X_pow_dvd m)
    ((-1 : BivariatePolynomial) ^ m)

private theorem cleared_difference_eq_scaled_core (m : ℕ) :
    clearedMomentNumeratorPoly m (sourceQuotientClearE m) -
        sourceClearedQuotientPoly m * clearedMomentDenominatorPoly m =
      C (X ^ sourceQuotientClearE m * sourceDeltaPoly m ^ 3) *
        (sourceOuterNumeratorCore m +
          sourceOuterQuotientCore m * clearedMomentDenominatorPoly m) := by
  rw [sourceClearedQuotientPoly_eq_reversed]
  unfold clearedMomentNumeratorPoly sourceOuterNumeratorCore sourceOuterQuotientCore
  unfold sourceDeltaPoly
  simp only [map_neg, map_mul, map_pow]
  ring

private theorem natDegree_cleared_difference_le (m : ℕ) :
    (clearedMomentNumeratorPoly m (sourceQuotientClearE m) -
      sourceClearedQuotientPoly m * clearedMomentDenominatorPoly m).natDegree ≤ m := by
  rw [cleared_difference_eq_scaled_core]
  exact (natDegree_C_mul_le _ _).trans (natDegree_source_core_residual_at_most m)

private theorem natDegree_denominatorExcept_le (m : ℕ) (k : Fin (m + 1)) :
    (clearedMomentDenominatorExceptPoly m k.val).natDegree ≤ m := by
  unfold clearedMomentDenominatorExceptPoly
  calc
    _ ≤ ∑ j ∈ (range (m + 1)).erase k.val,
        (C ((X : ParameterPolynomial) ^ (m + 1 + j)) - X : BivariatePolynomial).natDegree :=
      natDegree_prod_le _ _
    _ ≤ ∑ _j ∈ (range (m + 1)).erase k.val, 1 :=
      Finset.sum_le_sum fun j hj => natDegree_linear_le _
    _ ≤ m := by
      simp [Finset.card_erase_of_mem (Finset.mem_range.mpr k.isLt)]

private theorem natDegree_residueCertificate_le (m : ℕ) :
    (residueCertificatePoly m (sourceQuotientClearD m)
      (fun k => sourceResiduePoly m k.val)).natDegree ≤ m := by
  unfold residueCertificatePoly
  exact (natDegree_C_mul_le _ _).trans <|
    natDegree_sum_le_of_forall_le Finset.univ
      (fun k : Fin (m + 1) =>
        C (sourceResiduePoly m k.val * X ^ (m + 1 + k.val)) *
          clearedMomentDenominatorExceptPoly m k.val) fun k hk =>
      natDegree_mul_le.trans <| by
        have hd := natDegree_denominatorExcept_le m k
        rw [natDegree_C, zero_add]
        exact hd

private theorem eval_cleared_denominator_at_pole_zero
    (m : ℕ) (k : Fin (m + 1)) :
    (clearedMomentDenominatorPoly m).eval
      ((X : ParameterPolynomial) ^ (m + 1 + k.val)) = 0 := by
  unfold clearedMomentDenominatorPoly
  rw [eval_prod]
  apply Finset.prod_eq_zero (i := k.val) (Finset.mem_range.mpr k.isLt)
  simp

private theorem eval_residueCertificate_at_pole
    (m : ℕ) (k : Fin (m + 1)) :
    (residueCertificatePoly m (sourceQuotientClearD m)
      (fun r => sourceResiduePoly m r.val)).eval
        ((X : ParameterPolynomial) ^ (m + 1 + k.val)) =
      X ^ sourceQuotientClearD m * sourceResiduePoly m k.val *
        X ^ (m + 1 + k.val) *
        (clearedMomentDenominatorExceptPoly m k.val).eval
          ((X : ParameterPolynomial) ^ (m + 1 + k.val)) := by
  unfold residueCertificatePoly
  simp only [eval_mul, eval_C, eval_finset_sum]
  rw [Finset.sum_eq_single k]
  · ring
  · intro r _ hrk
    have hvals : k.val ≠ r.val := by
      intro h
      apply hrk
      exact Fin.ext h.symm
    have hk_mem : k.val ∈ (range (m + 1)).erase r.val := by
      simp [k.isLt, hvals]
    have hz :
        (clearedMomentDenominatorExceptPoly m r.val).eval
          ((X : ParameterPolynomial) ^ (m + 1 + k.val)) = 0 := by
      unfold clearedMomentDenominatorExceptPoly
      rw [eval_prod]
      apply Finset.prod_eq_zero (i := k.val) hk_mem
      simp
    rw [hz, mul_zero]
  · intro hk
    exact (hk (Finset.mem_univ k)).elim

private theorem source_partial_fraction_residual_eval_zero
    (m : ℕ) (k : Fin (m + 1)) :
    (clearedMomentNumeratorPoly m (sourceQuotientClearE m) -
        (sourceClearedQuotientPoly m * clearedMomentDenominatorPoly m +
          residueCertificatePoly m (sourceQuotientClearD m)
            (fun r => sourceResiduePoly m r.val))).eval
      ((X : ParameterPolynomial) ^ (m + 1 + k.val)) = 0 := by
  rw [eval_sub, eval_add, eval_mul, eval_cleared_denominator_at_pole_zero,
    mul_zero, zero_add, eval_residueCertificate_at_pole]
  exact sub_eq_zero.mpr
    (eval_clearedMomentNumeratorPoly_at_pole m k.val (Nat.le_of_lt_succ k.isLt))

private theorem polePower_injective (m : ℕ) :
    Function.Injective (fun k : Fin (m + 1) =>
      (X : ParameterPolynomial) ^ (m + 1 + k.val)) := by
  intro a b hab
  have hd := congrArg Polynomial.natDegree hab
  simp only [natDegree_X_pow] at hd
  exact Fin.ext (by omega)

/-- **Unconditional all-index partial fraction identity.** -/
theorem sourcePade_partial_fraction_identity (m : ℕ) :
    clearedMomentNumeratorPoly m (sourceQuotientClearE m) =
      sourceClearedQuotientPoly m * clearedMomentDenominatorPoly m +
        residueCertificatePoly m (sourceQuotientClearD m)
          (fun k => sourceResiduePoly m k.val) := by
  apply sub_eq_zero.mp
  apply eq_zero_of_natDegree_lt_card_of_eval_eq_zero _ (polePower_injective m)
  · exact source_partial_fraction_residual_eval_zero m
  · have hleft := natDegree_cleared_difference_le m
    have hres := natDegree_residueCertificate_le m
    have hdeg :
        (clearedMomentNumeratorPoly m (sourceQuotientClearE m) -
          (sourceClearedQuotientPoly m * clearedMomentDenominatorPoly m +
            residueCertificatePoly m (sourceQuotientClearD m)
              (fun k => sourceResiduePoly m k.val))).natDegree ≤ m := by
      have := natDegree_sub_le
        (clearedMomentNumeratorPoly m (sourceQuotientClearE m) -
          sourceClearedQuotientPoly m * clearedMomentDenominatorPoly m)
        (residueCertificatePoly m (sourceQuotientClearD m)
          (fun k => sourceResiduePoly m k.val))
      rw [sub_sub] at this
      exact this.trans (max_le hleft hres)
    simpa using Nat.lt_succ_of_le hdeg

#print axioms sourcePade_partial_fraction_identity

end
end ErdosProblems.Erdos1049.PaperR20
