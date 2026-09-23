import ErdosProblems.Erdos1049.PaperR20.SourcePadePartialFraction
import ErdosProblems.Erdos1049.PaperR20.KernelZeroCorrection

/-!
# The finite source correction attached to the Padé quotient

This module extracts the literal positive outer coefficients of the all-index
Padé quotient, removes their forced geometric denominators, and packages the
result with the already explicit residue quotients.  The resulting polynomial
is the finite correction on the right side of
`kernelZero_correction_identity`.

The identification of this source correction with the paper's `β_m` is left
to the analytic uniqueness argument; it is not assumed here.
-/

namespace ErdosProblems.Erdos1049.PaperR20

open Finset Polynomial
open scoped BigOperators

noncomputable section

/-- The product `Delta_m` with its `j`th factor removed. -/
def sourceDeltaExceptPoly (m j : ℕ) : ParameterPolynomial :=
  ∏ r ∈ (range m).erase j, (X ^ (r + 1) - 1)

theorem sourceDelta_factor (m j : ℕ) (hj : j < m) :
    sourceDeltaPoly m =
      (X ^ (j + 1) - 1) * sourceDeltaExceptPoly m j := by
  unfold sourceDeltaPoly sourceDeltaExceptPoly
  exact (Finset.mul_prod_erase (range m)
    (fun r : ℕ => (X : ParameterPolynomial) ^ (r + 1) - 1)
    (mem_range.mpr hj)).symm

/-- The coefficient of the positive outer power `Y^(j+1)` in the concrete
cleared quotient (the outer polynomial variable is written `Y` here only in
the prose). -/
def sourceQuotientPositiveCoeff (m : ℕ) (j : Fin m) : ParameterPolynomial :=
  sourceClearedQuotientCoeff m (m - (j.val + 1))

/-- Remove one forced copy of `X^(j+1)-1` from the positive quotient
coefficient.  Two untouched copies remain in `Delta_m^3`. -/
def sourceQuotientQuotientPoly (m : ℕ) (j : Fin m) : ParameterPolynomial :=
  -(sourceDeltaExceptPoly m j.val * sourceDeltaPoly m ^ 2 *
    X ^ (((m - (j.val + 1) + 1).choose 2) + sourceQuotientClearE m) *
    sourceNormalizedTriangularCoeff m (m - (j.val + 1)))

theorem sourceQuotientPositiveCoeff_factor (m : ℕ) (j : Fin m) :
    sourceQuotientPositiveCoeff m j =
      (X ^ (j.val + 1) - 1) * sourceQuotientQuotientPoly m j := by
  rw [sourceQuotientPositiveCoeff, sourceClearedQuotientCoeff,
    sourceQuotientQuotientPoly, sourceDelta_factor m j.val j.isLt]
  ring

/-- The shifted positive quotient coefficient after removing both its
geometric denominator and the global clearing power `X^d`.  Polynomiality is
termwise at the shifted evaluation point; it does not use cancellation
between different quotient coefficients. -/
def sourceShiftedQuotientCorrectionPoly (m : ℕ) (j : Fin m) :
    ParameterPolynomial :=
  -(sourceDeltaExceptPoly m j.val * sourceDeltaPoly m ^ 2 *
    X ^ (((m + 1) * (j.val + 1) +
      (m - (j.val + 1) + 1).choose 2 + sourceQuotientClearE m) -
        sourceQuotientClearD m) *
    sourceNormalizedTriangularCoeff m (m - (j.val + 1)))

private theorem sourceQuotientClearD_le_shiftedExponent
    (m : ℕ) (j : Fin m) :
    sourceQuotientClearD m ≤
      (m + 1) * (j.val + 1) +
        (m - (j.val + 1) + 1).choose 2 + sourceQuotientClearE m := by
  let a := m - (j.val + 1) + 1
  have ha : a + j.val = m := by
    dsimp [a]
    omega
  have hm2 := PaperR12.twice_choose_two_nat m
  have ha2 := PaperR12.twice_choose_two_nat a
  have hchoose : m.choose 2 ≤ (m + 1) * (j.val + 1) + a.choose 2 := by
    nlinarith
  have hde := sourceQuotientClearD_sub_E m
  rw [← Nat.choose_two_right] at hde
  dsimp [a] at hchoose
  omega

/-- Exact removal of the global clearing power from every shifted quotient
term used by the kernel-zero correction. -/
theorem sourceShiftedQuotientCorrection_scale (m : ℕ) (j : Fin m) :
    X ^ sourceQuotientClearD m * sourceShiftedQuotientCorrectionPoly m j =
      X ^ ((m + 1) * (j.val + 1)) * sourceQuotientQuotientPoly m j := by
  unfold sourceShiftedQuotientCorrectionPoly sourceQuotientQuotientPoly
  have hle := sourceQuotientClearD_le_shiftedExponent m j
  have hpow : (X : ParameterPolynomial) ^ sourceQuotientClearD m *
      X ^ (((m + 1) * (j.val + 1) +
        (m - (j.val + 1) + 1).choose 2 + sourceQuotientClearE m) -
          sourceQuotientClearD m) =
      X ^ ((m + 1) * (j.val + 1)) *
        X ^ (((m - (j.val + 1) + 1).choose 2) + sourceQuotientClearE m) := by
    rw [← pow_add, ← pow_add]
    congr 1
    omega
  linear_combination (-(sourceDeltaExceptPoly m j.val * sourceDeltaPoly m ^ 2 *
    sourceNormalizedTriangularCoeff m (m - (j.val + 1)))) * hpow

/-- Coefficient extraction from the descending-power presentation of the
cleared quotient. -/
theorem coeff_sourceClearedQuotientPoly (m r : ℕ) (hr : r ≤ m) :
    (sourceClearedQuotientPoly m).coeff r =
      sourceClearedQuotientCoeff m (m - r) := by
  rw [sourceClearedQuotientPoly, finset_sum_coeff, Finset.sum_eq_single (m - r)]
  · rw [coeff_C_mul, show m - (m - r) = r by omega, coeff_X_pow_self, mul_one]
  · intro l hl hne
    have hlm : l ≤ m := Nat.le_of_lt_succ (mem_range.mp hl)
    have hpow : r ≠ m - l := by
      intro h
      apply hne
      omega
    rw [coeff_C_mul, coeff_X_pow, if_neg hpow, mul_zero]
  · intro hnot
    exact (hnot (mem_range.mpr (by omega))).elim

/-- The concrete quotient is its constant coefficient plus its `m` positive
coefficients.  This is the split expected by the rational-kernel consumer. -/
theorem sourceClearedQuotientPoly_split (m : ℕ) :
    sourceClearedQuotientPoly m =
      C (sourceClearedQuotientCoeff m m) +
        ∑ j : Fin m, C (sourceQuotientPositiveCoeff m j) * X ^ (j.val + 1) := by
  have hdeg : (sourceClearedQuotientPoly m).natDegree < m + 1 := by
    apply Nat.lt_succ_of_le
    unfold sourceClearedQuotientPoly
    refine natDegree_sum_le_of_forall_le (range (m + 1))
      (fun l => C (sourceClearedQuotientCoeff m l) * X ^ (m - l)) ?_
    intro l hl
    exact (natDegree_C_mul_le _ _).trans
      ((natDegree_X_pow_le (m - l)).trans (Nat.sub_le m l))
  calc
    sourceClearedQuotientPoly m =
        ∑ r ∈ range (m + 1),
          C ((sourceClearedQuotientPoly m).coeff r) * X ^ r :=
      (sourceClearedQuotientPoly m).as_sum_range_C_mul_X_pow' hdeg
    _ = C ((sourceClearedQuotientPoly m).coeff 0) +
        ∑ r ∈ range m,
          C ((sourceClearedQuotientPoly m).coeff (r + 1)) * X ^ (r + 1) := by
      rw [sum_range_succ', pow_zero, mul_one]
      exact add_comm _ _
    _ = _ := by
      rw [coeff_sourceClearedQuotientPoly m 0 (Nat.zero_le m)]
      simp only [Nat.sub_zero]
      rw [← Fin.sum_univ_eq_sum_range]
      apply congrArg (C (sourceClearedQuotientCoeff m m) + ·)
      apply Finset.sum_congr rfl
      intro j _
      rw [coeff_sourceClearedQuotientPoly m (j.val + 1) (by omega)]
      rfl

/-- The finite polynomial produced by the source partial fractions after the
kernel-zero correction: short residue prefixes minus the quotient evaluated
at the shifted power `p^(m+1)`. -/
def sourceFiniteCorrectionPoly (m : ℕ) : ParameterPolynomial :=
  (∑ k : Fin (m + 1),
      ∑ n : Fin k.val, sourceResidueQuotientPoly m k.val n.val) -
    ∑ j : Fin m,
      sourceShiftedQuotientCorrectionPoly m j

/-- Evaluation exposes exactly the short-prefix correction occurring on the
right side of `kernelZero_correction_identity`. -/
theorem parameterEval_sourceFiniteCorrectionPoly (m : ℕ) (p : ℝ) :
    parameterEval p (sourceFiniteCorrectionPoly m) =
      (∑ k : Fin (m + 1),
        ∑ n : Fin k.val, parameterEval p (sourceResidueQuotientPoly m k.val n.val)) -
      ∑ j : Fin m,
        parameterEval p (sourceShiftedQuotientCorrectionPoly m j) := by
  simp only [sourceFiniteCorrectionPoly, map_sub, map_sum]

/-- Cleared evaluation form of the source correction.  This is the exact
normalization needed to compare with `kernelZero_correction_identity`. -/
theorem parameterEval_sourceFiniteCorrectionPoly_cleared (m : ℕ) (p : ℝ) :
    p ^ sourceQuotientClearD m *
        parameterEval p (sourceFiniteCorrectionPoly m) =
      p ^ sourceQuotientClearD m *
          (∑ k : Fin (m + 1),
            ∑ n : Fin k.val,
              parameterEval p (sourceResidueQuotientPoly m k.val n.val)) -
        ∑ j : Fin m,
          p ^ ((m + 1) * (j.val + 1)) *
            parameterEval p (sourceQuotientQuotientPoly m j) := by
  rw [parameterEval_sourceFiniteCorrectionPoly, mul_sub]
  congr 1
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j _
  have h := congrArg (parameterEval p)
    (sourceShiftedQuotientCorrection_scale m j)
  have hX : parameterEval p X = p := by simp [parameterEval]
  simpa only [map_mul, map_pow, hX] using h

#print axioms sourceQuotientPositiveCoeff_factor
#print axioms sourceShiftedQuotientCorrection_scale
#print axioms sourceClearedQuotientPoly_split
#print axioms parameterEval_sourceFiniteCorrectionPoly
#print axioms parameterEval_sourceFiniteCorrectionPoly_cleared

end
end ErdosProblems.Erdos1049.PaperR20
