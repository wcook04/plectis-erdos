import ErdosProblems.Erdos243.PaperCompleteR20.CubicRateDefect

/-!
# Erdős 243: normalised cubic comparison

The remaining product-comparison estimate naturally says that the quotient by
the rising cubic converges to its limit with error `o(n^-2)`.  This file proves
that this single estimate supplies both normalisations required downstream.
-/

noncomputable section

namespace ErdosProblems.Erdos243.PaperCompleteR20

open Filter

def normalisedCubicError (C : ℕ → ℝ) (K : ℝ) (n : ℕ) : ℝ :=
  (n : ℝ) ^ 2 * (C n / risingCubic n - K)

theorem risingCubic_div_cube_tendsto_one :
    Tendsto (fun n : ℕ => risingCubic n / (n : ℝ) ^ 3) atTop (nhds 1) := by
  have hinv : Tendsto (fun n : ℕ => ((n : ℝ))⁻¹) atTop (nhds 0) :=
    tendsto_inv_atTop_zero.comp tendsto_natCast_atTop_atTop
  have hprod : Tendsto
      (fun n : ℕ => (1 + ((n : ℝ))⁻¹) * (1 + 2 * ((n : ℝ))⁻¹))
      atTop (nhds 1) := by
    have hone : Tendsto (fun _ : ℕ => (1 : ℝ)) atTop (nhds 1) :=
      tendsto_const_nhds
    have htwo : Tendsto (fun _ : ℕ => (2 : ℝ)) atTop (nhds 2) :=
      tendsto_const_nhds
    simpa using (hone.add hinv).mul (hone.add (htwo.mul hinv))
  apply hprod.congr'
  filter_upwards [eventually_gt_atTop (0 : ℕ)] with n hn
  simp only [risingCubic]
  push_cast
  field_simp [hn.ne']

theorem quotient_error_tendsto_zero_of_normalisedCubicError
    (C : ℕ → ℝ) (K : ℝ)
    (herror : Tendsto (normalisedCubicError C K) atTop (nhds 0)) :
    Tendsto (fun n => C n / risingCubic n - K) atTop (nhds 0) := by
  have hinv : Tendsto (fun n : ℕ => ((n : ℝ) ^ 2)⁻¹) atTop (nhds 0) := by
    have hbase : Tendsto (fun n : ℕ => ((n : ℝ))⁻¹) atTop (nhds 0) :=
      tendsto_inv_atTop_zero.comp tendsto_natCast_atTop_atTop
    simpa [inv_pow] using hbase.pow 2
  have hprod : Tendsto
      (fun n => normalisedCubicError C K n * ((n : ℝ) ^ 2)⁻¹)
      atTop (nhds 0) := by
    simpa using herror.mul hinv
  apply hprod.congr'
  filter_upwards [eventually_gt_atTop (0 : ℕ)] with n hn
  simp only [normalisedCubicError]
  field_simp [hn.ne']

/-- The normalised quotient estimate implies cubic-size convergence. -/
theorem cubic_size_tendsto_of_normalisedCubicError
    (C : ℕ → ℝ) (K : ℝ)
    (herror : Tendsto (normalisedCubicError C K) atTop (nhds 0)) :
    Tendsto (fun n => C n / (n : ℝ) ^ 3) atTop (nhds K) := by
  have hquot : Tendsto (fun n => C n / risingCubic n) atTop (nhds K) := by
    simpa only [sub_add_cancel, zero_add] using
      (quotient_error_tendsto_zero_of_normalisedCubicError C K herror).add_const K
  have hprod : Tendsto
      (fun n => C n / risingCubic n * (risingCubic n / (n : ℝ) ^ 3))
      atTop (nhds K) := by
    simpa using hquot.mul risingCubic_div_cube_tendsto_one
  apply hprod.congr'
  filter_upwards [eventually_gt_atTop (0 : ℕ)] with n hn
  simp only [risingCubic]
  push_cast
  field_simp [hn.ne']

/-- The same estimate makes the residual sublinear. -/
theorem cubic_residual_sublinear_of_normalisedCubicError
    (C r : ℕ → ℝ) (K : ℝ)
    (hdecomp : C = fun n => K * risingCubic n + r n)
    (herror : Tendsto (normalisedCubicError C K) atTop (nhds 0)) :
    Tendsto (fun n => r n / (n : ℝ)) atTop (nhds 0) := by
  have hprod : Tendsto
      (fun n => normalisedCubicError C K n *
        (risingCubic n / (n : ℝ) ^ 3)) atTop (nhds 0) := by
    simpa using herror.mul risingCubic_div_cube_tendsto_one
  apply hprod.congr'
  filter_upwards [eventually_gt_atTop (0 : ℕ)] with n hn
  simp only [normalisedCubicError, hdecomp]
  field_simp [risingCubic, hn.ne']
  ring

#print axioms ErdosProblems.Erdos243.PaperCompleteR20.cubic_size_tendsto_of_normalisedCubicError
#print axioms ErdosProblems.Erdos243.PaperCompleteR20.cubic_residual_sublinear_of_normalisedCubicError

end ErdosProblems.Erdos243.PaperCompleteR20
