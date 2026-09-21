import ErdosProblems.Erdos243.PaperCompleteR20.CubicRateNormalisation

/-!
# Erdős 243: quotient increments at the cubic rate
-/

noncomputable section

namespace ErdosProblems.Erdos243.PaperCompleteR20

open Filter

def cubicQuotient (C : ℕ → ℝ) (n : ℕ) : ℝ := C n / risingCubic n

theorem cubicQuotient_increment_eq
    (C : ℕ → ℝ) (n : ℕ) (hn : 0 < n) (hC : C n ≠ 0) :
    cubicQuotient C (n + 1) - cubicQuotient C n =
      cubicQuotient C n * cubicRatioError C n /
        (1 + 3 / (n : ℝ)) := by
  have hmodel := risingCubic_ratio n hn
  simp only [cubicQuotient, cubicRatioError]
  rw [hmodel]
  field_simp [risingCubic, hn.ne', hC]

theorem cubic_model_ratio_tendsto_one :
    Tendsto (fun n : ℕ => 1 + 3 / (n : ℝ)) atTop (nhds 1) := by
  have hinv : Tendsto (fun n : ℕ => ((n : ℝ))⁻¹) atTop (nhds 0) :=
    tendsto_inv_atTop_zero.comp tendsto_natCast_atTop_atTop
  simpa [div_eq_mul_inv] using tendsto_const_nhds.add (tendsto_const_nhds.mul hinv)

/-- Once the normalised quotient is bounded, the literal cubic little-o ratio
error gives an `o(n^-3)` quotient increment. -/
theorem cubicQuotient_increment_scaled_tendsto_zero
    (C : ℕ → ℝ)
    (hC : ∀ᶠ n in atTop, C n ≠ 0)
    (hbounded : ∃ M : ℝ, ∀ᶠ n in atTop, |cubicQuotient C n| ≤ M)
    (hratio : Tendsto
      (fun n : ℕ => (n : ℝ) ^ 3 * cubicRatioError C n) atTop (nhds 0)) :
    Tendsto (fun n : ℕ => (n : ℝ) ^ 3 *
      (cubicQuotient C (n + 1) - cubicQuotient C n)) atTop (nhds 0) := by
  obtain ⟨M, hM⟩ := hbounded
  have hqmul : Tendsto
      (fun n : ℕ => cubicQuotient C n * ((n : ℝ) ^ 3 * cubicRatioError C n))
      atTop (nhds 0) := by
    apply isBoundedUnder_le_mul_tendsto_zero
    exact ⟨M, by simpa [Function.comp_def, Real.norm_eq_abs] using hM⟩
    exact hratio
  have hmodelInv : Tendsto (fun n : ℕ => (1 + 3 / (n : ℝ))⁻¹)
      atTop (nhds 1) := by
    simpa using cubic_model_ratio_tendsto_one.inv₀ (by norm_num)
  have hprod := hqmul.mul hmodelInv
  simp only [zero_mul] at hprod
  apply hprod.congr'
  filter_upwards [hC, eventually_gt_atTop (0 : ℕ)] with n hCn hn
  rw [cubicQuotient_increment_eq C n hn hCn]
  field_simp [show (1 + 3 / (n : ℝ)) ≠ 0 by positivity]

#print axioms ErdosProblems.Erdos243.PaperCompleteR20.cubicQuotient_increment_scaled_tendsto_zero

end ErdosProblems.Erdos243.PaperCompleteR20
