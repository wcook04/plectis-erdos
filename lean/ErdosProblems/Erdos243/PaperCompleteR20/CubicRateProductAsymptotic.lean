import ErdosProblems.Erdos243.PaperCompleteR20.CubicRateQuotientBounded
import ErdosProblems.Erdos243.PaperCompleteR20.CubicRateSummableTail

/-!
# Erdős 243: the literal cubic product asymptotic

This module closes the analytic producer.  It starts with the paper's literal
scaled ratio error, proves the quotient bounded through the convergent product,
then sums the resulting quotient increments to the `o(n⁻²)` tail estimate.
-/

noncomputable section

namespace ErdosProblems.Erdos243.PaperCompleteR20

open Filter

theorem normalisedCubicError_of_literal_ratio_error
    (C : ℕ → ℝ)
    (hC : ∀ᶠ n in atTop, C n ≠ 0)
    (hratio : Tendsto
      (fun n : ℕ => (n : ℝ) ^ 3 * cubicRatioError C n) atTop (nhds 0)) :
    ∃ K : ℝ, Tendsto (normalisedCubicError C K) atTop (nhds 0) := by
  have hbounded := cubicQuotient_eventually_bounded_of_ratio_error C hC hratio
  have hincr := cubicQuotient_increment_scaled_tendsto_zero C hC hbounded hratio
  exact normalisedCubicError_tendsto_zero_of_quotient_increment C hincr

theorem cubic_size_and_residual_of_literal_ratio_error
    (C : ℕ → ℝ)
    (hC : ∀ᶠ n in atTop, C n ≠ 0)
    (hratio : Tendsto
      (fun n : ℕ => (n : ℝ) ^ 3 * cubicRatioError C n) atTop (nhds 0)) :
    ∃ K : ℝ, ∃ r : ℕ → ℝ,
      C = (fun n : ℕ => K * risingCubic n + r n) ∧
      Tendsto (fun n : ℕ => C n / (n : ℝ) ^ 3) atTop (nhds K) ∧
      Tendsto (fun n : ℕ => r n / (n : ℝ)) atTop (nhds 0) := by
  obtain ⟨K, hK⟩ := normalisedCubicError_of_literal_ratio_error C hC hratio
  let r : ℕ → ℝ := fun n : ℕ => C n - K * risingCubic n
  have hdecomp : C = fun n : ℕ => K * risingCubic n + r n := by
    funext n
    simp [r]
  exact ⟨K, r, hdecomp,
    cubic_size_tendsto_of_normalisedCubicError C K hK,
    cubic_residual_sublinear_of_normalisedCubicError C r K hdecomp hK⟩

#print axioms ErdosProblems.Erdos243.PaperCompleteR20.normalisedCubicError_of_literal_ratio_error
#print axioms ErdosProblems.Erdos243.PaperCompleteR20.cubic_size_and_residual_of_literal_ratio_error

end ErdosProblems.Erdos243.PaperCompleteR20
