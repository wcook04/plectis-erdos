import ErdosProblems.Erdos243.PaperCompleteR20.CubicRateResidualStep

/-!
# Erdős 243: from ratio little-o to additive cubic defect

The paper states the rate multiplicatively.  This file records the exact
rescaling that converts its `o(n^-3)` error into an additive error tending to
zero once the numerator has cubic size.
-/

noncomputable section

namespace ErdosProblems.Erdos243.PaperCompleteR20

open Filter

def cubicRatioError (C : ℕ → ℝ) (n : ℕ) : ℝ :=
  C (n + 1) / C n - (1 + 3 / (n : ℝ))

theorem cubicAdditiveDefect_eq_mul_ratioError
    (C : ℕ → ℝ) (n : ℕ) (hC : C n ≠ 0) :
    cubicAdditiveDefect C n = C n * cubicRatioError C n := by
  simp only [cubicAdditiveDefect, cubicRatioError]
  field_simp [hC]

theorem cubicAdditiveDefect_eq_scaled_ratioError
    (C : ℕ → ℝ) (n : ℕ) (hn : 0 < n) (hC : C n ≠ 0) :
    cubicAdditiveDefect C n =
      (C n / (n : ℝ) ^ 3) * ((n : ℝ) ^ 3 * cubicRatioError C n) := by
  rw [cubicAdditiveDefect_eq_mul_ratioError C n hC]
  field_simp [hn.ne']

/-- Literal `o(n^-3)` ratio control, written without asymptotic notation,
times cubic-size control gives an additive recurrence defect tending to zero. -/
theorem cubicAdditiveDefect_tendsto_zero_of_ratioError
    (C : ℕ → ℝ) (K : ℝ)
    (hC : ∀ᶠ n in atTop, C n ≠ 0)
    (hcubic : Tendsto (fun n => C n / (n : ℝ) ^ 3) atTop (nhds K))
    (hratio : Tendsto
      (fun n : ℕ => (n : ℝ) ^ 3 * cubicRatioError C n) atTop (nhds 0)) :
    Tendsto (cubicAdditiveDefect C) atTop (nhds 0) := by
  have hprod : Tendsto
      (fun n => (C n / (n : ℝ) ^ 3) *
        ((n : ℝ) ^ 3 * cubicRatioError C n)) atTop (nhds 0) := by
    simpa using hcubic.mul hratio
  apply hprod.congr'
  filter_upwards [hC, eventually_gt_atTop (0 : ℕ)] with n hCn hn
  exact (cubicAdditiveDefect_eq_scaled_ratioError C n hn hCn).symm

/-- Composition through the finite-difference interface. -/
theorem cubic_ratio_and_residual_estimates_give_eventually_constant_third_difference
    (C : ℕ → ℤ) (K : ℝ) (r : ℕ → ℝ)
    (hpos : ∀ n, 0 < C n)
    (hdecomp : (fun n => (C n : ℝ)) = fun n => K * risingCubic n + r n)
    (hcubic : Tendsto (fun n => (C n : ℝ) / (n : ℝ) ^ 3) atTop (nhds K))
    (hratio : Tendsto (fun n : ℕ => (n : ℝ) ^ 3 *
      cubicRatioError (fun j => (C j : ℝ)) n) atTop (nhds 0))
    (hsublinear : Tendsto (fun n => r n / (n : ℝ)) atTop (nhds 0)) :
    ∃ N : ℕ, ∀ n, N ≤ n →
      iterIntForwardDiff 3 C n = iterIntForwardDiff 3 C N := by
  apply cubic_rate_estimates_give_eventually_constant_third_difference C K r hdecomp
  · apply cubicAdditiveDefect_tendsto_zero_of_ratioError (fun n => (C n : ℝ)) K
    · filter_upwards [] with n
      exact_mod_cast (ne_of_gt (hpos n))
    · exact hcubic
    · exact hratio
  · exact hsublinear

#print axioms ErdosProblems.Erdos243.PaperCompleteR20.cubicAdditiveDefect_tendsto_zero_of_ratioError
#print axioms ErdosProblems.Erdos243.PaperCompleteR20.cubic_ratio_and_residual_estimates_give_eventually_constant_third_difference

end ErdosProblems.Erdos243.PaperCompleteR20
