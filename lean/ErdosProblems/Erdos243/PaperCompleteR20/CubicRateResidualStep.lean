import ErdosProblems.Erdos243.PaperCompleteR20.CubicRateDifferenceLimits

/-!
# Erdős 243: the cubic-rate residual recurrence

This is the exact algebraic step between the ratio comparison and the finite
difference argument.  The additive recurrence defect and the sublinear
residual together force the first residual difference to tend to zero.
-/

noncomputable section

namespace ErdosProblems.Erdos243.PaperCompleteR20

open Filter

/-- The additive defect from the cubic model ratio `1 + 3/n`. -/
def cubicAdditiveDefect (C : ℕ → ℝ) (n : ℕ) : ℝ :=
  C (n + 1) - (1 + 3 / (n : ℝ)) * C n

theorem risingCubic_ratio (n : ℕ) (hn : 0 < n) :
    risingCubic (n + 1) = (1 + 3 / (n : ℝ)) * risingCubic n := by
  simp only [risingCubic]
  push_cast
  field_simp [hn.ne']
  ring

/-- If `C = K n(n+1)(n+2) + r`, the residual difference is the additive
ratio defect plus `3r/n`. -/
theorem realForwardDiff_residual_eq
    (C r : ℕ → ℝ) (K : ℝ)
    (hdecomp : C = fun n => K * risingCubic n + r n)
    (n : ℕ) (hn : 0 < n) :
    realForwardDiff r n = cubicAdditiveDefect C n + 3 * (r n / (n : ℝ)) := by
  have hmodel := risingCubic_ratio n hn
  simp only [realForwardDiff, cubicAdditiveDefect, hdecomp]
  rw [hmodel]
  field_simp [hn.ne']
  ring

/-- The precise residual-limit lemma used by the cubic-rate extraction. -/
theorem realForwardDiff_residual_tendsto_zero
    (C r : ℕ → ℝ) (K : ℝ)
    (hdecomp : C = fun n => K * risingCubic n + r n)
    (hdefect : Tendsto (cubicAdditiveDefect C) atTop (nhds 0))
    (hsublinear : Tendsto (fun n => r n / (n : ℝ)) atTop (nhds 0)) :
    Tendsto (realForwardDiff r) atTop (nhds 0) := by
  have hsum : Tendsto
      (fun n => cubicAdditiveDefect C n + 3 * (r n / (n : ℝ)))
      atTop (nhds 0) := by
    simpa using hdefect.add (tendsto_const_nhds.mul hsublinear)
  apply hsum.congr'
  filter_upwards [eventually_gt_atTop (0 : ℕ)] with n hn
  exact (realForwardDiff_residual_eq C r K hdecomp n hn).symm

/-- Complete composition from the two analytic estimates to eventual
constancy of the third integer difference. -/
theorem cubic_rate_estimates_give_eventually_constant_third_difference
    (C : ℕ → ℤ) (K : ℝ) (r : ℕ → ℝ)
    (hdecomp : (fun n => (C n : ℝ)) = fun n => K * risingCubic n + r n)
    (hdefect : Tendsto (cubicAdditiveDefect (fun n => (C n : ℝ))) atTop (nhds 0))
    (hsublinear : Tendsto (fun n => r n / (n : ℝ)) atTop (nhds 0)) :
    ∃ N : ℕ, ∀ n, N ≤ n →
      iterIntForwardDiff 3 C n = iterIntForwardDiff 3 C N := by
  apply cubic_residual_gives_eventually_constant_third_difference C K r hdecomp
  exact realForwardDiff_residual_tendsto_zero (fun n => (C n : ℝ)) r K
    hdecomp hdefect hsublinear

#print axioms ErdosProblems.Erdos243.PaperCompleteR20.realForwardDiff_residual_tendsto_zero
#print axioms ErdosProblems.Erdos243.PaperCompleteR20.cubic_rate_estimates_give_eventually_constant_third_difference

end ErdosProblems.Erdos243.PaperCompleteR20
