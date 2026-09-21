/- Copyright (c) 2026 Will Cook. Released under Apache 2.0. -/
import ErdosProblems.Synthesis.FeedbackContinuation
open Filter Topology Finset
namespace ErdosProblems.ExternalVerification
theorem feedbackPolicy_preserves_sum
    {A M d : ℕ → ℕ} {w lo hi : ℕ → ℝ} {y : ℝ}
    (hw : ∀ n, 0 ≤ w n) (hlo : ∀ n, 0 ≤ lo n)
    (hvanish : Tendsto hi atTop (𝓝 0))
    (hstep : ∀ n, d n ≤ A n ∧
      (M n : ℤ) ∣ ((∑ i ∈ range n, d i : ℕ) : ℤ) + (d n : ℤ) ∧
      lo (n + 1) ≤ (y - ∑ i ∈ range n, (d i : ℝ) * w i) - (d n : ℝ) * w n ∧
      (y - ∑ i ∈ range n, (d i : ℝ) * w i) - (d n : ℝ) * w n ≤ hi (n + 1)) :
    (∀ n, d n ≤ A n) ∧
      (∀ n, (M n : ℤ) ∣ ((∑ i ∈ range (n + 1), d i : ℕ) : ℤ)) ∧
      HasSum (fun n => (d n : ℝ) * w n) y := by
  exact ErdosProblems.Synthesis.FeedbackContinuation.admissible_digits_hasSum
    hw hlo hvanish hstep
#print axioms feedbackPolicy_preserves_sum
end ErdosProblems.ExternalVerification
