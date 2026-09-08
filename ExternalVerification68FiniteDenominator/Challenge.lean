import Mathlib

namespace Erdos249257.ExternalVerification68FiniteDenominator

noncomputable def factorialGapSeries : ℝ :=
  ∑' n : ℕ, if 1 < n then (1 : ℝ) / (((n.factorial : ℤ) - 1 : ℤ) : ℝ) else 0

theorem finite_denominator_exclusion (a : ℤ) (q : ℕ) (hq : 0 < q)
    (hS : factorialGapSeries = (a : ℝ) / q) :
    (2 : ℕ) ^ 39990 ≤ q ∧ (10 : ℕ) ^ 12040 < q := by
  sorry

end Erdos249257.ExternalVerification68FiniteDenominator
