import Mathlib

namespace Erdos249257.ExternalVerification1041CyclicTrinomialFiber

/-- Eliminating the middle coefficient at a quotient root gives the exact
two-term radial-spoke factorization. -/
theorem trinomialRoot_spoke_factorization
    {m r : ℕ} {a c w : ℂ} {u : ℝ}
    (hroot : w ^ m + a * w ^ r + c = 0) :
    (u : ℂ) ^ m * w ^ m + a * (u : ℂ) ^ r * w ^ r + c =
      ((1 - u ^ r : ℝ) : ℂ) * c -
        ((u ^ r - u ^ m : ℝ) : ℂ) * w ^ m := by
  sorry

/-- Every quotient-root spoke is strictly inside the unit lemniscate when
the quotient root and constant term both lie in the open unit disk. -/
theorem trinomialRoot_spoke_norm_lt_one_of_norm_lt_one
    {m r : ℕ} (hr : 1 ≤ r) (hrm : r ≤ m) {a c w : ℂ}
    (hroot : w ^ m + a * w ^ r + c = 0)
    (hw : ‖w‖ < 1) (hc : ‖c‖ < 1) {u : ℝ}
    (hu0 : 0 ≤ u) (hu1 : u ≤ 1) :
    ‖(u : ℂ) ^ m * w ^ m + a * (u : ℂ) ^ r * w ^ r + c‖ < 1 := by
  sorry

/-- Two selected fibre displacements of radius below one have total broken-line
length strictly below two. -/
theorem cyclicTrinomial_two_short_fiber_displacements {y₁ y₂ : ℂ}
    (hy₁ : ‖y₁‖ < 1) (hy₂ : ‖y₂‖ < 1) :
    ‖y₁‖ + ‖y₂‖ < 2 := by
  sorry

end Erdos249257.ExternalVerification1041CyclicTrinomialFiber
