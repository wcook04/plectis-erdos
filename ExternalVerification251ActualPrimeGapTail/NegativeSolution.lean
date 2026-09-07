/- Deliberate mismatch: replaces the source's open-unit-interval obstruction
with a different closed-unit-interval statement and omits the other endpoints. -/
import Mathlib

namespace Erdos249257.ExternalVerification251ActualPrimeGapTail

noncomputable def prime0 (n : ℕ) : ℕ := Nat.nth Nat.Prime n
noncomputable def primeGap0 (n : ℕ) : ℕ := prime0 (n + 1) - prime0 n
noncomputable def primeGapPartialSumQ (n : ℕ) : ℚ :=
  ∑ i ∈ Finset.range n, (primeGap0 i : ℚ) / 2 ^ (i + 1)
noncomputable def rationalPrimeGapTailState (S : ℚ) (N : ℕ) : ℚ :=
  2 ^ (N + 1) * (S - primeGapPartialSumQ (N + 1))
def tailShift (T : ℕ → ℚ) (h N : ℕ) : ℚ := T (N + h) - T N

theorem rationalPrimeGapTail_has_positive_shift_not_eventually_small
    (S : ℚ) :
    ∃ h, 0 < h ∧
      ¬ ∃ N₀, ∀ N, N₀ ≤ N →
        -1 ≤ tailShift (rationalPrimeGapTailState S) h N ∧
          tailShift (rationalPrimeGapTailState S) h N ≤ 1 := by
  sorry

end Erdos249257.ExternalVerification251ActualPrimeGapTail
