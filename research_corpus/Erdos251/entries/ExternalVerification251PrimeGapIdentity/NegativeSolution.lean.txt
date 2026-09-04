/- Deliberate mismatch: the gap sum is incorrectly shifted by `1`. -/
import Mathlib

namespace Erdos249257.ExternalVerification251PrimeGapIdentity

noncomputable def prime0 (n : ℕ) : ℕ := Nat.nth Nat.Prime n
noncomputable def primeGap0 (n : ℕ) : ℕ := prime0 (n + 1) - prime0 n
noncomputable def primeDyadicTerm (n : ℕ) : ℝ := (prime0 n : ℝ) / 2 ^ (n + 1)
noncomputable def primeGapDyadicTerm (n : ℕ) : ℝ := (primeGap0 n : ℝ) / 2 ^ (n + 1)

theorem primeSeries_eq_two_add_primeGapSeries :
    (∑' n : ℕ, primeDyadicTerm n) =
      1 + ∑' n : ℕ, primeGapDyadicTerm n := by
  sorry

end Erdos249257.ExternalVerification251PrimeGapIdentity
