/-
Copyright (c) 2026 Will Cook. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Will Cook
-/
import Mathlib

/-! Independent external-replay challenge; proof holes occur only in this template. -/

namespace Erdos249257.ExternalVerification68CanonicalArithmetic

/-- Rationality is exactly eventual termination of the canonical factorial
expansion, expressed directly through the factorial-scale floors. -/
theorem rational_iff_factorial_floor_tail
    (x : ℝ) :
    (∃ q : ℚ, (q : ℝ) = x) ↔
      ∃ N : ℕ, ∀ n ≥ N,
        ⌊((n + 1).factorial : ℝ) * x⌋ =
          ((n + 1 : ℕ) : ℤ) * ⌊(n.factorial : ℝ) * x⌋ := by
  sorry

/-- Reduction retains a prime divisor's full common-denominator exponent
exactly when that prime does not divide the numerator. -/
theorem rational_denominator_full_prime_exponent
    {p B L : ℕ} (hp : p.Prime) (hL : 0 < L) (hpL : p ∣ L) :
    ((B : ℚ) / L).den.factorization p = L.factorization p ↔ ¬p ∣ B := by
  sorry

end Erdos249257.ExternalVerification68CanonicalArithmetic
