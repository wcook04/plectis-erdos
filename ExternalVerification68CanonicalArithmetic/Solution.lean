/-
Copyright (c) 2026 Will Cook. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Will Cook
-/
import ErdosProblems.Erdos68.CanonicalFactorialTermination
import ErdosProblems.Erdos68.PrimePoleDenominator

namespace Erdos249257.ExternalVerification68CanonicalArithmetic

/-- Rationality is exactly eventual termination of the canonical factorial
expansion, expressed directly through the factorial-scale floors. -/
theorem rational_iff_factorial_floor_tail
    (x : ℝ) :
    (∃ q : ℚ, (q : ℝ) = x) ↔
      ∃ N : ℕ, ∀ n ≥ N,
        ⌊((n + 1).factorial : ℝ) * x⌋ =
          ((n + 1 : ℕ) : ℤ) * ⌊(n.factorial : ℝ) * x⌋ := by
  simpa only [ErdosProblems.Erdos68.canonicalDigit,
    ErdosProblems.Erdos68.facFloor, Nat.add_sub_cancel, sub_eq_zero] using
    ErdosProblems.Erdos68.exists_rat_eq_iff_eventually_zero_canonicalDigit x

/-- Reduction retains a prime divisor's full common-denominator exponent
exactly when that prime does not divide the numerator. -/
theorem rational_denominator_full_prime_exponent
    {p B L : ℕ} (hp : p.Prime) (hL : 0 < L) (hpL : p ∣ L) :
    ((B : ℚ) / L).den.factorization p = L.factorization p ↔ ¬p ∣ B := by
  exact ErdosProblems.Erdos68.natRatio_den_factorization_eq_iff hp hL hpL

end Erdos249257.ExternalVerification68CanonicalArithmetic
