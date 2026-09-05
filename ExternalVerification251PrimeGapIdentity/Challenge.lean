/-
Copyright (c) 2026 Will Cook. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Will Cook
-/
import Mathlib

/-!
# Trusted challenge for the Erdős #251 prime-gap identity

The package exposes unconditional convergence, the exact infinite
prime/prime-gap identity, and the resulting irrationality equivalence. It does
not assert irrationality of either series.
-/

namespace Erdos249257.ExternalVerification251PrimeGapIdentity

noncomputable def prime0 (n : ℕ) : ℕ := Nat.nth Nat.Prime n

noncomputable def primeGap0 (n : ℕ) : ℕ := prime0 (n + 1) - prime0 n

noncomputable def primeDyadicTerm (n : ℕ) : ℝ :=
  (prime0 n : ℝ) / 2 ^ (n + 1)

noncomputable def primeGapDyadicTerm (n : ℕ) : ℝ :=
  (primeGap0 n : ℝ) / 2 ^ (n + 1)

/-- The normalized zero-based prime series converges unconditionally. -/
theorem primeSeries_summable : Summable primeDyadicTerm := by
  sorry

/-- The consecutive-prime-gap series converges unconditionally. -/
theorem primeGapSeries_summable : Summable primeGapDyadicTerm := by
  sorry

/-- Exact unconditional infinite summation-by-parts identity. -/
theorem primeSeries_eq_two_add_primeGapSeries :
    (∑' n : ℕ, primeDyadicTerm n) =
      2 + ∑' n : ℕ, primeGapDyadicTerm n := by
  sorry

/-- Adding the integer `2` shows that the prime and prime-gap series have
exactly the same irrationality status. -/
theorem primeSeries_irrational_iff_primeGapSeries :
    Irrational (∑' n : ℕ, primeDyadicTerm n) ↔
      Irrational (∑' n : ℕ, primeGapDyadicTerm n) := by
  sorry

end Erdos249257.ExternalVerification251PrimeGapIdentity
