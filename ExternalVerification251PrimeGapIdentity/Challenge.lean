/-
Copyright (c) 2026 Will Cook. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Will Cook
-/
import Mathlib

/-!
# Trusted challenge for the Erdős #251 prime-gap identity

This Mathlib-only statement exposes an explicit elementary polynomial upper
bound for the `n`th prime, unconditional convergence of the prime and
consecutive-prime-gap dyadic series, the exact infinite summation-by-parts
identity in the normalized indexing `2^(n+1)` and in the displayed indexing
`2^n`, and the irrationality equivalences those identities force.

Every theorem here is unconditional.  None of them asserts irrationality of
any of the three series, so the package does not solve Erdős Problem 251.
-/

namespace Erdos249257.ExternalVerification251PrimeGapIdentity

/-- Zero-based prime enumeration. -/
noncomputable def prime0 (n : ℕ) : ℕ := Nat.nth Nat.Prime n

/-- Zero-based consecutive prime gap. -/
noncomputable def primeGap0 (n : ℕ) : ℕ := prime0 (n + 1) - prime0 n

/-- The term of the normalized prime series, with denominator `2^(n+1)`. -/
noncomputable def primeDyadicTerm (n : ℕ) : ℝ :=
  (prime0 n : ℝ) / 2 ^ (n + 1)

/-- The term of the displayed prime series, with denominator `2^n`. -/
noncomputable def primeDisplayedDyadicTerm (n : ℕ) : ℝ :=
  (prime0 n : ℝ) / 2 ^ n

/-- The term of the corresponding consecutive-prime-gap series. -/
noncomputable def primeGapDyadicTerm (n : ℕ) : ℝ :=
  (primeGap0 n : ℝ) / 2 ^ (n + 1)

/-- An explicit elementary polynomial upper bound for the zero-based `n`th
prime. -/
theorem prime0_le_polynomial (n : ℕ) :
    prime0 n ≤ 1250 * (n + 1) ^ 4 := by
  sorry

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

/-- The displayed indexing satisfies the exact unconditional identity
`∑ p n / 2 ^ n = 4 + 2 * ∑ g n / 2 ^ (n + 1)`. -/
theorem primeDisplayedSeries_eq_four_add_two_primeGapSeries :
    (∑' n : ℕ, primeDisplayedDyadicTerm n) =
      4 + 2 * ∑' n : ℕ, primeGapDyadicTerm n := by
  sorry

/-- The displayed prime series and the prime-gap series have exactly the same
irrationality status. -/
theorem primeDisplayedSeries_irrational_iff_primeGapSeries :
    Irrational (∑' n : ℕ, primeDisplayedDyadicTerm n) ↔
      Irrational (∑' n : ℕ, primeGapDyadicTerm n) := by
  sorry

end Erdos249257.ExternalVerification251PrimeGapIdentity
