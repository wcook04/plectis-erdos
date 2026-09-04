/-
Copyright (c) 2026 Will Cook. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Will Cook
-/
import Mathlib

/-!
# Trusted challenge for the actual Erdős #251 prime-gap tail bridge

This package exposes the exact passage from a hypothetical rational value of
the actual prime-gap series to its rational tail orbit, denominator collapse,
and the fixed-shift smallness obstruction forced by prime-gap nonperiodicity.
-/

open scoped BigOperators

namespace Erdos249257.ExternalVerification251ActualPrimeGapTail

noncomputable def prime0 (n : ℕ) : ℕ := Nat.nth Nat.Prime n

noncomputable def primeGap0 (n : ℕ) : ℕ := prime0 (n + 1) - prime0 n

noncomputable def primeGapDyadicTerm (n : ℕ) : ℝ :=
  (primeGap0 n : ℝ) / 2 ^ (n + 1)

noncomputable def primeGapPartialSumQ (n : ℕ) : ℚ :=
  ∑ i ∈ Finset.range n, (primeGap0 i : ℚ) / 2 ^ (i + 1)

def DyadicTailRecurrence (g : ℕ → ℤ) (T : ℕ → ℚ) : Prop :=
  ∀ N, T (N + 1) = 2 * T N - g (N + 1)

noncomputable def rationalPrimeGapTailState (S : ℚ) (N : ℕ) : ℚ :=
  2 ^ (N + 1) * (S - primeGapPartialSumQ (N + 1))

def tailShift (T : ℕ → ℚ) (h N : ℕ) : ℚ :=
  T (N + h) - T N

def RatIntegral (x : ℚ) : Prop :=
  ∃ z : ℤ, x = z

/-- Hypothetical non-irrationality produces one rational candidate whose
algebraic states are every scaled real tail of the actual gap series. -/
theorem exists_rationalPrimeGapTailState_representation_of_not_irrational
    (h : ¬ Irrational (∑' n : ℕ, primeGapDyadicTerm n)) :
    ∃ S : ℚ,
      (S : ℝ) = ∑' n : ℕ, primeGapDyadicTerm n ∧
      ∀ N,
        ((rationalPrimeGapTailState S N : ℚ) : ℝ) =
          2 ^ (N + 1) *
            ∑' k : ℕ, primeGapDyadicTerm (k + (N + 1)) := by
  sorry

/-- The proposed rational state satisfies the actual prime-gap recurrence
identically, before any rationality hypothesis is imposed. -/
theorem rationalPrimeGapTailState_recurrence (S : ℚ) :
    DyadicTailRecurrence (fun n => (primeGap0 n : ℤ))
      (rationalPrimeGapTailState S) := by
  sorry

/-- Complete denominator decomposition gives one positive fixed shift which
is integral at every sufficiently late actual-gap tail state. -/
theorem rationalPrimeGapTailShift_eventuallyIntegral
    (S : ℚ) :
    ∃ h, 0 < h ∧
      ∃ N₀, ∀ N, N₀ ≤ N →
        RatIntegral
          (tailShift (rationalPrimeGapTailState S) h N) := by
  sorry

/-- Actual prime-gap nonperiodicity forces the denominator-selected integral
shift to escape the open unit interval infinitely often. -/
theorem rationalPrimeGapTail_has_positive_shift_not_eventually_small
    (S : ℚ) :
    ∃ h, 0 < h ∧
      ¬ ∃ N₀, ∀ N, N₀ ≤ N →
        -1 < tailShift (rationalPrimeGapTailState S) h N ∧
          tailShift (rationalPrimeGapTailState S) h N < 1 := by
  sorry

end Erdos249257.ExternalVerification251ActualPrimeGapTail
