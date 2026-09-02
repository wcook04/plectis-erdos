/-
Copyright (c) 2026 Will Cook. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Will Cook
-/
import Mathlib

/-!
# Trusted challenge for the Erdős #251 polynomial-shift countermodel

This source-independent statement exposes the complete exact infinite
countermodel to coarse prime-gap arguments.  Its quadratic digit word is
positive, even, and strictly increasing; it satisfies the exact dyadic tail
recurrence; every fixed tail shift is integral; and its adjacent differences
are never `±2`.

Thus the compared declaration itself—not merely its surrounding prose—records
that positivity, parity, polynomial growth, unboundedness, nonperiodicity, and
the recurrence cannot force the adjacent-small-mismatch mechanism.  The word
is not the actual prime-gap word, so the theorem does not decide Erdős #251.
-/

namespace Erdos249257.ExternalVerification251PolynomialShiftCountermodel

/-- Abstract dyadic tail recurrence with integer digits. -/
def DyadicTailRecurrence (g : ℕ → ℤ) (T : ℕ → ℚ) : Prop :=
  ∀ N, T (N + 1) = 2 * T N - g (N + 1)

/-- Difference between tail states separated by `h` steps. -/
def tailShift (T : ℕ → ℚ) (h N : ℕ) : ℚ :=
  T (N + h) - T N

/-- A rational number is integral when it is the cast of an integer. -/
def RatIntegral (x : ℚ) : Prop :=
  ∃ z : ℤ, x = z

/-- The rational polynomial tail orbit in the exact #251 countermodel. -/
def polynomialTailOrbit (n : ℕ) : ℚ :=
  (2 * (n + 4) ^ 2 : ℕ)

/-- The positive-even quadratic word paired with `polynomialTailOrbit`. -/
def polynomialGapWord (n : ℕ) : ℤ :=
  (2 * (n ^ 2 + 4 * n + 2) : ℕ)

/-- A positive, even, strictly growing polynomial digit word can satisfy the
dyadic recurrence while every fixed tail shift remains integral and every
adjacent digit difference avoids `±2`. -/
theorem polynomialGapTailCountermodel :
    DyadicTailRecurrence polynomialGapWord polynomialTailOrbit ∧
      (∀ n, 0 < polynomialGapWord n) ∧
      (∀ n, ∃ k : ℤ, polynomialGapWord n = 2 * k) ∧
      StrictMono polynomialGapWord ∧
      (∀ h N, RatIntegral (tailShift polynomialTailOrbit h N)) ∧
      (∀ N,
        polynomialGapWord (N + 2) - polynomialGapWord (N + 1) ≠ 2 ∧
        polynomialGapWord (N + 2) - polynomialGapWord (N + 1) ≠ -2) := by
  sorry

end Erdos249257.ExternalVerification251PolynomialShiftCountermodel
