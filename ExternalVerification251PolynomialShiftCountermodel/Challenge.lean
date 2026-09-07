/-
Copyright (c) 2026 Will Cook. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Will Cook
-/
import Mathlib

/-!
# Trusted challenge for the Erdős #251 polynomial-shift countermodel

This source-independent statement exposes the complete exact infinite
countermodel to coarse prime-gap arguments, in its final analytic form.  The
dyadic series of the quadratic digit word sums to the rational number `32`, so
that sum is not irrational.  The same declaration records the properties of the
word that hold alongside that value: it is positive, even, and strictly
increasing; it satisfies the exact dyadic tail recurrence; every fixed tail
shift is integral; and every adjacent difference equals `4n + 10`, hence is
never `±2` at any index.

Thus the compared declaration itself records that positivity, parity,
polynomial growth, unboundedness, nonperiodicity, the recurrence, and
integrality at every fixed shift are jointly compatible with a rational sum, so
no argument that uses only those properties can force irrationality.  The word
is a model sequence and is not the actual prime-gap word, so the theorem is
internal infrastructure and decides nothing about Erdős #251.

A telescoping countermodel of the same species, for the neighbouring conjecture
printed under #251, was published first by Vjeko Kovač, `On the Erdős problem
#251`, https://web.math.pmf.unizg.hr/~vjekovac/files/Erdos_problem_251.pdf,
15 April 2026.
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

/-- The real dyadic term of the countermodel series, indexed so that `n = 0`
carries the digit `g 1 / 2`.  The zero-index digit is the initial carry and is
not part of the series. -/
noncomputable def polynomialGapDyadicTerm (n : ℕ) : ℝ :=
  (polynomialGapWord (n + 1) : ℝ) / 2 ^ (n + 1)

/-- A positive, even, strictly growing polynomial digit word satisfies the
dyadic recurrence while every fixed tail shift remains integral and every
adjacent digit difference equals `4n + 10`, and its dyadic series sums to the
rational number `32`. -/
theorem polynomialGapTailCountermodel :
    DyadicTailRecurrence polynomialGapWord polynomialTailOrbit ∧
      (∀ n, 0 < polynomialGapWord n) ∧
      (∀ n, ∃ k : ℤ, polynomialGapWord n = 2 * k) ∧
      StrictMono polynomialGapWord ∧
      (∀ h N, RatIntegral (tailShift polynomialTailOrbit h N)) ∧
      (∀ n, polynomialGapWord (n + 1) - polynomialGapWord n = ((4 * n + 10 : ℕ) : ℤ)) ∧
      (∀ n,
        polynomialGapWord (n + 1) - polynomialGapWord n ≠ 2 ∧
        polynomialGapWord (n + 1) - polynomialGapWord n ≠ -2) ∧
      (∑' n : ℕ, polynomialGapDyadicTerm n) = 32 ∧
      ¬ Irrational (∑' n : ℕ, polynomialGapDyadicTerm n) := by
  sorry

end Erdos249257.ExternalVerification251PolynomialShiftCountermodel
