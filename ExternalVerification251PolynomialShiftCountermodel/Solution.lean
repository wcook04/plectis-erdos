/-
Copyright (c) 2026 Will Cook. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Will Cook
-/
import Mathlib
import ErdosProblems.Erdos251.PrimeGapDyadicTail
import ErdosProblems.Erdos251.PolynomialGapSeriesValue

/-!
# Source transport for the Erdős #251 polynomial-shift countermodel

The proof transports the complete source countermodel into the literal,
Mathlib-only Comparator vocabulary.  The single compared declaration includes
the recurrence, positivity, evenness, strict growth, integrality of every fixed
shift, the exact adjacent difference `4n + 10`, the resulting failure of the
adjacent `±2` event at every index, and the rational value `32` of the dyadic
series together with its non-irrationality.  Consequently those coarse
properties are jointly compatible with a rational sum and cannot force the
small-mismatch producer needed by the current #251 route.

This is internal infrastructure that removes one of our own routes.  It is a
statement about a model word, and it decides nothing about the actual
consecutive prime gaps or about Erdős #251.
-/

namespace Erdos249257.ExternalVerification251PolynomialShiftCountermodel

def DyadicTailRecurrence (g : ℕ → ℤ) (T : ℕ → ℚ) : Prop :=
  ∀ N, T (N + 1) = 2 * T N - g (N + 1)

def tailShift (T : ℕ → ℚ) (h N : ℕ) : ℚ :=
  T (N + h) - T N

def RatIntegral (x : ℚ) : Prop :=
  ∃ z : ℤ, x = z

def polynomialTailOrbit (n : ℕ) : ℚ :=
  (2 * (n + 4) ^ 2 : ℕ)

def polynomialGapWord (n : ℕ) : ℤ :=
  (2 * (n ^ 2 + 4 * n + 2) : ℕ)

noncomputable def polynomialGapDyadicTerm (n : ℕ) : ℝ :=
  (polynomialGapWord (n + 1) : ℝ) / 2 ^ (n + 1)

/-- The Comparator vocabulary word is the source word. -/
theorem polynomialGapWord_eq_source :
    polynomialGapWord = ErdosProblems.Erdos251.polynomialGapWord := rfl

/-- The Comparator vocabulary series term is the source series term. -/
theorem polynomialGapDyadicTerm_eq_source :
    polynomialGapDyadicTerm = ErdosProblems.Erdos251.polynomialGapDyadicTerm := rfl

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
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simpa [DyadicTailRecurrence, polynomialGapWord, polynomialTailOrbit,
      ErdosProblems.Erdos251.DyadicTailRecurrence,
      ErdosProblems.Erdos251.polynomialGapWord,
      ErdosProblems.Erdos251.polynomialTailOrbit] using
      ErdosProblems.Erdos251.polynomialTailOrbit_recurrence
  · intro n
    simpa [polynomialGapWord, ErdosProblems.Erdos251.polynomialGapWord] using
      ErdosProblems.Erdos251.polynomialGapWord_pos n
  · intro n
    simpa [polynomialGapWord, ErdosProblems.Erdos251.polynomialGapWord] using
      ErdosProblems.Erdos251.polynomialGapWord_even n
  · simpa [polynomialGapWord, ErdosProblems.Erdos251.polynomialGapWord] using
      ErdosProblems.Erdos251.polynomialGapWord_strictMono
  · intro h N
    simpa [tailShift, RatIntegral, polynomialTailOrbit,
      ErdosProblems.Erdos251.tailShift,
      ErdosProblems.Erdos251.RatIntegral,
      ErdosProblems.Erdos251.polynomialTailOrbit] using
      ErdosProblems.Erdos251.polynomialTailOrbit_shift_integral h N
  · intro n
    rw [polynomialGapWord_eq_source]
    exact ErdosProblems.Erdos251.polynomialGapWord_succ_sub n
  · intro n
    rw [polynomialGapWord_eq_source]
    exact ⟨ErdosProblems.Erdos251.polynomialGapWord_adjacent_difference_ne_two n,
      ErdosProblems.Erdos251.polynomialGapWord_adjacent_difference_ne_neg_two n⟩
  · rw [polynomialGapDyadicTerm_eq_source]
    exact ErdosProblems.Erdos251.tsum_polynomialGapDyadicTerm_eq
  · rw [polynomialGapDyadicTerm_eq_source]
    exact ErdosProblems.Erdos251.not_irrational_tsum_polynomialGapDyadicTerm

end Erdos249257.ExternalVerification251PolynomialShiftCountermodel
