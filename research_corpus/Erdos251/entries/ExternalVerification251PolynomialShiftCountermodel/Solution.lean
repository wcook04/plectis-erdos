/-
Copyright (c) 2026 Will Cook. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Will Cook
-/
import Mathlib
import ErdosProblems.Erdos251.PrimeGapDyadicTail

/-!
# Source transport for the Erdős #251 polynomial-shift countermodel

The proof transports the complete source countermodel into the literal,
Mathlib-only Comparator vocabulary.  The single compared declaration includes
the recurrence, positivity, evenness, strict growth, integrality of every fixed
shift, and global absence of adjacent `±2` differences.  Consequently those
coarse properties cannot force the small-mismatch producer needed by the
current #251 route.

This is a strategy-elimination theorem, not a theorem about the actual
consecutive-prime gaps and not a solution or refutation of Erdős #251.
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

theorem polynomialGapTailCountermodel :
    DyadicTailRecurrence polynomialGapWord polynomialTailOrbit ∧
      (∀ n, 0 < polynomialGapWord n) ∧
      (∀ n, ∃ k : ℤ, polynomialGapWord n = 2 * k) ∧
      StrictMono polynomialGapWord ∧
      (∀ h N, RatIntegral (tailShift polynomialTailOrbit h N)) ∧
      (∀ N,
        polynomialGapWord (N + 2) - polynomialGapWord (N + 1) ≠ 2 ∧
        polynomialGapWord (N + 2) - polynomialGapWord (N + 1) ≠ -2) := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
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
  · intro N
    simpa [polynomialGapWord, ErdosProblems.Erdos251.polynomialGapWord] using
      ErdosProblems.Erdos251.polynomialGapWord_no_adjacent_two_digit N

end Erdos249257.ExternalVerification251PolynomialShiftCountermodel
