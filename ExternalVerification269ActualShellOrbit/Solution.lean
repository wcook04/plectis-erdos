/-
Copyright (c) 2026 Will Cook. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Will Cook
-/
import Mathlib
import ErdosProblems.Erdos269.DyadicShellSummability

/-!
# Source transport for the actual dyadic shell orbit in Erdős #269

The proof repeats the Mathlib-only challenge definitions and combines the
source-current summability, genuine-tail recurrence, and exact escape
dichotomy without strengthening the surviving integral branch.
-/

namespace Erdos249257.ExternalVerification269ActualShellOrbit

open scoped BigOperators

noncomputable section

def smooth3Val (p q r i j k : ℕ) : ℕ :=
  p ^ i * q ^ j * r ^ k

def threePrimeHeight (p q r x : ℕ) : ℕ :=
  p ^ Nat.log p x * q ^ Nat.log q x * r ^ Nat.log r x

def strictSmoothExponents (p q r x : ℕ) : Finset (ℕ × ℕ × ℕ) :=
  ((Finset.range x).product ((Finset.range x).product (Finset.range x))).filter
    fun e => smooth3Val p q r e.1 e.2.1 e.2.2 < x

def strictSmoothShell (p q r x y : ℕ) : Finset (ℕ × ℕ × ℕ) :=
  strictSmoothExponents p q r y \ strictSmoothExponents p q r x

def dyadicSmoothShell235 (a : ℕ) : Finset (ℕ × ℕ × ℕ) :=
  strictSmoothShell 2 3 5 (2 ^ a) (2 ^ (a + 1))

def dyadicShellMassQ235 (a : ℕ) : ℚ :=
  ∑ e ∈ dyadicSmoothShell235 a,
    ((threePrimeHeight 2 3 5
      (smooth3Val 2 3 5 e.1 e.2.1 e.2.2) : ℚ)⁻¹)

def dyadicShellMassR235 (a : ℕ) : ℝ :=
  dyadicShellMassQ235 a

def DyadicInternalPower (p a e : ℕ) : Prop :=
  2 ^ a < p ^ e ∧ p ^ e < 2 ^ (a + 1)

noncomputable def dyadicBlockBase235 (a : ℕ) : ℕ :=
  by
    classical
    exact
      2 *
        (if ∃ e, DyadicInternalPower 3 a e then 3 else 1) *
        (if ∃ e, DyadicInternalPower 5 a e then 5 else 1)

def dyadicBeforeThresholdCount235 (p a : ℕ) : ℕ :=
  ((dyadicSmoothShell235 a).filter fun e =>
    smooth3Val 2 3 5 e.1 e.2.1 e.2.2 <
      p ^ Nat.log p (2 ^ (a + 1))).card

def dyadicOrderedBlockDigit235 (a : ℕ) : ℕ :=
  if 3 ^ Nat.log 3 (2 ^ (a + 1)) ≤ 5 ^ Nat.log 5 (2 ^ (a + 1)) then
    (dyadicSmoothShell235 a).card +
      10 * dyadicBeforeThresholdCount235 3 a +
      4 * dyadicBeforeThresholdCount235 5 a
  else
    (dyadicSmoothShell235 a).card +
      2 * dyadicBeforeThresholdCount235 3 a +
      12 * dyadicBeforeThresholdCount235 5 a

noncomputable def dyadicShellTsumTailR235 (a : ℕ) : ℝ :=
  ∑' n : ℕ, dyadicShellMassR235 (a + n)

noncomputable def dyadicNormalizedTailStateR235
    (tail : ℕ → ℝ) (a : ℕ) : ℝ :=
  ((threePrimeHeight 2 3 5 (2 ^ a) : ℝ) / 2) * tail a

def FarFromIntegers (x δ : ℝ) : Prop :=
  ∀ z : ℤ, δ ≤ |x - (z : ℝ)|

theorem actual_dyadicShellOrbit_recurrence_and_escape :
    Summable dyadicShellMassR235 ∧
      (∀ a : ℕ,
        dyadicNormalizedTailStateR235 dyadicShellTsumTailR235 (a + 1) =
          dyadicBlockBase235 a *
              dyadicNormalizedTailStateR235 dyadicShellTsumTailR235 a -
            dyadicOrderedBlockDigit235 a) ∧
      ((∃ a : ℕ, ∃ z : ℤ,
          dyadicNormalizedTailStateR235 dyadicShellTsumTailR235 a = (z : ℝ)) ∨
        ∀ a₀, ∃ a, a₀ ≤ a ∧
          FarFromIntegers
            (dyadicNormalizedTailStateR235 dyadicShellTsumTailR235 a)
            ((1 : ℝ) / 31)) := by
  refine ⟨?_, ?_, ?_⟩
  · simpa [dyadicShellMassR235, dyadicShellMassQ235,
      dyadicSmoothShell235, strictSmoothShell, strictSmoothExponents,
      threePrimeHeight, smooth3Val,
      ErdosProblems.Erdos269.dyadicShellMassR235,
      ErdosProblems.Erdos269.dyadicShellMassQ235,
      ErdosProblems.Erdos269.dyadicSmoothShell235,
      ErdosProblems.Erdos269.strictSmoothShell,
      ErdosProblems.Erdos269.strictSmoothExponents,
      ErdosProblems.Erdos269.threePrimeHeight,
      ErdosProblems.Erdos269.smooth3Val] using
      ErdosProblems.Erdos269.summable_dyadicShellMassR235
  · intro a
    simpa [dyadicNormalizedTailStateR235, dyadicShellTsumTailR235,
      dyadicShellMassR235, dyadicShellMassQ235, dyadicBlockBase235,
      DyadicInternalPower, dyadicOrderedBlockDigit235,
      dyadicBeforeThresholdCount235, dyadicSmoothShell235,
      strictSmoothShell, strictSmoothExponents, threePrimeHeight, smooth3Val,
      ErdosProblems.Erdos269.dyadicNormalizedTailStateR235,
      ErdosProblems.Erdos269.dyadicShellTsumTailR235,
      ErdosProblems.Erdos269.dyadicShellMassR235,
      ErdosProblems.Erdos269.dyadicShellMassQ235,
      ErdosProblems.Erdos269.dyadicBlockBase235,
      ErdosProblems.Erdos269.DyadicInternalPower,
      ErdosProblems.Erdos269.dyadicOrderedBlockDigit235,
      ErdosProblems.Erdos269.dyadicBeforeThresholdCount235,
      ErdosProblems.Erdos269.dyadicSmoothShell235,
      ErdosProblems.Erdos269.strictSmoothShell,
      ErdosProblems.Erdos269.strictSmoothExponents,
      ErdosProblems.Erdos269.threePrimeHeight,
      ErdosProblems.Erdos269.smooth3Val] using
      ErdosProblems.Erdos269.dyadicNormalizedShellTsumTailR235_succ a
  · simpa [FarFromIntegers, dyadicNormalizedTailStateR235,
      dyadicShellTsumTailR235, dyadicShellMassR235, dyadicShellMassQ235,
      dyadicBlockBase235, DyadicInternalPower, dyadicOrderedBlockDigit235,
      dyadicBeforeThresholdCount235, dyadicSmoothShell235,
      strictSmoothShell, strictSmoothExponents, threePrimeHeight, smooth3Val,
      ErdosProblems.Erdos269.FarFromIntegers,
      ErdosProblems.Erdos269.dyadicNormalizedTailStateR235,
      ErdosProblems.Erdos269.dyadicShellTsumTailR235,
      ErdosProblems.Erdos269.dyadicShellMassR235,
      ErdosProblems.Erdos269.dyadicShellMassQ235,
      ErdosProblems.Erdos269.dyadicBlockBase235,
      ErdosProblems.Erdos269.DyadicInternalPower,
      ErdosProblems.Erdos269.dyadicOrderedBlockDigit235,
      ErdosProblems.Erdos269.dyadicBeforeThresholdCount235,
      ErdosProblems.Erdos269.dyadicSmoothShell235,
      ErdosProblems.Erdos269.strictSmoothShell,
      ErdosProblems.Erdos269.strictSmoothExponents,
      ErdosProblems.Erdos269.threePrimeHeight,
      ErdosProblems.Erdos269.smooth3Val] using
      ErdosProblems.Erdos269.dyadicShellTsumTail_integer_or_cofinal_far

end

end Erdos249257.ExternalVerification269ActualShellOrbit
