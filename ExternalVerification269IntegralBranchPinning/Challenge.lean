/-
Copyright (c) 2026 Will Cook. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Will Cook
-/
import Mathlib

/-!
# Trusted challenge for the Erdős #269 integral-branch pinning family

The definitions below reproduce the literal `{2,3,5}` infinite shell orbit.
The compared theorems give its exact pinning identity, upward closure of an
integral state, and uniqueness among all indefinitely window-tracking orbits.
-/

namespace Erdos249257.ExternalVerification269IntegralBranchPinning

open scoped BigOperators

noncomputable section

def smooth3Val (p q r i j k : ℕ) : ℕ := p ^ i * q ^ j * r ^ k

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

def dyadicShellMassR235 (a : ℕ) : ℝ := dyadicShellMassQ235 a

def DyadicInternalPower (p a e : ℕ) : Prop :=
  2 ^ a < p ^ e ∧ p ^ e < 2 ^ (a + 1)

noncomputable def dyadicBlockBase235 (a : ℕ) : ℕ :=
  by
    classical
    exact
      2 * (if ∃ e, DyadicInternalPower 3 a e then 3 else 1) *
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

/-- The genuine infinite normalized tail state. -/
noncomputable def trueNormalizedState (a : ℕ) : ℝ :=
  dyadicNormalizedTailStateR235 dyadicShellTsumTailR235 a

/-- Every true state is pinned exactly above its ordered digit anchor. -/
theorem trueNormalizedState_pinning (a : ℕ) :
    trueNormalizedState a =
      (dyadicOrderedBlockDigit235 a : ℝ) / (dyadicBlockBase235 a : ℝ) +
        trueNormalizedState (a + 1) / (dyadicBlockBase235 a : ℝ) := by
  sorry

/-- Exact finite-depth mixed-radix expansion of the genuine infinite state,
with the remaining source tail displayed rather than discarded. -/
theorem trueNormalizedState_eq_telescope (m K : ℕ) :
    trueNormalizedState m =
      (∑ i ∈ Finset.range K,
          (dyadicOrderedBlockDigit235 (m + i) : ℝ) /
            ∏ j ∈ Finset.range (i + 1), (dyadicBlockBase235 (m + j) : ℝ)) +
        (threePrimeHeight 2 3 5 (2 ^ m) : ℝ) / 2 *
          dyadicShellTsumTailR235 (m + K) := by
  sorry

/-- One integral true state forces every later true state to be integral. -/
theorem integral_state_upward_closed {a : ℕ} {z : ℤ}
    (hint : trueNormalizedState a = (z : ℝ)) :
    ∀ n, a ≤ n → ∃ z' : ℤ, trueNormalizedState n = (z' : ℝ) := by
  sorry

/-- Any orbit following the source recurrence forever in the same shrinking
anchor windows coincides with the genuine infinite tail at its basepoint. -/
theorem surviving_window_orbit_eq_true_state
    (width : ℕ → ℝ) (A : ℕ) (y : ℕ → ℝ)
    (hrec : ∀ n, A ≤ n →
      y (n + 1) =
        (dyadicBlockBase235 n : ℝ) * y n -
          (dyadicOrderedBlockDigit235 n : ℝ))
    (hwin : ∀ n, A ≤ n →
      (dyadicOrderedBlockDigit235 n : ℝ) / (dyadicBlockBase235 n : ℝ) < y n ∧
        y n ≤ (dyadicOrderedBlockDigit235 n : ℝ) /
          (dyadicBlockBase235 n : ℝ) + width n)
    (hwidth : ∀ n, A ≤ n →
      (dyadicOrderedBlockDigit235 n : ℝ) / (dyadicBlockBase235 n : ℝ) <
          trueNormalizedState n ∧
        trueNormalizedState n ≤
          (dyadicOrderedBlockDigit235 n : ℝ) /
            (dyadicBlockBase235 n : ℝ) + width n)
    (hvanish : ∀ ε > 0, ∃ k₀ : ℕ, ∀ k, k₀ ≤ k →
      width (A + k) / 2 ^ k < ε) :
    y A = trueNormalizedState A := by
  sorry

end

end Erdos249257.ExternalVerification269IntegralBranchPinning
