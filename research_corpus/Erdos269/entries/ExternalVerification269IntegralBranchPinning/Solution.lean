/-
Copyright (c) 2026 Will Cook. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Will Cook
-/
import ErdosProblems.Erdos269.IntegralBranchWidth

namespace Erdos249257.ExternalVerification269IntegralBranchPinning

abbrev smooth3Val := ErdosProblems.Erdos269.smooth3Val
abbrev threePrimeHeight := ErdosProblems.Erdos269.threePrimeHeight
abbrev strictSmoothExponents := ErdosProblems.Erdos269.strictSmoothExponents
abbrev strictSmoothShell := ErdosProblems.Erdos269.strictSmoothShell
abbrev dyadicSmoothShell235 := ErdosProblems.Erdos269.dyadicSmoothShell235
abbrev dyadicShellMassQ235 := ErdosProblems.Erdos269.dyadicShellMassQ235
abbrev dyadicShellMassR235 := ErdosProblems.Erdos269.dyadicShellMassR235
abbrev DyadicInternalPower := ErdosProblems.Erdos269.DyadicInternalPower
abbrev dyadicBlockBase235 := ErdosProblems.Erdos269.dyadicBlockBase235
abbrev dyadicBeforeThresholdCount235 :=
  ErdosProblems.Erdos269.dyadicBeforeThresholdCount235
abbrev dyadicOrderedBlockDigit235 :=
  ErdosProblems.Erdos269.dyadicOrderedBlockDigit235
abbrev dyadicShellTsumTailR235 := ErdosProblems.Erdos269.dyadicShellTsumTailR235
abbrev dyadicNormalizedTailStateR235 :=
  ErdosProblems.Erdos269.dyadicNormalizedTailStateR235
abbrev trueNormalizedState := ErdosProblems.Erdos269.trueNormalizedState

theorem trueNormalizedState_pinning (a : ℕ) :
    trueNormalizedState a =
      (dyadicOrderedBlockDigit235 a : ℝ) / (dyadicBlockBase235 a : ℝ) +
        trueNormalizedState (a + 1) / (dyadicBlockBase235 a : ℝ) :=
  ErdosProblems.Erdos269.trueNormalizedState_pinning a

theorem trueNormalizedState_eq_telescope (m K : ℕ) :
    trueNormalizedState m =
      (∑ i ∈ Finset.range K,
          (dyadicOrderedBlockDigit235 (m + i) : ℝ) /
            ∏ j ∈ Finset.range (i + 1), (dyadicBlockBase235 (m + j) : ℝ)) +
        (threePrimeHeight 2 3 5 (2 ^ m) : ℝ) / 2 *
          dyadicShellTsumTailR235 (m + K) :=
  ErdosProblems.Erdos269.trueNormalizedState_eq_telescope m K

theorem integral_state_upward_closed {a : ℕ} {z : ℤ}
    (hint : trueNormalizedState a = (z : ℝ)) :
    ∀ n, a ≤ n → ∃ z' : ℤ, trueNormalizedState n = (z' : ℝ) :=
  ErdosProblems.Erdos269.integral_state_upward_closed hint

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
    y A = trueNormalizedState A :=
  ErdosProblems.Erdos269.surviving_window_orbit_eq_true_state
    width A y hrec hwin hwidth hvanish

end Erdos249257.ExternalVerification269IntegralBranchPinning
