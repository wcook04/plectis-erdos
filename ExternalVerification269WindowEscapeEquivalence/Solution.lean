/-
Copyright (c) 2026 Will Cook. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Will Cook
-/
import Mathlib
import ErdosProblems.Erdos269.CofinalWindowEscapeEquivalence

namespace Erdos249257.ExternalVerification269WindowEscapeEquivalence

abbrev smooth3Val := ErdosProblems.Erdos269.smooth3Val
abbrev threePrimeHeight := ErdosProblems.Erdos269.threePrimeHeight
abbrev strictSmoothExponents := ErdosProblems.Erdos269.strictSmoothExponents
abbrev strictSmoothShell := ErdosProblems.Erdos269.strictSmoothShell
abbrev dyadicSmoothShell235 := ErdosProblems.Erdos269.dyadicSmoothShell235
abbrev dyadicShellMassQ235 := ErdosProblems.Erdos269.dyadicShellMassQ235
abbrev dyadicShellMassR235 := ErdosProblems.Erdos269.dyadicShellMassR235
abbrev DyadicInternalPower := ErdosProblems.Erdos269.DyadicInternalPower
noncomputable abbrev dyadicBlockBase235 := ErdosProblems.Erdos269.dyadicBlockBase235
abbrev dyadicBeforeThresholdCount235 :=
  ErdosProblems.Erdos269.dyadicBeforeThresholdCount235
abbrev dyadicOrderedBlockDigit235 :=
  ErdosProblems.Erdos269.dyadicOrderedBlockDigit235
noncomputable abbrev dyadicShellTsumTailR235 := ErdosProblems.Erdos269.dyadicShellTsumTailR235
noncomputable abbrev dyadicNormalizedTailStateR235 :=
  ErdosProblems.Erdos269.dyadicNormalizedTailStateR235
noncomputable abbrev trueNormalizedState := ErdosProblems.Erdos269.trueNormalizedState
abbrev leastPositiveResidue := ErdosProblems.Erdos269.leastPositiveResidue
abbrev windowBase := ErdosProblems.Erdos269.windowBase
abbrev windowForcing := ErdosProblems.Erdos269.windowForcing
abbrev CofinalLocalWindowEscape :=
  ErdosProblems.Erdos269.CofinalLocalWindowEscape
abbrev bridgeWidth := ErdosProblems.Erdos269.bridgeWidth
abbrev ActualCofinalLocalWindowEscape :=
  ErdosProblems.Erdos269.ActualCofinalLocalWindowEscape

theorem actualCofinalLocalWindowEscape_iff_irrational_value :
    ActualCofinalLocalWindowEscape ↔ Irrational (dyadicShellTsumTailR235 0) :=
  ErdosProblems.Erdos269.actualCofinalLocalWindowEscape_iff_irrational_value

theorem actualCofinalLocalWindowEscape_iff :
    ActualCofinalLocalWindowEscape ↔ Irrational (dyadicShellTsumTailR235 1) :=
  ErdosProblems.Erdos269.actualCofinalLocalWindowEscape_iff

theorem cofinalLocalWindowEscape_of_irrational
    (h : Irrational (dyadicShellTsumTailR235 1)) :
    ActualCofinalLocalWindowEscape :=
  ErdosProblems.Erdos269.cofinalLocalWindowEscape_of_irrational h

theorem cofinalLocalWindowEscape_of_irrational_of_quadratic
    (h : Irrational (dyadicShellTsumTailR235 1)) (sb : ℕ → ℕ → ℕ) (c : ℕ → ℕ)
    (hsb : ∀ B n, sb B n ≤ c B * (n + 1) ^ 2) :
    CofinalLocalWindowEscape dyadicBlockBase235 dyadicOrderedBlockDigit235 sb :=
  ErdosProblems.Erdos269.cofinalLocalWindowEscape_of_irrational_of_quadratic
    h sb c hsb

theorem exists_reducedCarry_of_value_eq_rat
    {p q : ℤ} (hq : 0 < q)
    (hval : dyadicShellTsumTailR235 1 = (p : ℝ) / (q : ℝ)) :
    ∃ (B a₀ : ℕ) (d : ℕ → ℤ), 0 < B ∧ Nat.Coprime B 30 ∧
      (∀ n, a₀ ≤ n →
        d (n + 1) = (dyadicBlockBase235 n : ℤ) * d n
          - (B : ℤ) * (dyadicOrderedBlockDigit235 n : ℤ)) ∧
      (∀ n, a₀ ≤ n → 0 < d n) ∧
      (∀ n, a₀ ≤ n → Int.natAbs (d n) ≤ B * bridgeWidth n) :=
  ErdosProblems.Erdos269.exists_reducedCarry_of_value_eq_rat hq hval

theorem trueNormalizedState_window (lo len : ℕ) :
    trueNormalizedState (lo + len)
      = ((windowBase (fun n => (dyadicBlockBase235 n : ℤ)) lo len : ℤ) : ℝ)
          * trueNormalizedState lo
        - ((windowForcing (fun n => (dyadicBlockBase235 n : ℤ))
              (fun n => (dyadicOrderedBlockDigit235 n : ℤ)) lo len : ℤ) : ℝ) :=
  ErdosProblems.Erdos269.trueNormalizedState_window lo len

theorem near_integer_of_residue_le_general
    (B lo len K : ℕ) (hB : 0 < B)
    (hKle : B * bridgeWidth (lo + len) ≤ K)
    (hres : leastPositiveResidue
        (Int.natAbs (windowBase (fun n => (dyadicBlockBase235 n : ℤ)) lo len))
        (-((B : ℤ) * windowForcing (fun n => (dyadicBlockBase235 n : ℤ))
             (fun n => (dyadicOrderedBlockDigit235 n : ℤ)) lo len))
      ≤ K) :
    ∃ k : ℤ, |(B : ℝ) * trueNormalizedState lo - (k : ℝ)|
      ≤ ((K : ℕ) : ℝ) / 2 ^ len :=
  ErdosProblems.Erdos269.near_integer_of_residue_le_general
    B lo len K hB hKle hres

theorem exists_pow_gt_quadratic (c lo : ℕ) :
    ∃ len : ℕ, 0 < len ∧ c * (lo + len + 1) ^ 2 < 2 ^ len :=
  ErdosProblems.Erdos269.exists_pow_gt_quadratic c lo

end Erdos249257.ExternalVerification269WindowEscapeEquivalence
