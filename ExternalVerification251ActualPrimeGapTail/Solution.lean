/-
Copyright (c) 2026 Will Cook. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Will Cook
-/
import ErdosProblems.Erdos251.PrimeGapDyadicTail

open scoped BigOperators

namespace Erdos249257.ExternalVerification251ActualPrimeGapTail

noncomputable abbrev prime0 := ErdosProblems.Erdos251.prime0
noncomputable abbrev primeGap0 := ErdosProblems.Erdos251.primeGap0
noncomputable abbrev primeGapDyadicTerm := ErdosProblems.Erdos251.primeGapDyadicTerm
noncomputable abbrev primeGapPartialSumQ := ErdosProblems.Erdos251.primeGapPartialSumQ
abbrev DyadicTailRecurrence := ErdosProblems.Erdos251.DyadicTailRecurrence
noncomputable abbrev rationalPrimeGapTailState :=
  ErdosProblems.Erdos251.rationalPrimeGapTailState
abbrev tailShift := ErdosProblems.Erdos251.tailShift
abbrev RatIntegral := ErdosProblems.Erdos251.RatIntegral

theorem exists_rationalPrimeGapTailState_representation_of_not_irrational
    (h : ¬ Irrational (∑' n : ℕ, primeGapDyadicTerm n)) :
    ∃ S : ℚ,
      (S : ℝ) = ∑' n : ℕ, primeGapDyadicTerm n ∧
      ∀ N,
        ((rationalPrimeGapTailState S N : ℚ) : ℝ) =
          2 ^ (N + 1) *
            ∑' k : ℕ, primeGapDyadicTerm (k + (N + 1)) :=
  ErdosProblems.Erdos251.exists_rationalPrimeGapTailState_representation_of_not_irrational h

theorem rationalPrimeGapTailState_recurrence (S : ℚ) :
    DyadicTailRecurrence (fun n => (primeGap0 n : ℤ))
      (rationalPrimeGapTailState S) :=
  ErdosProblems.Erdos251.rationalPrimeGapTailState_recurrence S

theorem rationalPrimeGapTailShift_eventuallyIntegral
    (S : ℚ) :
    ∃ h, 0 < h ∧
      ∃ N₀, ∀ N, N₀ ≤ N →
        RatIntegral
          (tailShift (rationalPrimeGapTailState S) h N) :=
  ErdosProblems.Erdos251.rationalPrimeGapTailShift_eventuallyIntegral S

theorem rationalPrimeGapTail_has_positive_shift_not_eventually_small
    (S : ℚ) :
    ∃ h, 0 < h ∧
      ¬ ∃ N₀, ∀ N, N₀ ≤ N →
        -1 < tailShift (rationalPrimeGapTailState S) h N ∧
          tailShift (rationalPrimeGapTailState S) h N < 1 :=
  ErdosProblems.Erdos251.rationalPrimeGapTail_has_positive_shift_not_eventually_small S

end Erdos249257.ExternalVerification251ActualPrimeGapTail
