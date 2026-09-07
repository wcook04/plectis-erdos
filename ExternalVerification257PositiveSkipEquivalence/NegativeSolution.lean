/-
Copyright (c) 2026 Will Cook. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Will Cook
-/
import Erdos257PeriodNoncollapse.BooleanMobiusSkipRowCofinal

namespace Erdos249257.ExternalVerification257PositiveSkipEquivalence

open Set

noncomputable section

def mersenneWeightRat (n : ℕ) : ℚ :=
  Erdos257PeriodNoncollapse.mersenneWeightRat n

noncomputable def mersenneWeight (n : ℕ) : ℝ :=
  Erdos257PeriodNoncollapse.mersenneWeight n

noncomputable def positiveMersenneSupportValue (A : Set ℕ) : ℝ :=
  Erdos257PeriodNoncollapse.positiveMersenneSupportValue A

def mersenneAchievementSet : Set ℝ :=
  Erdos257PeriodNoncollapse.mersenneAchievementSet

def greedyMersenneRemainderRat (x : ℚ) : ℕ → ℚ :=
  Erdos257PeriodNoncollapse.greedyMersenneRemainderRat x

def CofinalPositiveHalfGreedySkips : Prop :=
  ∀ N : ℕ, ∃ c : ℕ,
    max N 4 ≤ c ∧
      0 < greedyMersenneRemainderRat (1 / 2 : ℚ) (c - 1) ∧
      greedyMersenneRemainderRat (1 / 2 : ℚ) (c - 1) <
        mersenneWeightRat c

theorem greedyMersenneRemainderRat_half_pos (n : ℕ) :
    0 < greedyMersenneRemainderRat (1 / 2 : ℚ) n := by
  change 0 < Erdos257PeriodNoncollapse.greedyMersenneRemainderRat
    (1 / 2 : ℚ) n
  exact Erdos257PeriodNoncollapse.greedyMersenneRemainderRat_half_pos n

/- Deliberate interface mismatch: Comparator must reject this extra input. -/
theorem cofinalPositiveHalfGreedySkips_iff_half_mem (_extra : True) :
    CofinalPositiveHalfGreedySkips ↔
      (1 / 2 : ℝ) ∈ mersenneAchievementSet := by
  change Erdos257PeriodNoncollapse.CofinalPositiveHalfGreedySkips ↔
    (1 / 2 : ℝ) ∈ Erdos257PeriodNoncollapse.mersenneAchievementSet
  exact Erdos257PeriodNoncollapse.cofinalPositiveHalfGreedySkips_iff_half_mem

end

end Erdos249257.ExternalVerification257PositiveSkipEquivalence
