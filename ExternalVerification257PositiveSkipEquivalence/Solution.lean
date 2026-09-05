/-
Copyright (c) 2026 Will Cook. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Will Cook
-/
import Erdos249257.BooleanMobiusSkipRowCofinal

namespace Erdos249257.ExternalVerification257PositiveSkipEquivalence

open Set

noncomputable section

def mersenneWeightRat (n : ℕ) : ℚ :=
  Erdos249257.mersenneWeightRat n

noncomputable def mersenneWeight (n : ℕ) : ℝ :=
  Erdos249257.mersenneWeight n

noncomputable def positiveMersenneSupportValue (A : Set ℕ) : ℝ :=
  Erdos249257.positiveMersenneSupportValue A

def mersenneAchievementSet : Set ℝ :=
  Erdos249257.mersenneAchievementSet

def greedyMersenneRemainderRat (x : ℚ) : ℕ → ℚ :=
  Erdos249257.greedyMersenneRemainderRat x

def CofinalPositiveHalfGreedySkips : Prop :=
  ∀ N : ℕ, ∃ c : ℕ,
    max N 4 ≤ c ∧
      0 < greedyMersenneRemainderRat (1 / 2 : ℚ) (c - 1) ∧
      greedyMersenneRemainderRat (1 / 2 : ℚ) (c - 1) <
        mersenneWeightRat c

theorem greedyMersenneRemainderRat_half_pos (n : ℕ) :
    0 < greedyMersenneRemainderRat (1 / 2 : ℚ) n := by
  change 0 < Erdos249257.greedyMersenneRemainderRat
    (1 / 2 : ℚ) n
  exact Erdos249257.greedyMersenneRemainderRat_half_pos n

theorem cofinalPositiveHalfGreedySkips_iff_half_mem :
    CofinalPositiveHalfGreedySkips ↔
      (1 / 2 : ℝ) ∈ mersenneAchievementSet := by
  change Erdos249257.CofinalPositiveHalfGreedySkips ↔
    (1 / 2 : ℝ) ∈ Erdos249257.mersenneAchievementSet
  exact Erdos249257.cofinalPositiveHalfGreedySkips_iff_half_mem

end

end Erdos249257.ExternalVerification257PositiveSkipEquivalence
