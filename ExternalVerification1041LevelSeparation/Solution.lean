/-
Copyright (c) 2026 Will Cook. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Will Cook
-/
import ExternalVerification1041LevelSeparation.Statements
import ErdosProblems.Erdos1041.LevelSeparation

/-!
# Source transport for the #1041 level-separation boundary

The proof is the exact source theorem.  Its scope is finite generic-position
avoidance for critical values; it does not establish the short connecting
curve or solve unrestricted Erdős #1041.
-/

namespace Erdos249257.ExternalVerification1041LevelSeparation

theorem exists_small_translation_separating_arguments_and_norms
    {ι : Type*} [Fintype ι] [DecidableEq ι] (c : ι → ℂ)
    (hc : Function.Injective c) {ε : ℝ} (hε : 0 < ε) :
    ∃ shift : ℂ, ‖shift‖ < ε ∧
      (∀ i, c i + shift ≠ 0) ∧
      (∀ i j, i ≠ j → ¬ SamePositiveRay (c i + shift) (c j + shift)) ∧
      (∀ i j, i ≠ j → ‖c i + shift‖ ≠ ‖c j + shift‖) := by
  exact ErdosProblems.Erdos1041.exists_small_translation_separating_arguments_and_norms
    c hc hε

end Erdos249257.ExternalVerification1041LevelSeparation
