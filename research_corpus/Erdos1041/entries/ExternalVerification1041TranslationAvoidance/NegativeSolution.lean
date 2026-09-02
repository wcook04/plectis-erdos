/-
Copyright (c) 2026 Will Cook. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Will Cook
-/
import ExternalVerification1041TranslationAvoidance.Statements
import ErdosProblems.Erdos1041.NewtonFlowRaySeparation

/-!
# Deliberate nearby mismatch for the #1041 translation-avoidance boundary

The negative fixture adds an irrelevant proposition argument after the
challenge hypotheses.  It can reuse the source proof, but its declaration
type is not the Challenge type, so Comparator must reject it before semantic
acceptance.
-/

namespace Erdos249257.ExternalVerification1041TranslationAvoidance

theorem exists_small_translation_separating_arguments
    {ι : Type*} [Fintype ι] (c : ι → ℂ)
    (hc : Function.Injective c) {ε : ℝ} (hε : 0 < ε) (hweak : True) :
    ∃ shift : ℂ, ‖shift‖ < ε ∧
      (∀ i, c i + shift ≠ 0) ∧
      ∀ i j, i ≠ j →
        ¬ SamePositiveRay (c i + shift) (c j + shift) := by
  exact ErdosProblems.Erdos1041.exists_small_translation_separating_arguments
    c hc hε

end Erdos249257.ExternalVerification1041TranslationAvoidance
