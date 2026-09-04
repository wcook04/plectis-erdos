/-
Copyright (c) 2026 Will Cook. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Will Cook
-/
import ExternalVerification1041TranslationAvoidance.Statements
import ErdosProblems.Erdos1041.NewtonFlowRaySeparation

/-!
# Source transport for the #1041 translation-avoidance boundary

The proof is the exact source theorem.  Its scope is finite-family generic
position under a common translation; it does not close unrestricted Erdős
#1041 or supply a polynomial root path-length estimate.
-/

namespace Erdos249257.ExternalVerification1041TranslationAvoidance

theorem exists_small_translation_separating_arguments
    {ι : Type*} [Fintype ι] (c : ι → ℂ)
    (hc : Function.Injective c) {ε : ℝ} (hε : 0 < ε) :
    ∃ shift : ℂ, ‖shift‖ < ε ∧
      (∀ i, c i + shift ≠ 0) ∧
      ∀ i j, i ≠ j →
        ¬ SamePositiveRay (c i + shift) (c j + shift) := by
  exact ErdosProblems.Erdos1041.exists_small_translation_separating_arguments
    c hc hε

end Erdos249257.ExternalVerification1041TranslationAvoidance
