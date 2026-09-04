/-
Copyright (c) 2026 Will Cook. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Will Cook
-/
import Mathlib

/-!
# Trusted challenge for the #1041 translation-avoidance boundary

The Challenge contains only the literal theorem type.  It does not import
the project-local source module or expose its namespace vocabulary.
-/

namespace Erdos249257.ExternalVerification1041TranslationAvoidance

/-- A finite injective family admits arbitrarily small translations avoiding
zero and all positive-ray coincidences. -/
theorem exists_small_translation_separating_arguments
    {ι : Type*} [Fintype ι] (c : ι → ℂ)
    (hc : Function.Injective c) {ε : ℝ} (hε : 0 < ε) :
    ∃ shift : ℂ, ‖shift‖ < ε ∧
      (∀ i, c i + shift ≠ 0) ∧
      ∀ i j, i ≠ j →
        ¬ SamePositiveRay (c i + shift) (c j + shift) := by
  sorry

end Erdos249257.ExternalVerification1041TranslationAvoidance
