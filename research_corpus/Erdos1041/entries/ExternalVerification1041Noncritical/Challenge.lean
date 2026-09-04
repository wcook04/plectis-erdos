/-
Copyright (c) 2026 Will Cook. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Will Cook
-/
import Mathlib

/-!
# Trusted challenge for the #1041 noncriticality boundary

The Challenge contains only the literal theorem type.  It does not import
the project-local source module or expose its namespace vocabulary.
-/

namespace Erdos249257.ExternalVerification1041Noncritical

/-- A strict derivative margin prevents a smaller perturbation from creating a
critical point on the protected set. -/
theorem noncritical_on_of_norm_lt_uniform_lower_bound
    {f' : ℂ → ℂ} {C : Set ℂ} {lower : ℝ} {shift : ℂ}
    (hlower : ∀ z ∈ C, lower ≤ ‖f' z‖)
    (hshift : ‖shift‖ < lower) :
    ∀ z ∈ C, f' z + shift ≠ 0 := by
  sorry

end Erdos249257.ExternalVerification1041Noncritical
