/-
Copyright (c) 2026 Will Cook. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Will Cook
-/
import Mathlib

/-!
# Trusted challenge for the #1041 Orlicz lower-bound obstruction

The Challenge contains only the literal logical statement.  It does not
import the project-local source module or expose its namespace vocabulary.
-/

namespace Erdos249257.ExternalVerification1041OrliczNoUniformLinear

/- A transform sublinear at zero cannot dominate positive age by one positive
universal linear constant. -/
theorem no_positive_uniform_linear_lower
    (Phi : ℝ → ℝ)
    (hsublinear : ∀ c : ℝ, 0 < c → ∃ x : ℝ, 0 < x ∧ Phi x < c * x) :
    ¬ ∃ c : ℝ, 0 < c ∧ ∀ x : ℝ, 0 < x → c * x ≤ Phi x := by
  sorry

end Erdos249257.ExternalVerification1041OrliczNoUniformLinear
