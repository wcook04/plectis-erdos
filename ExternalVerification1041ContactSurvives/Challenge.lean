/-
Copyright (c) 2026 Will Cook. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Will Cook
-/
import Mathlib

/-!
# Trusted challenge for the #1041 strict contact criterion

The Challenge contains only the literal ordered-algebra statement.  It does
not import the project-local source module or expose its namespace vocabulary.
-/

namespace Erdos249257.ExternalVerification1041ContactSurvives

/- A negative completed-square discriminant forces the contact value below
zero. -/
theorem contact_survives {kappa B V eps x F : ℝ} (hk : 0 < kappa)
    (hF : F ≤ -kappa * x ^ 2 + B * |x| + V + eps)
    (hdisc : V + eps + B ^ 2 / (4 * kappa) < 0) :
    F < 0 := by
  sorry

end Erdos249257.ExternalVerification1041ContactSurvives
