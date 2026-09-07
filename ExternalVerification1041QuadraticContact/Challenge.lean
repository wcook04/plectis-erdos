/-
Copyright (c) 2026 Will Cook. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Will Cook
-/
import Mathlib

/-!
# Trusted challenge for the #1041 quadratic-contact bound

The Challenge contains only the literal completed-square inequality.  It does
not import the project-local source module or expose its namespace vocabulary.
-/

namespace Erdos249257.ExternalVerification1041QuadraticContact

/- A quadratic contact absorbs the transverse slope at the exact cost
`B² / (4 * kappa)`. -/
theorem quadratic_contact_absorbs {kappa B V eps x F : ℝ} (hk : 0 < kappa)
    (hF : F ≤ -kappa * x ^ 2 + B * |x| + V + eps) :
    F ≤ V + eps + B ^ 2 / (4 * kappa) := by
  sorry

end Erdos249257.ExternalVerification1041QuadraticContact
