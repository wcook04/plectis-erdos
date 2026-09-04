/-
Copyright (c) 2026 Will Cook. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Will Cook
-/
import Mathlib

/-!
# Trusted challenge for the #1041 reciprocal power-sum bound

The Challenge contains only the literal finite inequality.  It does not
import the project-local source module or expose its namespace vocabulary.
-/

namespace Erdos249257.ExternalVerification1041NormRecipPowerSum

/- If all roots have modulus at least `r > 0`, the reciprocal power sum is
bounded by `n * r⁻ᵐ`; this is the input to the geometric tail estimates. -/
theorem norm_recipPowerSum_le {n : ℕ} (a : Fin n → ℂ) (m : ℕ) {r : ℝ}
    (hr : 0 < r) (ha : ∀ j, r ≤ ‖a j‖) :
    ‖∑ j, (a j)⁻¹ ^ m‖ ≤ n * (r⁻¹) ^ m := by
  sorry

end Erdos249257.ExternalVerification1041NormRecipPowerSum
