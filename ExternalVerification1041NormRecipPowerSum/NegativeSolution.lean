/-
Copyright (c) 2026 Will Cook. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Will Cook
-/
import ExternalVerification1041NormRecipPowerSum.Statements
import ErdosProblems.Erdos1041.ReciprocalNewtonExpansion

/-!
# Deliberate nearby mismatch for the #1041 reciprocal power-sum bound

The negative fixture adds an irrelevant proposition argument after the
challenge hypotheses.  It can reuse the source proof, but Comparator must
reject it before semantic acceptance.
-/

namespace Erdos249257.ExternalVerification1041NormRecipPowerSum

theorem norm_recipPowerSum_le {n : ℕ} (a : Fin n → ℂ) (m : ℕ) {r : ℝ}
    (hr : 0 < r) (ha : ∀ j, r ≤ ‖a j‖) (hweak : True) :
    ‖∑ j, (a j)⁻¹ ^ m‖ ≤ n * (r⁻¹) ^ m := by
  exact ErdosProblems.Erdos1041.ReciprocalNewtonExpansion.norm_recipPowerSum_le
    a m hr ha

end Erdos249257.ExternalVerification1041NormRecipPowerSum
