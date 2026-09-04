/-
Copyright (c) 2026 Will Cook. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Will Cook
-/
import ExternalVerification1041QuadraticContact.Statements
import ErdosProblems.Erdos1041.ReciprocalNewtonExpansion

/-!
# Deliberate nearby mismatch for the #1041 quadratic-contact bound

The negative fixture adds an irrelevant proposition argument after the
challenge hypotheses.  It can reuse the source proof, but Comparator must
reject it before semantic acceptance.
-/

namespace Erdos249257.ExternalVerification1041QuadraticContact

theorem quadratic_contact_absorbs {kappa B V eps x F : ℝ} (hk : 0 < kappa)
    (hF : F ≤ -kappa * x ^ 2 + B * |x| + V + eps) (hweak : True) :
    F ≤ V + eps + B ^ 2 / (4 * kappa) := by
  exact ErdosProblems.Erdos1041.ReciprocalNewtonExpansion.quadratic_contact_absorbs
    hk hF

end Erdos249257.ExternalVerification1041QuadraticContact
