/-
Copyright (c) 2026 Will Cook. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Will Cook
-/
import ExternalVerification1041QuadraticContact.Statements
import ErdosProblems.Erdos1041.ReciprocalNewtonExpansion

/-!
# Source transport for the #1041 quadratic-contact bound

The proof is the exact source theorem.  This fixture isolates the
completed-square estimate used by the contact-survival criterion.
-/

namespace Erdos249257.ExternalVerification1041QuadraticContact

theorem quadratic_contact_absorbs {kappa B V eps x F : ℝ} (hk : 0 < kappa)
    (hF : F ≤ -kappa * x ^ 2 + B * |x| + V + eps) :
    F ≤ V + eps + B ^ 2 / (4 * kappa) := by
  exact ErdosProblems.Erdos1041.ReciprocalNewtonExpansion.quadratic_contact_absorbs
    hk hF

end Erdos249257.ExternalVerification1041QuadraticContact
