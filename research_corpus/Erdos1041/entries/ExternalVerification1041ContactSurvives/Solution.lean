/-
Copyright (c) 2026 Will Cook. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Will Cook
-/
import ExternalVerification1041ContactSurvives.Statements
import ErdosProblems.Erdos1041.ReciprocalNewtonExpansion

/-!
# Source transport for the #1041 strict contact criterion

The proof is the exact source theorem.  This fixture isolates the strict sign
consequence of the completed-square contact estimate.
-/

namespace Erdos249257.ExternalVerification1041ContactSurvives

theorem contact_survives {kappa B V eps x F : ℝ} (hk : 0 < kappa)
    (hF : F ≤ -kappa * x ^ 2 + B * |x| + V + eps)
    (hdisc : V + eps + B ^ 2 / (4 * kappa) < 0) :
    F < 0 := by
  exact ErdosProblems.Erdos1041.ReciprocalNewtonExpansion.contact_survives
    hk hF hdisc

end Erdos249257.ExternalVerification1041ContactSurvives
