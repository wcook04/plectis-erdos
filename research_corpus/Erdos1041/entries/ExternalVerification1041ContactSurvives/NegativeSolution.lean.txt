/-
Copyright (c) 2026 Will Cook. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Will Cook
-/
import ExternalVerification1041ContactSurvives.Statements
import ErdosProblems.Erdos1041.ReciprocalNewtonExpansion

/-!
# Deliberate nearby mismatch for the #1041 strict contact criterion

The negative fixture adds an irrelevant proposition argument after the
challenge parameters.  It can reuse the source proof, but Comparator must
reject it before semantic acceptance.
-/

namespace Erdos249257.ExternalVerification1041ContactSurvives

theorem contact_survives {kappa B V eps x F : ℝ} (hk : 0 < kappa)
    (hF : F ≤ -kappa * x ^ 2 + B * |x| + V + eps)
    (hdisc : V + eps + B ^ 2 / (4 * kappa) < 0)
    (hweak : True) :
    F < 0 := by
  exact ErdosProblems.Erdos1041.ReciprocalNewtonExpansion.contact_survives
    hk hF hdisc

end Erdos249257.ExternalVerification1041ContactSurvives
