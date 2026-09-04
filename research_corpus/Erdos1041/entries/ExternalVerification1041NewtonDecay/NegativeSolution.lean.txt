/-
Copyright (c) 2026 Will Cook. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Will Cook
-/
import ExternalVerification1041NewtonDecay.Statements
import ErdosProblems.Erdos1041.NewtonFlowRaySeparation

/-!
# Deliberate nearby mismatch for the #1041 Newton-decay boundary

The negative fixture adds an irrelevant proposition argument after the
challenge hypotheses.  It can reuse the source proof, but its declaration
type is not the Challenge type, so Comparator must reject it before semantic
acceptance.
-/

namespace Erdos249257.ExternalVerification1041NewtonDecay

theorem no_newtonConnection_of_not_samePositiveRay
    {startValue endValue : ℂ} {time : ℝ}
    (hrays : ¬ SamePositiveRay startValue endValue)
    (hconnection :
      endValue = (Real.exp (-time) : ℂ) * startValue)
    (hweak : True) :
    False := by
  exact ErdosProblems.Erdos1041.no_newtonConnection_of_not_samePositiveRay
    hrays hconnection

end Erdos249257.ExternalVerification1041NewtonDecay
