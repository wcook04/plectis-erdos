/-
Copyright (c) 2026 Will Cook. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Will Cook
-/
import ExternalVerification1041NewtonDecay.Statements
import ErdosProblems.Erdos1041.NewtonFlowRaySeparation

/-!
# Source transport for the #1041 Newton-decay boundary

The proof is the exact source theorem.  Its scope is only the endpoint
obstruction supplied by exponential value decay; it does not establish a
short connecting curve or solve unrestricted Erdős #1041.
-/

namespace Erdos249257.ExternalVerification1041NewtonDecay

theorem no_newtonConnection_of_not_samePositiveRay
    {startValue endValue : ℂ} {time : ℝ}
    (hrays : ¬ SamePositiveRay startValue endValue)
    (hconnection :
      endValue = (Real.exp (-time) : ℂ) * startValue) :
    False := by
  exact ErdosProblems.Erdos1041.no_newtonConnection_of_not_samePositiveRay
    hrays hconnection

end Erdos249257.ExternalVerification1041NewtonDecay
