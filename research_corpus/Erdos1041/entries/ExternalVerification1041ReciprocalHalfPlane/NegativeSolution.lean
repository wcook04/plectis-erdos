/-
Copyright (c) 2026 Will Cook. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Will Cook
-/
import ExternalVerification1041ReciprocalHalfPlane.Statements
import ErdosProblems.Erdos1041.ReciprocalNewtonExpansion

/-!
# Deliberate nearby mismatch for the #1041 reciprocal half-plane boundary

The negative fixture adds an irrelevant proposition argument after the
challenge hypotheses.  It can reuse the source proof, but its declaration
type is not the Challenge type, so Comparator must reject it before semantic
acceptance.
-/

namespace Erdos249257.ExternalVerification1041ReciprocalHalfPlane

theorem newtonReciprocalVector_supportingHalfPlane
    {ι : Type*} [Fintype ι] (w : ι → ℂ)
    (hw : ∀ i, 0 ≤ (w i).re)
    (hweak : True) :
    (-(∑ i, (w i)⁻¹)⁻¹).re ≤ 0 := by
  exact ErdosProblems.Erdos1041.newtonReciprocalVector_supportingHalfPlane
    w hw

end Erdos249257.ExternalVerification1041ReciprocalHalfPlane
