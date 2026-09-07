/-
Copyright (c) 2026 Will Cook. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Will Cook
-/
import ExternalVerification1041ReciprocalHalfPlane.Statements
import ErdosProblems.Erdos1041.ReciprocalNewtonExpansion

/-!
# Source transport for the #1041 reciprocal half-plane boundary

The proof is the exact source theorem.  Its scope is the supporting
half-plane inequality for a reciprocal Newton vector; it does not establish
the global path construction or solve unrestricted Erdős #1041.
-/

namespace Erdos249257.ExternalVerification1041ReciprocalHalfPlane

theorem newtonReciprocalVector_supportingHalfPlane
    {ι : Type*} [Fintype ι] (w : ι → ℂ)
    (hw : ∀ i, 0 ≤ (w i).re) :
    (-(∑ i, (w i)⁻¹)⁻¹).re ≤ 0 := by
  exact ErdosProblems.Erdos1041.newtonReciprocalVector_supportingHalfPlane
    w hw

end Erdos249257.ExternalVerification1041ReciprocalHalfPlane
