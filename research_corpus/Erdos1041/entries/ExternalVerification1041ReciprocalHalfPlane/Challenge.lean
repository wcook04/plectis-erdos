/-
Copyright (c) 2026 Will Cook. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Will Cook
-/
import Mathlib

/-!
# Trusted challenge for the #1041 reciprocal half-plane boundary

The Challenge contains only the literal theorem type.  It does not import
the project-local source module or expose its namespace vocabulary.
-/

namespace Erdos249257.ExternalVerification1041ReciprocalHalfPlane

/-- A Newton vector built from right-half-plane reciprocal displacements has
nonpositive real component in the supporting direction. -/
theorem newtonReciprocalVector_supportingHalfPlane
    {ι : Type*} [Fintype ι] (w : ι → ℂ)
    (hw : ∀ i, 0 ≤ (w i).re) :
    (-(∑ i, (w i)⁻¹)⁻¹).re ≤ 0 := by
  sorry

end Erdos249257.ExternalVerification1041ReciprocalHalfPlane
