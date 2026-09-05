/-
Copyright (c) 2026 Will Cook. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Will Cook
-/
import Mathlib

/-!
# Trusted challenge for the #1041 reciprocal boundary-rigidity kernel

The Challenge contains only the literal half-plane conclusion.  It does not
import the project-local source module or expose its namespace vocabulary.
-/

namespace Erdos249257.ExternalVerification1041ReciprocalRigidity

/-- If nonzero displacements lie in a closed supported half-plane and their
reciprocals balance to zero, every displacement lies on the support line. -/
theorem re_eq_zero_of_reciprocal_sum_eq_zero
    {ι : Type*} [Fintype ι] (w : ι → ℂ)
    (hw : ∀ i, 0 ≤ (w i).re) (hne : ∀ i, w i ≠ 0)
    (hbalance : ∑ i, (w i)⁻¹ = 0) :
    ∀ i, (w i).re = 0 := by
  sorry

end Erdos249257.ExternalVerification1041ReciprocalRigidity
