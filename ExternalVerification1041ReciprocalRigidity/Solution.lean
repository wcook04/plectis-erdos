/-
Copyright (c) 2026 Will Cook. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Will Cook
-/
import ExternalVerification1041ReciprocalRigidity.Statements
import ErdosProblems.Erdos1041.NewtonFlowRaySeparation

/-!
# Source transport for the #1041 reciprocal boundary-rigidity kernel

The proof is the exact source theorem.  It records the equality case behind
the strict convex-hull alternative without claiming the full path theorem.
-/

namespace Erdos249257.ExternalVerification1041ReciprocalRigidity

theorem re_eq_zero_of_reciprocal_sum_eq_zero
    {ι : Type*} [Fintype ι] (w : ι → ℂ)
    (hw : ∀ i, 0 ≤ (w i).re) (hne : ∀ i, w i ≠ 0)
    (hbalance : ∑ i, (w i)⁻¹ = 0) :
    ∀ i, (w i).re = 0 := by
  exact ErdosProblems.Erdos1041.re_eq_zero_of_reciprocal_sum_eq_zero
    w hw hne hbalance

end Erdos249257.ExternalVerification1041ReciprocalRigidity
