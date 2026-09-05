/-
Copyright (c) 2026 Will Cook. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Will Cook
-/
import ExternalVerification1041LifetimeOrliczBound.Statements
import ErdosProblems.Erdos1041.AttachmentAgeLifetimeOrlicz

/-!
# Source transport for the #1041 lifetime-to-Orlicz bound

The proof is the exact source theorem.  This fixture isolates the edge
transform that converts a lifetime upper bound into an Orlicz upper bound.
-/

namespace Erdos249257.ExternalVerification1041LifetimeOrliczBound

theorem orlicz_le_of_lifetime_le
    {lifetime size phi budget : ℝ}
    (hsize : 0 < size)
    (hexact : lifetime = size * phi)
    (hbudget : lifetime ≤ budget) :
    phi ≤ budget / size := by
  exact ErdosProblems.Erdos1041.AttachmentAgeLifetimeOrlicz.orlicz_le_of_lifetime_le
    hsize hexact hbudget

end Erdos249257.ExternalVerification1041LifetimeOrliczBound
