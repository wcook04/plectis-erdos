/-
Copyright (c) 2026 Will Cook. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Will Cook
-/
import ExternalVerification1041LifetimeOrliczBound.Statements
import ErdosProblems.Erdos1041.AttachmentAgeLifetimeOrlicz

/-!
# Deliberate nearby mismatch for the #1041 lifetime-to-Orlicz bound

The negative fixture adds an irrelevant proposition argument after the
challenge parameters.  It can reuse the source proof, but Comparator must
reject it before semantic acceptance.
-/

namespace Erdos249257.ExternalVerification1041LifetimeOrliczBound

theorem orlicz_le_of_lifetime_le
    {lifetime size phi budget : ℝ}
    (hsize : 0 < size)
    (hexact : lifetime = size * phi)
    (hbudget : lifetime ≤ budget)
    (hweak : True) :
    phi ≤ budget / size := by
  exact ErdosProblems.Erdos1041.AttachmentAgeLifetimeOrlicz.orlicz_le_of_lifetime_le
    hsize hexact hbudget

end Erdos249257.ExternalVerification1041LifetimeOrliczBound
