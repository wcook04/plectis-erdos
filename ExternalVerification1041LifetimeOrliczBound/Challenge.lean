/-
Copyright (c) 2026 Will Cook. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Will Cook
-/
import Mathlib

/-!
# Trusted challenge for the #1041 lifetime-to-Orlicz bound

The Challenge contains only the literal ordered-algebra statement.  It does
not import the project-local source module or expose its namespace vocabulary.
-/

namespace Erdos249257.ExternalVerification1041LifetimeOrliczBound

/- An exact lifetime factorization and a positive size convert the lifetime
upper bound into the corresponding Orlicz upper bound. -/
theorem orlicz_le_of_lifetime_le
    {lifetime size phi budget : ℝ}
    (hsize : 0 < size)
    (hexact : lifetime = size * phi)
    (hbudget : lifetime ≤ budget) :
    phi ≤ budget / size := by
  sorry

end Erdos249257.ExternalVerification1041LifetimeOrliczBound
