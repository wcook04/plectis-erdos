/-
Copyright (c) 2026 Will Cook. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Will Cook
-/
import Mathlib

/-!
# Trusted challenge for the #1041 second-age tail bound

The Challenge contains only the literal ordered-algebra statement.  It does
not import the project-local source module or expose its namespace vocabulary.
-/

namespace Erdos249257.ExternalVerification1041SecondAgeBound

/- A tail lower bound selects the sharp `total / (count - 1)` threshold. -/
theorem second_age_le_of_tail_lower
    {secondAge total count : ℝ}
    (hcount : 1 < count)
    (htail : (count - 1) * secondAge ≤ total) :
    secondAge ≤ total / (count - 1) := by
  sorry

end Erdos249257.ExternalVerification1041SecondAgeBound
