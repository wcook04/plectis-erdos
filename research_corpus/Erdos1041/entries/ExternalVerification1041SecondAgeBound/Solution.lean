/-
Copyright (c) 2026 Will Cook. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Will Cook
-/
import ExternalVerification1041SecondAgeBound.Statements
import ErdosProblems.Erdos1041.AttachmentAgeLifetimeOrlicz

/-!
# Source transport for the #1041 second-age tail bound

The proof is the exact source theorem.  This fixture isolates the final
ordered-age step selecting the sharp threshold used by Corollary D1.
-/

namespace Erdos249257.ExternalVerification1041SecondAgeBound

theorem second_age_le_of_tail_lower
    {secondAge total count : ℝ}
    (hcount : 1 < count)
    (htail : (count - 1) * secondAge ≤ total) :
    secondAge ≤ total / (count - 1) := by
  exact ErdosProblems.Erdos1041.AttachmentAgeLifetimeOrlicz.second_age_le_of_tail_lower
    hcount htail

end Erdos249257.ExternalVerification1041SecondAgeBound
