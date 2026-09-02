/-
Copyright (c) 2026 Will Cook. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Will Cook
-/
import ExternalVerification1041SecondAgeBound.Statements
import ErdosProblems.Erdos1041.AttachmentAgeLifetimeOrlicz

/-!
# Deliberate nearby mismatch for the #1041 second-age tail bound

The negative fixture adds an irrelevant proposition argument after the
challenge parameters.  It can reuse the source proof, but Comparator must
reject it before semantic acceptance.
-/

namespace Erdos249257.ExternalVerification1041SecondAgeBound

theorem second_age_le_of_tail_lower
    {secondAge total count : ℝ}
    (hcount : 1 < count)
    (htail : (count - 1) * secondAge ≤ total)
    (hweak : True) :
    secondAge ≤ total / (count - 1) := by
  exact ErdosProblems.Erdos1041.AttachmentAgeLifetimeOrlicz.second_age_le_of_tail_lower
    hcount htail

end Erdos249257.ExternalVerification1041SecondAgeBound
