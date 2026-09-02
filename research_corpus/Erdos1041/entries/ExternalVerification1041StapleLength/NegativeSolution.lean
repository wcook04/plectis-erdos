/-
Copyright (c) 2026 Will Cook. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Will Cook
-/
import ExternalVerification1041StapleLength.Statements
import ErdosProblems.Erdos1041.ReciprocalNewtonExpansion

/-!
# Deliberate nearby mismatch for the #1041 staple-length bound

The negative fixture adds an irrelevant proposition argument after the
challenge hypotheses.  It can reuse the source proof, but Comparator must
reject it before semantic acceptance.
-/

namespace Erdos249257.ExternalVerification1041StapleLength

theorem staple_length_lt_two {A B s c : ℝ} (hA : A < 1) (hB : B < 1)
    (hs : 0 ≤ s) (hc : c ≤ 2) (hweak : True) :
    A + B - s * (2 - c) < 2 := by
  exact ErdosProblems.Erdos1041.ReciprocalNewtonExpansion.staple_length_lt_two
    hA hB hs hc

end Erdos249257.ExternalVerification1041StapleLength
