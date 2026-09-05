/-
Copyright (c) 2026 Will Cook. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Will Cook
-/
import ExternalVerification1041StapleLength.Statements
import ErdosProblems.Erdos1041.ReciprocalNewtonExpansion

/-!
# Source transport for the #1041 staple-length bound

The proof is the exact source theorem.  This fixture isolates the strict
geometric inequality used to show that a two-root staple cannot reach length
two when both root moduli are below one.
-/

namespace Erdos249257.ExternalVerification1041StapleLength

theorem staple_length_lt_two {A B s c : ℝ} (hA : A < 1) (hB : B < 1)
    (hs : 0 ≤ s) (hc : c ≤ 2) :
    A + B - s * (2 - c) < 2 := by
  exact ErdosProblems.Erdos1041.ReciprocalNewtonExpansion.staple_length_lt_two
    hA hB hs hc

end Erdos249257.ExternalVerification1041StapleLength
