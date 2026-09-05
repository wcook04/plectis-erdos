/-
Copyright (c) 2026 Will Cook. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Will Cook
-/
import Mathlib

/-!
# Trusted challenge for the #1041 staple-length bound

The Challenge contains only the literal strict inequality.  It does not
import the project-local source module or expose its namespace vocabulary.
-/

namespace Erdos249257.ExternalVerification1041StapleLength

/- The equal-radius staple spends no more length than two roots in the open
unit disk, with no polynomial-dependent slack in the bound. -/
theorem staple_length_lt_two {A B s c : ℝ} (hA : A < 1) (hB : B < 1)
    (hs : 0 ≤ s) (hc : c ≤ 2) :
    A + B - s * (2 - c) < 2 := by
  sorry

end Erdos249257.ExternalVerification1041StapleLength
