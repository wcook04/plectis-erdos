/-
Copyright (c) 2026 Will Cook. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Will Cook
-/
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.Analysis.SpecialFunctions.Log.Basic

/-!
# Deliberate nearby mismatch for the #1049 numerical-height packet

This theorem has the same name as the challenge declaration but an altered
weak inequality and an extra hypothesis. Comparator accepting this file is a
security regression.
-/

namespace Erdos249257.ExternalVerification1049

theorem comparator_sevenHalves_numericalHeight
    (mismatch : Real.log 2 / Real.log 7 ≤ (1 : ℝ) / 2 - 1 / Real.pi ^ 2) :
    Real.log 2 / Real.log 7 ≤ (1 : ℝ) / 2 - 1 / Real.pi ^ 2 := mismatch

end Erdos249257.ExternalVerification1049
