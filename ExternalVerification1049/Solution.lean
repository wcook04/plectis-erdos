/-
Copyright (c) 2026 Will Cook. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Will Cook
-/
import ExternalVerification1049.Statements
import ErdosProblems.Erdos1049.RationalBaseLambert

/-!
# Source transport for the #1049 numerical-height packet

The proof is a direct transport of the public Lean certificate. This module
proves no irrationality statement about the base `7/2`.
-/

namespace Erdos249257.ExternalVerification1049

theorem comparator_sevenHalves_numericalHeight :
    Real.log 2 / Real.log 7 < (1 : ℝ) / 2 - 1 / Real.pi ^ 2 := by
  exact ErdosProblems.Erdos1049.sevenHalves_bundschuhVaananen_margin

end Erdos249257.ExternalVerification1049
