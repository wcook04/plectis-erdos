/-
Copyright (c) 2026 Will Cook. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Will Cook
-/
import ErdosProblems.Erdos1041.PaperCubicSchur

namespace Erdos249257.ExternalVerification1041CubicRootCount

/-- Exact source transport of the normalized cubic root-count theorem. -/
theorem cubic_root_count (b : ℂ) (hb : 1 ≤ ‖1 - b ^ 3 / 2‖) :
    ∃ u v : ℂ, u ≠ v ∧ ‖u‖ ≤ 1 ∧ ‖v‖ ≤ 1 ∧
      u ^ 3 - (3 / 2 : ℂ) * b * u ^ 2 + 1 = 0 ∧
      v ^ 3 - (3 / 2 : ℂ) * b * v ^ 2 + 1 = 0 := by
  exact ErdosProblems.Erdos1041.PaperCubicSchur.cubic_root_count b hb

end Erdos249257.ExternalVerification1041CubicRootCount
