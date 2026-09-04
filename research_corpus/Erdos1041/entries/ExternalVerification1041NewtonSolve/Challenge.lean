/-
Copyright (c) 2026 Will Cook. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Will Cook
-/
import Mathlib

/-!
# Trusted challenge for the #1041 solved Newton-identity kernel

The Challenge contains only the literal finite identity.  It does not import
the project-local source module or expose its namespace vocabulary.
-/

namespace Erdos249257.ExternalVerification1041NewtonSolve

/-- Solving the reversed-polynomial Newton identity isolates the reciprocal
coordinate `p m` as the current coefficient term plus lower coordinates. -/
theorem newton_solve {m : ℕ} (hm : 0 < m) (chat p : ℕ → ℂ) (h0 : chat 0 = 1)
    (h : (∑ j ∈ Finset.range m, chat j * p (m - j)) + m * chat m = 0) :
    p m = -(m * chat m) - ∑ j ∈ Finset.Ico 1 m, chat j * p (m - j) := by
  sorry

end Erdos249257.ExternalVerification1041NewtonSolve
