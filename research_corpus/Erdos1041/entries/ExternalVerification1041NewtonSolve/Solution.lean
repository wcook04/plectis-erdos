/-
Copyright (c) 2026 Will Cook. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Will Cook
-/
import ExternalVerification1041NewtonSolve.Statements
import ErdosProblems.Erdos1041.ReciprocalNewtonExpansion

/-!
# Source transport for the #1041 solved Newton-identity kernel

The proof is the exact source theorem.  This fixture isolates the algebraic
solved form used to keep reciprocal Newton coordinates rational in the
polynomial coefficients.
-/

namespace Erdos249257.ExternalVerification1041NewtonSolve

theorem newton_solve {m : ℕ} (hm : 0 < m) (chat p : ℕ → ℂ) (h0 : chat 0 = 1)
    (h : (∑ j ∈ Finset.range m, chat j * p (m - j)) + m * chat m = 0) :
    p m = -(m * chat m) - ∑ j ∈ Finset.Ico 1 m, chat j * p (m - j) := by
  exact ErdosProblems.Erdos1041.ReciprocalNewtonExpansion.newton_solve
    hm chat p h0 h

end Erdos249257.ExternalVerification1041NewtonSolve
