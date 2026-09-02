/-
Copyright (c) 2026 Will Cook. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Will Cook
-/
import ExternalVerification1041FiniteAvoidance.Statements
import ErdosProblems.Erdos1041.NewtonFlowRaySeparation

/-!
# Source transport for the #1041 finite-avoidance kernel

The proof is the exact source theorem.  This fixture isolates the finite
geometric step used by the translated critical-value separation argument.
-/

namespace Erdos249257.ExternalVerification1041FiniteAvoidance

theorem exists_small_avoiding_finite_realAffineLines
    {κ : Type*} [Fintype κ] (p v : κ → ℂ) {ε : ℝ} (hε : 0 < ε) :
    ∃ z : ℂ, ‖z‖ < ε ∧
      ∀ k, z ∉ Set.range (fun t : ℝ => t • v k + p k) := by
  exact ErdosProblems.Erdos1041.exists_small_avoiding_finite_realAffineLines
    p v hε

end Erdos249257.ExternalVerification1041FiniteAvoidance
