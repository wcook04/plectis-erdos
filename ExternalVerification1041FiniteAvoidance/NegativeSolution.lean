/-
Copyright (c) 2026 Will Cook. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Will Cook
-/
import ExternalVerification1041FiniteAvoidance.Statements
import ErdosProblems.Erdos1041.NewtonFlowRaySeparation

/-!
# Deliberate nearby mismatch for the #1041 finite-avoidance kernel

The negative fixture adds an irrelevant proposition argument after the
challenge hypotheses.  It can reuse the source proof, but Comparator must
reject it before semantic acceptance.
-/

namespace Erdos249257.ExternalVerification1041FiniteAvoidance

theorem exists_small_avoiding_finite_realAffineLines
    {κ : Type*} [Fintype κ] (p v : κ → ℂ) {ε : ℝ} (hε : 0 < ε)
    (hweak : True) :
    ∃ z : ℂ, ‖z‖ < ε ∧
      ∀ k, z ∉ Set.range (fun t : ℝ => t • v k + p k) := by
  exact ErdosProblems.Erdos1041.exists_small_avoiding_finite_realAffineLines
    p v hε

end Erdos249257.ExternalVerification1041FiniteAvoidance
