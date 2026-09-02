/-
Copyright (c) 2026 Will Cook. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Will Cook
-/
import ExternalVerification1041Noncritical.Statements
import ErdosProblems.Erdos1041.NewtonFlowRaySeparation

/-!
# Source transport for the #1041 noncriticality boundary

The proof is the exact source theorem.  Its scope is the stated perturbative
derivative margin on a protected set; it does not establish the global
Newton-flow route or solve unrestricted Erdős #1041.
-/

namespace Erdos249257.ExternalVerification1041Noncritical

theorem noncritical_on_of_norm_lt_uniform_lower_bound
    {f' : ℂ → ℂ} {C : Set ℂ} {lower : ℝ} {shift : ℂ}
    (hlower : ∀ z ∈ C, lower ≤ ‖f' z‖)
    (hshift : ‖shift‖ < lower) :
    ∀ z ∈ C, f' z + shift ≠ 0 := by
  exact ErdosProblems.Erdos1041.noncritical_on_of_norm_lt_uniform_lower_bound
    hlower hshift

end Erdos249257.ExternalVerification1041Noncritical
