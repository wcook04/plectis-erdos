/-
Copyright (c) 2026 Will Cook. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Will Cook
-/
import ExternalVerification1041Noncritical.Statements
import ErdosProblems.Erdos1041.NewtonFlowRaySeparation

/-!
# Deliberate nearby mismatch for the #1041 noncriticality boundary

The negative fixture adds an irrelevant proposition argument after the
challenge hypotheses.  It can reuse the source proof, but its declaration
type is not the Challenge type, so Comparator must reject it before semantic
acceptance.
-/

namespace Erdos249257.ExternalVerification1041Noncritical

theorem noncritical_on_of_norm_lt_uniform_lower_bound
    {f' : ℂ → ℂ} {C : Set ℂ} {lower : ℝ} {shift : ℂ}
    (hlower : ∀ z ∈ C, lower ≤ ‖f' z‖)
    (hshift : ‖shift‖ < lower)
    (hweak : True) :
    ∀ z ∈ C, f' z + shift ≠ 0 := by
  exact ErdosProblems.Erdos1041.noncritical_on_of_norm_lt_uniform_lower_bound
    hlower hshift

end Erdos249257.ExternalVerification1041Noncritical
