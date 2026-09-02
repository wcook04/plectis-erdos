/-
Copyright (c) 2026 Will Cook. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Will Cook
-/
import ExternalVerification1041OrliczNoUniformLinear.Statements
import ErdosProblems.Erdos1041.AttachmentAgeLifetimeOrlicz

/-!
# Deliberate nearby mismatch for the #1041 Orlicz lower-bound obstruction

The negative fixture adds an irrelevant proposition argument after the
challenge parameters.  It can reuse the source proof, but Comparator must
reject it before semantic acceptance.
-/

namespace Erdos249257.ExternalVerification1041OrliczNoUniformLinear

theorem no_positive_uniform_linear_lower
    (Phi : ℝ → ℝ)
    (hsublinear : ∀ c : ℝ, 0 < c → ∃ x : ℝ, 0 < x ∧ Phi x < c * x)
    (hweak : True) :
    ¬ ∃ c : ℝ, 0 < c ∧ ∀ x : ℝ, 0 < x → c * x ≤ Phi x := by
  exact ErdosProblems.Erdos1041.AttachmentAgeLifetimeOrlicz.no_positive_uniform_linear_lower
    Phi hsublinear

end Erdos249257.ExternalVerification1041OrliczNoUniformLinear
