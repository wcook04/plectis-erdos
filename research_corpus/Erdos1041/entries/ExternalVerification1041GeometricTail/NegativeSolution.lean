/-
Copyright (c) 2026 Will Cook. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Will Cook
-/
import ExternalVerification1041GeometricTail.Statements
import ErdosProblems.Erdos1041.ReciprocalNewtonExpansion

/-!
# Deliberate nearby mismatch for the #1041 geometric-tail kernel

The negative fixture adds an irrelevant proposition argument after the
challenge hypotheses.  It can reuse the source proof, but Comparator must
reject it before semantic acceptance.
-/

namespace Erdos249257.ExternalVerification1041GeometricTail

theorem tsum_geometric_tail {q : ℝ} (hq0 : 0 ≤ q) (hq1 : q < 1) (N : ℕ)
    (hweak : True) :
    ∑' m : ℕ, q ^ (N + 1 + m) = q ^ (N + 1) / (1 - q) := by
  exact ErdosProblems.Erdos1041.ReciprocalNewtonExpansion.tsum_geometric_tail
    hq0 hq1 N

end Erdos249257.ExternalVerification1041GeometricTail
