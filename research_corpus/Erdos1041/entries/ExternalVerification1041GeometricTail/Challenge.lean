/-
Copyright (c) 2026 Will Cook. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Will Cook
-/
import Mathlib

/-!
# Trusted challenge for the #1041 geometric-tail kernel

The Challenge contains only the literal infinite-series identity.  It does
not import the project-local source module or expose its namespace vocabulary.
-/

namespace Erdos249257.ExternalVerification1041GeometricTail

/-- The geometric tail beginning at `N + 1` has its closed-form sum when the
ratio lies in `[0, 1)`. -/
theorem tsum_geometric_tail {q : ℝ} (hq0 : 0 ≤ q) (hq1 : q < 1) (N : ℕ) :
    ∑' m : ℕ, q ^ (N + 1 + m) = q ^ (N + 1) / (1 - q) := by
  sorry

end Erdos249257.ExternalVerification1041GeometricTail
