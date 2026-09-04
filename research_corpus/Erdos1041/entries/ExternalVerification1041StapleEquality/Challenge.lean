/-
Copyright (c) 2026 Will Cook. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Will Cook
-/
import Mathlib

/-!
# Trusted challenge for the #1041 staple-length identity

The Challenge contains only the literal affine identity.  It does not import
the project-local source module or expose its namespace vocabulary.
-/

namespace Erdos249257.ExternalVerification1041StapleEquality

/- The equal-radius staple length expands to the root-modulus sum minus the
angular savings term. -/
theorem staple_length_eq (A B s c : ℝ) :
    (A - s) + s * c + (B - s) = A + B - s * (2 - c) := by
  sorry

end Erdos249257.ExternalVerification1041StapleEquality
