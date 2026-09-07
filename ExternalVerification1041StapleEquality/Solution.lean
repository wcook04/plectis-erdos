/-
Copyright (c) 2026 Will Cook. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Will Cook
-/
import ExternalVerification1041StapleEquality.Statements
import ErdosProblems.Erdos1041.ReciprocalNewtonExpansion

/-!
# Source transport for the #1041 staple-length identity

The proof is the exact source theorem.  This fixture isolates the affine
length calculation underlying the strict staple bound.
-/

namespace Erdos249257.ExternalVerification1041StapleEquality

theorem staple_length_eq (A B s c : ℝ) :
    (A - s) + s * c + (B - s) = A + B - s * (2 - c) := by
  exact ErdosProblems.Erdos1041.ReciprocalNewtonExpansion.staple_length_eq
    A B s c

end Erdos249257.ExternalVerification1041StapleEquality
