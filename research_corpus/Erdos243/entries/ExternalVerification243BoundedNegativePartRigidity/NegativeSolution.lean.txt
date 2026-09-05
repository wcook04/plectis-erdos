/-
Copyright (c) 2026 Will Cook. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Will Cook
-/
import Mathlib

/-!
# Deliberately incomplete result for the #243 rigidity package

This same-named declaration retains only eventual Sylvester recurrence and
omits the theorem's eventual zero-defect conclusion.  Comparator must reject
the mathematically watered-down statement as a type mismatch.
-/

namespace Erdos249257.ExternalVerification243BoundedNegativePartRigidity

def sylvesterNext (a : ℤ) : ℤ :=
  a ^ 2 - a + 1

def centeredState (a D C : ℤ) : ℤ :=
  D - (a - 1) * C

theorem boundedNegativePart_completeRigidity
    (a C D : ℕ → ℕ) (E : ℕ → ℤ)
    (ha : ∀ n, 1 < a n)
    (hCpos : ∀ n, 0 < C n)
    (hC : ∀ n, C (n + 1) + D n = a n * C n)
    (hD : ∀ n, D (n + 1) = a n * D n)
    (hE : ∀ n, E n = centeredState (a n : ℤ) (D n : ℤ) (C n : ℤ))
    (hcentered : ∃ N, ∀ n, N ≤ n → Int.natAbs (E n) < C n)
    (hbound : ∃ N B : ℕ, ∀ n, N ≤ n → -(B : ℤ) ≤ E n)
    (hvanish : ∀ K, ∃ N, ∀ n, N ≤ n →
      K * Int.natAbs (E n) < C n) :
    ∃ N, ∀ n, N ≤ n →
      (a (n + 1) : ℤ) = sylvesterNext (a n : ℤ) := by
  sorry

end Erdos249257.ExternalVerification243BoundedNegativePartRigidity
