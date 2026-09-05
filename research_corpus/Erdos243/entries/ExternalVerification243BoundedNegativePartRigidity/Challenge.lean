/-
Copyright (c) 2026 Will Cook. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Will Cook
-/
import Mathlib

/-!
# Trusted challenge for bounded-negative-part rigidity in Erdős #243

The theorem isolates the complete rigidity consequence of the bounded-negative
branch for exact reciprocal-tail dynamics.  Eventual strict centering, an
eventual one-sided lower bound on the centered error, and division-free
normalized vanishing force both eventual zero defect and the exact Sylvester
recurrence.  No periodicity hypothesis is used.

The theorem is conditional on its explicit tail hypotheses.  It does not show
that every orbit in Erdős #243 satisfies them, and the unrestricted problem
remains open.
-/

namespace Erdos249257.ExternalVerification243BoundedNegativePartRigidity

/-- The Sylvester successor map. -/
def sylvesterNext (a : ℤ) : ℤ :=
  a ^ 2 - a + 1

/-- Centered reciprocal-tail error. -/
def centeredState (a D C : ℤ) : ℤ :=
  D - (a - 1) * C

/-- Complete rigidity of the bounded-negative centered-error branch: the
centered defect vanishes eventually and the denominator orbit consequently
follows the exact Sylvester recurrence eventually. -/
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
    (∃ N, ∀ n, N ≤ n → E n = 0) ∧
      ∃ N, ∀ n, N ≤ n →
        (a (n + 1) : ℤ) = sylvesterNext (a n : ℤ) := by
  sorry

end Erdos249257.ExternalVerification243BoundedNegativePartRigidity
