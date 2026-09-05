/-
Copyright (c) 2026 Will Cook. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Will Cook
-/
import Mathlib
import ErdosProblems.Erdos243.ReciprocalTailRigidity

/-!
# Source transport for bounded-negative-part rigidity in Erdős #243

This proof packages the checked zero-defect and paper-facing Sylvester
endpoints into one Mathlib-only statement.
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
    (∃ N, ∀ n, N ≤ n → E n = 0) ∧
      ∃ N, ∀ n, N ≤ n →
        (a (n + 1) : ℤ) = sylvesterNext (a n : ℤ) := by
  have hE' : ∀ n, E n = ErdosProblems.Erdos243.centeredState
      (a n : ℤ) (D n : ℤ) (C n : ℤ) := by
    intro n
    simpa [centeredState, ErdosProblems.Erdos243.centeredState] using hE n
  have hzero : ∃ N, ∀ n, N ≤ n → E n = 0 :=
    ErdosProblems.Erdos243.eventuallyBoundedNegativePart_eventually_zero
      a C D E ha hCpos hC hD hE' hcentered hbound hvanish
  have hrec : ∃ N, ∀ n, N ≤ n →
      (a (n + 1) : ℤ) = sylvesterNext (a n : ℤ) := by
    simpa [sylvesterNext, ErdosProblems.Erdos243.sylvesterNext] using
      ErdosProblems.Erdos243.boundedNegativePart_sylvesterNext_eventually
        a C D E ha hCpos hC hD hE' hcentered hbound hvanish
  exact ⟨hzero, hrec⟩

end Erdos249257.ExternalVerification243BoundedNegativePartRigidity
