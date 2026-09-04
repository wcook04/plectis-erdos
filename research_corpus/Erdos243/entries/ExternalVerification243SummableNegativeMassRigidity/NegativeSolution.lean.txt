/-
Copyright (c) 2026 Will Cook. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Will Cook
-/
import Mathlib

/-!
# Deliberate mismatch for the #243 summable-negative-mass package

The same-named declaration adds an irrelevant extra hypothesis.  Comparator
must reject it because its theorem type is not the trusted challenge type.
-/

namespace Erdos249257.ExternalVerification243SummableNegativeMassRigidity

def sylvesterNext (a : ℤ) : ℤ := a ^ 2 - a + 1
def nextDenState (a D : ℤ) : ℤ := a * D
def nextTailState (a D C : ℤ) : ℤ := a * C - D
def centeredState (a D C : ℤ) : ℤ := D - (a - 1) * C
noncomputable def negativeRelativeMass
    (C : ℕ → ℕ) (E : ℕ → ℤ) (n : ℕ) : ℝ :=
  (Int.natAbs (min (E n) 0) : ℝ) / C n

theorem summableNegativeMass_completeRigidity
    (_extra : True)
    (a D : ℕ → ℤ) (C : ℕ → ℕ)
    (hD : ∀ n, D (n + 1) = nextDenState (a n) (D n))
    (hC : ∀ n, (C (n + 1) : ℤ) = nextTailState (a n) (D n) (C n))
    (hCpos : ∀ n, 0 < C n)
    (hstep : ∀ n, (C (n + 1) : ℤ) =
      (C n : ℤ) - centeredState (a n) (D n) (C n))
    (hvanish : ∀ K, ∃ N, ∀ n, N ≤ n →
      K * Int.natAbs (centeredState (a n) (D n) (C n)) < C n)
    (hsum : Summable (negativeRelativeMass C
      (fun n ↦ centeredState (a n) (D n) (C n)))) :
    (∃ N, ∀ n, N ≤ n → centeredState (a n) (D n) (C n) = 0) ∧
      ∃ N, ∀ n, N ≤ n → a (n + 1) = sylvesterNext (a n) := by
  sorry

end Erdos249257.ExternalVerification243SummableNegativeMassRigidity
