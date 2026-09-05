/-
Copyright (c) 2026 Will Cook. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Will Cook
-/
import Mathlib
import ErdosProblems.Erdos243.SparseResetRecovery

/-!
# Source transport for summable-negative-mass rigidity in Erdős #243

This proof combines the checked eventual-zero endpoint with its checked
paper-facing Sylvester consequence in one Mathlib-only statement.
-/

namespace Erdos249257.ExternalVerification243SummableNegativeMassRigidity

def sylvesterNext (a : ℤ) : ℤ :=
  a ^ 2 - a + 1

def nextDenState (a D : ℤ) : ℤ :=
  a * D

def nextTailState (a D C : ℤ) : ℤ :=
  a * C - D

def centeredState (a D C : ℤ) : ℤ :=
  D - (a - 1) * C

noncomputable def negativeRelativeMass
    (C : ℕ → ℕ) (E : ℕ → ℤ) (n : ℕ) : ℝ :=
  (Int.natAbs (min (E n) 0) : ℝ) / C n

theorem summableNegativeMass_completeRigidity
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
  have hD' : ∀ n, D (n + 1) =
      ErdosProblems.Erdos243.nextDenState (a n) (D n) := by
    simpa [nextDenState, ErdosProblems.Erdos243.nextDenState] using hD
  have hC' : ∀ n, (C (n + 1) : ℤ) =
      ErdosProblems.Erdos243.nextTailState (a n) (D n) (C n) := by
    simpa [nextTailState, ErdosProblems.Erdos243.nextTailState] using hC
  have hstep' : ∀ n, (C (n + 1) : ℤ) = (C n : ℤ) -
      ErdosProblems.Erdos243.centeredState (a n) (D n) (C n) := by
    simpa [centeredState, ErdosProblems.Erdos243.centeredState] using hstep
  have hvanish' : ∀ K, ∃ N, ∀ n, N ≤ n →
      K * Int.natAbs
        (ErdosProblems.Erdos243.centeredState (a n) (D n) (C n)) < C n := by
    simpa [centeredState, ErdosProblems.Erdos243.centeredState] using hvanish
  have hsum' : Summable
      (ErdosProblems.Erdos243.negativeRelativeMass C
        (fun n ↦ ErdosProblems.Erdos243.centeredState (a n) (D n) (C n))) := by
    simpa [negativeRelativeMass,
      ErdosProblems.Erdos243.negativeRelativeMass, centeredState,
      ErdosProblems.Erdos243.centeredState] using hsum
  have hzero' : ∃ N, ∀ n, N ≤ n →
      ErdosProblems.Erdos243.centeredState (a n) (D n) (C n) = 0 :=
    ErdosProblems.Erdos243.eventually_zero_of_summable_negativeRelativeMass
      C (fun n ↦ ErdosProblems.Erdos243.centeredState (a n) (D n) (C n))
      hCpos hstep' hvanish' hsum'
  have hrec' : ∃ N, ∀ n, N ≤ n →
      a (n + 1) = ErdosProblems.Erdos243.sylvesterNext (a n) :=
    ErdosProblems.Erdos243.sylvesterNext_eventually_of_summable_negativeRelativeMass
      a D C hD' hC' hCpos hstep' hvanish' hsum'
  constructor
  · simpa [centeredState, ErdosProblems.Erdos243.centeredState] using hzero'
  · simpa [sylvesterNext, ErdosProblems.Erdos243.sylvesterNext] using hrec'

end Erdos249257.ExternalVerification243SummableNegativeMassRigidity
