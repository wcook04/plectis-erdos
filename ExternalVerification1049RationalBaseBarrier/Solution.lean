/-
Copyright (c) 2026 Will Cook. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Will Cook
-/
import Mathlib
import ErdosProblems.Erdos1049.RationalBaseLambert

/-! Exact source transport for the rational-base clearing barrier. -/

namespace Erdos249257.ExternalVerification1049RationalBaseBarrier

open scoped BigOperators

def CoordinatewiseCorridor
    (a b N K Q digit : ℕ) : Prop :=
  0 < a ∧ 0 < Q ∧ 0 < digit ∧ digit ≤ N + K ∧
    a ^ K ∣ Q * digit ∧
    Q * b ^ (N + K + 1) < a ^ (K + 1)

def rationalBasePrefixQ
    (r s : ℚ) (coeff : ℕ → ℚ) (N : ℕ) : ℚ :=
  ∑ m ∈ Finset.range N,
    coeff (m + 1) * s ^ (m + 1) / r ^ (m + 1)

def rationalBaseClearedTailQ
    (r s B F : ℚ) (coeff : ℕ → ℚ) (N : ℕ) : ℚ :=
  B * r ^ N * (F - rationalBasePrefixQ r s coeff N)

def rationalBaseForcingNat
    (s B : ℕ) (coeff : ℕ → ℕ) (N : ℕ) : ℕ :=
  B * coeff (N + 1) * s ^ (N + 1)

theorem rationalBaseClearedTailQ_succ
    {r s B F : ℚ} {coeff : ℕ → ℚ} (hr : r ≠ 0) (N : ℕ) :
    rationalBaseClearedTailQ r s B F coeff (N + 1) =
      r * rationalBaseClearedTailQ r s B F coeff N -
        B * coeff (N + 1) * s ^ (N + 1) := by
  simpa [rationalBaseClearedTailQ, rationalBasePrefixQ,
    ErdosProblems.Erdos1049.rationalBaseClearedTailQ,
    ErdosProblems.Erdos1049.rationalBasePrefixQ] using
    ErdosProblems.Erdos1049.rationalBaseClearedTailQ_succ hr N

theorem twoPow_le_rationalBaseForcingNat
    {s B : ℕ} {coeff : ℕ → ℕ} {N : ℕ}
    (hs : 2 ≤ s) (hB : 1 ≤ B) (hc : 1 ≤ coeff (N + 1)) :
    2 ^ (N + 1) ≤ rationalBaseForcingNat s B coeff N := by
  simpa [rationalBaseForcingNat,
    ErdosProblems.Erdos1049.rationalBaseForcingNat] using
    ErdosProblems.Erdos1049.twoPow_le_rationalBaseForcingNat hs hB hc

theorem threeHalves_no_coordinatewiseCorridor
    {N K Q digit : ℕ} (hN : 1 ≤ N) (hK : 1 ≤ K) :
    ¬ CoordinatewiseCorridor 3 2 N K Q digit := by
  simpa [CoordinatewiseCorridor,
    ErdosProblems.Erdos1049.CoordinatewiseCorridor] using
    ErdosProblems.Erdos1049.threeHalves_no_coordinatewiseCorridor
      (Q := Q) (digit := digit) hN hK

end Erdos249257.ExternalVerification1049RationalBaseBarrier
