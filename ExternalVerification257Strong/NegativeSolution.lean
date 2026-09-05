/-
Copyright (c) 2026 Will Cook. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Will Cook
-/
import ExternalVerification257Strong.Statements
import Erdos249257.BouquetReciprocalIrrationality
import ErdosProblems.Erdos257.GreedyRepairCriterion

/-! One deliberate mismatch: reinstating pairwise coprimality weakens the first result. -/

namespace Erdos249257.ExternalVerification.Strong257


private def orthogonalPetalBouquet_to_source {A : Set ℕ}
    (hB : OrthogonalPetalBouquet A) :
    Erdos249257.SupportSunflowerDichotomy.OrthogonalPetalBouquet A where
  Q := hB.Q
  Q_pos := hB.Q_pos
  exceptional := hB.exceptional
  core := hB.core
  petal := hB.petal
  exceptional_pos := hB.exceptional_pos
  exceptional_dvd_Q := hB.exceptional_dvd_Q
  core_pos := hB.core_pos
  core_dvd_Q := hB.core_dvd_Q
  petal_one_lt := hB.petal_one_lt
  petal_coprime_Q := hB.petal_coprime_Q
  petal_pairwise := hB.petal_pairwise
  support_eq := hB.support_eq
  summable_inv_petal := hB.summable_inv_petal

private theorem greedyMersenneRemainder_eq_source (x : ℝ) (N : ℕ) :
    greedyMersenneRemainder x N = Erdos249257.greedyMersenneRemainder x N := by
  induction N with
  | zero => rfl
  | succ N ih =>
      simp only [greedyMersenneRemainder, Erdos249257.greedyMersenneRemainder,
        ih, mersenneWeight, Erdos249257.mersenneWeight]

private theorem greedyMersenneSupport_eq_source (x : ℝ) :
    greedyMersenneSupport x = Erdos249257.greedyMersenneSupport x := by
  ext m
  simp only [greedyMersenneSupport, Erdos249257.greedyMersenneSupport,
    Set.mem_setOf_eq, greedyMersenneRemainder_eq_source,
    mersenneWeight, Erdos249257.mersenneWeight]

private theorem binaryCoeffPrefixNumerator_eq_source (c : ℕ → ℕ) (N : ℕ) :
    binaryCoeffPrefixNumerator c N = Erdos249257.binaryCoeffPrefixNumerator c N := by
  induction N with
  | zero => rfl
  | succ N ih =>
      simp only [binaryCoeffPrefixNumerator,
        Erdos249257.binaryCoeffPrefixNumerator, ih]

private theorem supportCoeff_eq_source (A : Set ℕ) :
    supportCoeff A = Erdos249257.supportCoeff A := by
  rfl

private theorem greedyBinaryDefect_eq_source (x : ℝ) (N : ℕ) :
    greedyBinaryDefect x N = ErdosProblems.Erdos257.greedyBinaryDefect x N := by
  simp only [greedyBinaryDefect, ErdosProblems.Erdos257.greedyBinaryDefect,
    binaryCoeffPrefixNumerator_eq_source, greedyMersenneSupport_eq_source,
    supportCoeff_eq_source]

theorem irrational_erdosSupportSeries_of_summable_reciprocal
    (b : ℕ) (A : Set ℕ) (hb : 2 ≤ b) (hA : A.Infinite)
    (hsum : Summable (reciprocalSupportTerm A))
    (_hcop : Set.Pairwise A Nat.Coprime) :
    Irrational (erdosSupportSeries b A) := by
  simpa only [erdosSupportSeries, Erdos249257.erdosSupportSeries] using
    Erdos249257.irrational_erdosSupportSeries_of_summable_reciprocal
      b A hb hA (show Summable (Erdos249257.reciprocalSupportTerm A) from hsum)

theorem irrational_erdosSupportSeries_of_orthogonalPetalBouquet_allBase
    (b : ℕ) (hb : 2 ≤ b) {A : Set ℕ} (hB : OrthogonalPetalBouquet A) :
    Irrational (erdosSupportSeries b A) := by
  simpa only [erdosSupportSeries, Erdos249257.erdosSupportSeries] using
    Erdos249257.SupportSunflowerDichotomy.irrational_erdosSupportSeries_of_orthogonalPetalBouquet_allBase
      b hb (orthogonalPetalBouquet_to_source hB)

theorem mem_iff_greedyBinaryDefect_sqrt_windows {x : ℝ} (hx : 0 ≤ x) :
    x ∈ mersenneAchievementSet ↔
      ∀ K : ℕ, ∃ N : ℕ, K ≤ N ∧ N < K + 2 * Nat.sqrt K + 12 ∧
        greedyBinaryDefect x (N + 1) ≤ greedyBinaryDefect x N := by
  simpa only [greedyBinaryDefect_eq_source,
    mersenneAchievementSet, Erdos249257.mersenneAchievementSet,
    positiveMersenneSupportValue, Erdos249257.positiveMersenneSupportValue,
    mersenneWeight, Erdos249257.mersenneWeight] using
    ErdosProblems.Erdos257.mem_iff_greedyBinaryDefect_sqrt_windows hx
end Erdos249257.ExternalVerification.Strong257
