/-
Copyright (c) 2026 Will Cook. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Will Cook
-/
import Mathlib
import ErdosProblems.Erdos257.GreedyRepairCriterion

/-!
# Source transport for the general greedy repair criterion

The two compared statements are transported from
`ErdosProblems.Erdos257.mem_iff_greedyBinaryDefect_cofinal_repairs` and
`ErdosProblems.Erdos257.mem_iff_greedyBinaryDefect_sqrt_windows`. The definition chain the
criterion rests on is re-declared here in Mathlib vocabulary and identified with the source
chain, one equation per definition, so that the transported statements are the source
statements and not a re-interpretation of them.
-/

namespace Erdos249257.ExternalVerification257GeneralRepairCriterion

open Set

noncomputable section

noncomputable def mersenneWeight (n : ℕ) : ℝ :=
  1 / ((2 : ℝ) ^ n - 1)

noncomputable def greedyMersenneRemainder (x : ℝ) : ℕ → ℝ
  | 0 => x
  | n + 1 =>
      if mersenneWeight (n + 1) ≤ greedyMersenneRemainder x n then
        greedyMersenneRemainder x n - mersenneWeight (n + 1)
      else
        greedyMersenneRemainder x n

noncomputable def greedyMersenneSupport (x : ℝ) : Set ℕ :=
  {m : ℕ | m ≠ 0 ∧ mersenneWeight m ≤ greedyMersenneRemainder x (m - 1)}

noncomputable def supportCoeff (A : Set ℕ) (n : ℕ) : ℕ :=
  letI := Classical.decPred fun d : ℕ => d ∈ A
  (n.divisors.filter fun d => d ∈ A).card

def binaryCoeffPrefixNumerator (c : ℕ → ℕ) : ℕ → ℕ
  | 0 => 0
  | N + 1 => 2 * binaryCoeffPrefixNumerator c N + c (N + 1)

/-- The greedy defect at scale `N`: the dyadic numerator of `x` minus the dyadic
numerator already paid by the exponents the greedy rule has selected. -/
noncomputable def greedyBinaryDefect (x : ℝ) (N : ℕ) : ℕ :=
  ⌊(2 : ℝ) ^ N * x⌋₊ -
    binaryCoeffPrefixNumerator (supportCoeff (greedyMersenneSupport x)) N

noncomputable def positiveMersenneSupportValue (A : Set ℕ) : ℝ :=
  ∑' k : ℕ, Set.indicator A mersenneWeight (k + 1)

def mersenneAchievementSet : Set ℝ :=
  {x : ℝ | ∃ A : Set ℕ, 0 ∉ A ∧ x = positiveMersenneSupportValue A}

/-! ### Identification with the source definitions -/

theorem mersenneWeight_eq : mersenneWeight = Erdos257PeriodNoncollapse.mersenneWeight := rfl

theorem greedyMersenneRemainder_eq :
    greedyMersenneRemainder = Erdos257PeriodNoncollapse.greedyMersenneRemainder := by
  funext x n
  induction n with
  | zero => rfl
  | succ n ih =>
    show (if mersenneWeight (n + 1) ≤ greedyMersenneRemainder x n then
        greedyMersenneRemainder x n - mersenneWeight (n + 1)
      else greedyMersenneRemainder x n) = _
    rw [ih, mersenneWeight_eq]
    rfl

theorem greedyMersenneSupport_eq :
    greedyMersenneSupport = Erdos257PeriodNoncollapse.greedyMersenneSupport := by
  funext x
  simp only [greedyMersenneSupport, Erdos257PeriodNoncollapse.greedyMersenneSupport,
    mersenneWeight_eq, greedyMersenneRemainder_eq]

theorem supportCoeff_eq : supportCoeff = Erdos257PeriodNoncollapse.supportCoeff := rfl

theorem binaryCoeffPrefixNumerator_eq :
    binaryCoeffPrefixNumerator = Erdos257PeriodNoncollapse.binaryCoeffPrefixNumerator := by
  funext c N
  induction N with
  | zero => rfl
  | succ N ih =>
    show 2 * binaryCoeffPrefixNumerator c N + c (N + 1) = _
    rw [ih]
    rfl

theorem greedyBinaryDefect_eq :
    greedyBinaryDefect = ErdosProblems.Erdos257.greedyBinaryDefect := by
  funext x N
  simp only [greedyBinaryDefect, ErdosProblems.Erdos257.greedyBinaryDefect,
    greedyMersenneSupport_eq, supportCoeff_eq, binaryCoeffPrefixNumerator_eq]

theorem positiveMersenneSupportValue_eq :
    positiveMersenneSupportValue = Erdos257PeriodNoncollapse.positiveMersenneSupportValue := by
  funext A
  simp only [positiveMersenneSupportValue,
    Erdos257PeriodNoncollapse.positiveMersenneSupportValue, mersenneWeight_eq]

theorem mersenneAchievementSet_eq :
    mersenneAchievementSet = Erdos257PeriodNoncollapse.mersenneAchievementSet := by
  simp only [mersenneAchievementSet, Erdos257PeriodNoncollapse.mersenneAchievementSet,
    positiveMersenneSupportValue_eq]

/-! ### The compared theorems -/

/-- Membership is cofinal non-increase of the greedy defect. -/
theorem mem_iff_greedyBinaryDefect_cofinal_repairs {x : ℝ} (hx : 0 ≤ x) :
    x ∈ mersenneAchievementSet ↔
      ∀ K : ℕ, ∃ N : ℕ, K ≤ N ∧
        greedyBinaryDefect x (N + 1) ≤ greedyBinaryDefect x N := by
  rw [mersenneAchievementSet_eq, greedyBinaryDefect_eq]
  exact ErdosProblems.Erdos257.mem_iff_greedyBinaryDefect_cofinal_repairs hx

/-- The same criterion inside every window of width `2*sqrt K + 12`. -/
theorem mem_iff_greedyBinaryDefect_sqrt_windows {x : ℝ} (hx : 0 ≤ x) :
    x ∈ mersenneAchievementSet ↔
      ∀ K : ℕ, ∃ N : ℕ, K ≤ N ∧ N < K + 2 * Nat.sqrt K + 12 ∧
        greedyBinaryDefect x (N + 1) ≤ greedyBinaryDefect x N := by
  rw [mersenneAchievementSet_eq, greedyBinaryDefect_eq]
  exact ErdosProblems.Erdos257.mem_iff_greedyBinaryDefect_sqrt_windows hx

end

end Erdos249257.ExternalVerification257GeneralRepairCriterion
