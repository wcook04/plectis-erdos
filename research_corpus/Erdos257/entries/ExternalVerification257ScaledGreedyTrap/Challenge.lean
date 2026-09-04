import Mathlib

namespace Erdos249257.ExternalVerification257ScaledGreedyTrap

open Set
open Filter Topology
open scoped BigOperators

noncomputable section

def mersenneWeight (n : ℕ) : ℝ :=
  1 / ((2 : ℝ) ^ n - 1)

def positiveMersenneSupportValue (A : Set ℕ) : ℝ :=
  ∑' k : ℕ, Set.indicator A mersenneWeight (k + 1)

def mersenneAchievementSet : Set ℝ :=
  {x | ∃ A : Set ℕ, 0 ∉ A ∧ x = positiveMersenneSupportValue A}

def greedyMersenneRemainder (x : ℝ) : ℕ → ℝ
  | 0 => x
  | n + 1 =>
      if mersenneWeight (n + 1) ≤ greedyMersenneRemainder x n then
        greedyMersenneRemainder x n - mersenneWeight (n + 1)
      else
        greedyMersenneRemainder x n

def scaledGreedyRemainder (x : ℝ) (N : ℕ) : ℝ :=
  (2 : ℝ) ^ N * greedyMersenneRemainder x N

def mersenneScale (n : ℕ) : ℝ :=
  (2 : ℝ) ^ n * mersenneWeight n

def ScaledGreedyLowerBranchCofinally (x : ℝ) : Prop :=
  ∀ K : ℕ, ∃ N : ℕ, K ≤ N ∧
    2 * scaledGreedyRemainder x N < mersenneScale (N + 1)

/-- One bounded cofinal subsequence of the scaled greedy remainder. -/
def ScaledGreedyRemainderCofinallyBounded (x : ℝ) : Prop :=
  ∃ B : ℝ, ∀ K : ℕ, ∃ N : ℕ, K ≤ N ∧ scaledGreedyRemainder x N ≤ B

/-- Outside the achievement set the scaled orbit escapes to infinity. -/
theorem scaledGreedyRemainder_tendsto_atTop_of_not_mem {x : ℝ} (hx : 0 ≤ x)
    (hnot : x ∉ mersenneAchievementSet) :
    Tendsto (fun N : ℕ => scaledGreedyRemainder x N) atTop atTop := by
  sorry

/-- Membership is equivalent to the existence of one bounded cofinal
subsequence; no global orbit bound is assumed. -/
theorem mem_mersenneAchievementSet_iff_scaledRemainder_cofinallyBounded {x : ℝ}
    (hx : 0 ≤ x) :
    x ∈ mersenneAchievementSet ↔ ScaledGreedyRemainderCofinallyBounded x := by
  sorry

/-- The achievement set is exactly the non-escaping set below the universal
scaled barrier `2`. -/
theorem mersenneAchievementSet_eq_scaledGreedyTrap :
    mersenneAchievementSet =
      {x : ℝ | 0 ≤ x ∧ ∀ N : ℕ, scaledGreedyRemainder x N < 2} := by
  sorry

/-- For every nonnegative rational target, membership is exactly cofinal
crossing of the moving lower separatrix. -/
theorem rat_mem_mersenneAchievementSet_iff_scaledLowerBranchCofinally
    (q : ℚ) (hq : 0 ≤ q) :
    (q : ℝ) ∈ mersenneAchievementSet ↔
      ScaledGreedyLowerBranchCofinally (q : ℝ) := by
  sorry

/-- The source-current canonical `1/21` endpoint. -/
theorem one_div_twentyOne_mem_iff_scaledLowerBranchCofinally :
    (1 / 21 : ℝ) ∈ mersenneAchievementSet ↔
      ScaledGreedyLowerBranchCofinally (1 / 21 : ℝ) := by
  sorry

/-- The `1/21` specialization of the weakest bounded-return criterion. -/
theorem one_div_twentyOne_mem_iff_scaledRemainder_cofinallyBounded :
    (1 / 21 : ℝ) ∈ mersenneAchievementSet ↔
      ScaledGreedyRemainderCofinallyBounded (1 / 21 : ℝ) := by
  sorry

end

end Erdos249257.ExternalVerification257ScaledGreedyTrap
