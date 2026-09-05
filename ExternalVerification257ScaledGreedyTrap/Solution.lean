import Mathlib
import Erdos249257.GreedyTrapDynamics

namespace Erdos249257.ExternalVerification257ScaledGreedyTrap

open Set
open Filter Topology
open scoped BigOperators

noncomputable section

def mersenneWeight (n : ℕ) : ℝ :=
  Erdos249257.mersenneWeight n

def positiveMersenneSupportValue (A : Set ℕ) : ℝ :=
  Erdos249257.positiveMersenneSupportValue A

def mersenneAchievementSet : Set ℝ :=
  Erdos249257.mersenneAchievementSet

def greedyMersenneRemainder (x : ℝ) : ℕ → ℝ :=
  Erdos249257.greedyMersenneRemainder x

def scaledGreedyRemainder (x : ℝ) (N : ℕ) : ℝ :=
  Erdos249257.scaledGreedyRemainder x N

def mersenneScale (n : ℕ) : ℝ :=
  Erdos249257.mersenneScale n

def ScaledGreedyLowerBranchCofinally (x : ℝ) : Prop :=
  Erdos249257.ScaledGreedyLowerBranchCofinally x

def ScaledGreedyRemainderCofinallyBounded (x : ℝ) : Prop :=
  Erdos249257.ScaledGreedyRemainderCofinallyBounded x

theorem scaledGreedyRemainder_tendsto_atTop_of_not_mem {x : ℝ} (hx : 0 ≤ x)
    (hnot : x ∉ mersenneAchievementSet) :
    Tendsto (fun N : ℕ => scaledGreedyRemainder x N) atTop atTop := by
  change Tendsto
    (fun N : ℕ => Erdos249257.scaledGreedyRemainder x N) atTop atTop
  exact Erdos249257.scaledGreedyRemainder_tendsto_atTop_of_not_mem hx hnot

theorem mem_mersenneAchievementSet_iff_scaledRemainder_cofinallyBounded {x : ℝ}
    (hx : 0 ≤ x) :
    x ∈ mersenneAchievementSet ↔ ScaledGreedyRemainderCofinallyBounded x := by
  change x ∈ Erdos249257.mersenneAchievementSet ↔
    Erdos249257.ScaledGreedyRemainderCofinallyBounded x
  exact Erdos249257.mem_mersenneAchievementSet_iff_scaledRemainder_cofinallyBounded hx

theorem mersenneAchievementSet_eq_scaledGreedyTrap :
    mersenneAchievementSet =
      {x : ℝ | 0 ≤ x ∧ ∀ N : ℕ, scaledGreedyRemainder x N < 2} := by
  change Erdos249257.mersenneAchievementSet =
    {x : ℝ | 0 ≤ x ∧ ∀ N : ℕ,
      Erdos249257.scaledGreedyRemainder x N < 2}
  exact Erdos249257.mersenneAchievementSet_eq_scaledGreedyTrap

theorem rat_mem_mersenneAchievementSet_iff_scaledLowerBranchCofinally
    (q : ℚ) (hq : 0 ≤ q) :
    (q : ℝ) ∈ mersenneAchievementSet ↔
      ScaledGreedyLowerBranchCofinally (q : ℝ) := by
  change (q : ℝ) ∈ Erdos249257.mersenneAchievementSet ↔
    Erdos249257.ScaledGreedyLowerBranchCofinally (q : ℝ)
  exact
    Erdos249257.rat_mem_mersenneAchievementSet_iff_scaledLowerBranchCofinally
      q hq

theorem one_div_twentyOne_mem_iff_scaledLowerBranchCofinally :
    (1 / 21 : ℝ) ∈ mersenneAchievementSet ↔
      ScaledGreedyLowerBranchCofinally (1 / 21 : ℝ) := by
  change (1 / 21 : ℝ) ∈ Erdos249257.mersenneAchievementSet ↔
    Erdos249257.ScaledGreedyLowerBranchCofinally (1 / 21 : ℝ)
  exact Erdos249257.one_div_twentyOne_mem_iff_scaledLowerBranchCofinally

theorem one_div_twentyOne_mem_iff_scaledRemainder_cofinallyBounded :
    (1 / 21 : ℝ) ∈ mersenneAchievementSet ↔
      ScaledGreedyRemainderCofinallyBounded (1 / 21 : ℝ) := by
  change (1 / 21 : ℝ) ∈ Erdos249257.mersenneAchievementSet ↔
    Erdos249257.ScaledGreedyRemainderCofinallyBounded (1 / 21 : ℝ)
  exact Erdos249257.one_div_twentyOne_mem_iff_scaledRemainder_cofinallyBounded

end

end Erdos249257.ExternalVerification257ScaledGreedyTrap
