import Erdos249257.GreedyAchievementSet

/-! Finite prefix exclusion from the actual achievement set.
A certificate checks finitely many prefixes and a proved tail bound.
This is a consequence of classical subsum geometry, not a new irrationality criterion.
-/
noncomputable section
namespace ErdosProblems.Erdos257.PaperCompleteR8
open Erdos249257 Finset

def prefixValue (F : Finset ℕ) : ℝ := ∑ k ∈ F, mersenneWeight (k + 1)

/-- Every actual value belongs to an interval above a finite binary prefix. -/
theorem achievement_mem_finite_prefix_interval (n : ℕ) {x : ℝ}
    (hx : x ∈ mersenneAchievementSet) :
    ∃ F ∈ (Finset.range n).powerset,
      x ∈ Set.Icc (prefixValue F) (prefixValue F + mersenneTail n) := by
  classical
  obtain ⟨A, hA, rfl⟩ := hx
  let F := (Finset.range n).filter (fun k => k + 1 ∈ A)
  refine ⟨F, Finset.mem_powerset.mpr (Finset.filter_subset _ _), ?_⟩
  have hp : prefixValue F =
      ∑ k ∈ Finset.range n, Set.indicator A mersenneWeight (k + 1) := by
    simp only [prefixValue, F, Finset.sum_filter, Set.indicator_apply]
  have he := positiveMersenneSupportValue_eq_prefix_add_suffix A n
  have hlo := positiveMersenneSupportSuffix_nonneg A n
  have hhi := positiveMersenneSupportSuffix_le_tail A n
  rw [← hp] at he
  constructor <;> linarith only [he, hlo, hhi]

/-- A finite family of disjointness checks gives genuine nonmembership. -/
theorem not_mem_achievement_of_finite_prefix_certificate (n : ℕ) (U x : ℝ)
    (hU : mersenneTail n ≤ U)
    (hcheck : ∀ F ∈ (Finset.range n).powerset,
      x < prefixValue F ∨ prefixValue F + U < x) :
    x ∉ mersenneAchievementSet := by
  intro hx
  obtain ⟨F, hF, hlo, hhi⟩ := achievement_mem_finite_prefix_interval n hx
  rcases hcheck F hF with h | h <;> linarith

/-- The first unresolved tail has the concrete rational upper bound 2/3. -/
theorem mersenne_tail_one_le_two_thirds : mersenneTail 1 ≤ (2 / 3 : ℝ) := by
  convert mersenneTail_le_two_mul_weight 1 using 1 <;> norm_num [mersenneWeight]

/-- An entire rationally bounded interval is excluded, not merely one point. -/
theorem first_gap_interval_excluded {x : ℝ}
    (hlo : (2 / 3 : ℝ) < x) (hhi : x < 1) :
    x ∉ mersenneAchievementSet := by
  apply not_mem_achievement_of_finite_prefix_certificate 1 (2 / 3) x
    mersenne_tail_one_le_two_thirds
  intro F hF
  have hs : F ⊆ {0} := by
    simpa only [Finset.range_one] using Finset.mem_powerset.mp hF
  rcases Finset.subset_singleton_iff.mp hs with h | h
  · subst F
    right
    simpa only [prefixValue, Finset.sum_empty, zero_add] using hlo
  · subst F
    left
    simpa only [prefixValue, Finset.sum_singleton, zero_add, mersenneWeight,
      pow_one, show (2 : ℝ) - 1 = 1 by norm_num, div_one] using hhi

/-- The displayed three-fourths example, obtained from two finite prefix checks. -/
theorem three_fourths_finite_prefix_exclusion :
    (3 / 4 : ℝ) ∉ mersenneAchievementSet :=
  first_gap_interval_excluded (by norm_num) (by norm_num)

#print axioms not_mem_achievement_of_finite_prefix_certificate
#print axioms three_fourths_finite_prefix_exclusion
end ErdosProblems.Erdos257.PaperCompleteR8
end
