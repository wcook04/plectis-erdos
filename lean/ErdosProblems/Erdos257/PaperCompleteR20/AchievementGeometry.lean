import Erdos249257.GreedyAchievementSet
import Mathlib.Analysis.Convex.Hull

namespace ErdosProblems.Erdos257.PaperCompleteR20
open Erdos249257 Set MeasureTheory

private theorem support_value_bounds (A : Set ℕ) :
    positiveMersenneSupportValue A ∈ Icc 0 erdosBorweinMersenneConstant := by
  have he := positiveMersenneSupportValue_eq_prefix_add_suffix A 0
  simp only [Finset.range_zero, Finset.sum_empty, zero_add] at he
  rw [he]
  exact ⟨positiveMersenneSupportSuffix_nonneg A 0,
    positiveMersenneSupportSuffix_le_tail A 0⟩

theorem convexHull_achievementSet :
    convexHull ℝ mersenneAchievementSet = Icc 0 erdosBorweinMersenneConstant := by
  apply Subset.antisymm
  · apply convexHull_min
    · rintro x ⟨A, hA, rfl⟩
      exact support_value_bounds A
    · exact convex_Icc _ _
  · have hz : (0 : ℝ) ∈ mersenneAchievementSet := by
      refine ⟨∅, by simp, ?_⟩
      simp [positiveMersenneSupportValue]
    have hE : erdosBorweinMersenneConstant ∈ mersenneAchievementSet := by
      refine ⟨{n : ℕ | 0 < n}, by simp, ?_⟩
      simp [positiveMersenneSupportValue, erdosBorweinMersenneConstant, mersenneTail]
    rw [← segment_eq_Icc (show (0 : ℝ) ≤ erdosBorweinMersenneConstant from mersenneTail_nonneg 0),
      ← convexHull_pair]
    exact convexHull_mono (by simpa only [pair_subset_iff] using And.intro hz hE)

theorem unique_positive_support {x : ℝ} (hx : x ∈ mersenneAchievementSet) :
    ∃! A : Set ℕ, 0 ∉ A ∧ positiveMersenneSupportValue A = x := by
  obtain ⟨A, hA0, hv⟩ := hx
  refine ⟨A, ⟨hA0, hv.symm⟩, ?_⟩
  rintro B ⟨hB0, hB⟩
  exact positiveMersenneSupportValue_injective_normalized hB0 hA0 (hB.trans hv)

/-- All geometric and coding assertions of long `thm:geometry`. -/
theorem paper_achievement_geometry :
    IsCompact mersenneAchievementSet ∧ IsClosed mersenneAchievementSet ∧
    Perfect mersenneAchievementSet ∧ IsTotallyDisconnected mersenneAchievementSet ∧
    IsNowhereDense mersenneAchievementSet ∧ volume mersenneAchievementSet = 1 ∧
    convexHull ℝ mersenneAchievementSet = Icc 0 erdosBorweinMersenneConstant ∧
    Function.Injective positiveMersenneDigitValue ∧
    ∀ x ∈ mersenneAchievementSet, ∃! A : Set ℕ,
      0 ∉ A ∧ positiveMersenneSupportValue A = x :=
  ⟨isCompact_mersenneAchievementSet, isClosed_mersenneAchievementSet,
    perfect_mersenneAchievementSet, isTotallyDisconnected_mersenneAchievementSet,
    isNowhereDense_mersenneAchievementSet, volume_mersenneAchievementSet,
    convexHull_achievementSet, positiveMersenneDigitValue_injective,
    fun _ hx ↦ unique_positive_support hx⟩

#print axioms paper_achievement_geometry
end ErdosProblems.Erdos257.PaperCompleteR20
