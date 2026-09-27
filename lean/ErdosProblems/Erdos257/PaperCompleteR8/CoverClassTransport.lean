import ErdosProblems.Erdos257.PaperCompleteR8.OptimizedCoverBudget
import ErdosProblems.Erdos257.PaperCompleteR8.CoverPotentialBounds

/-! # Transport the paper's fixed geometric weights to arbitrary-weight covers
This transport prevents a type-level gap between the actual strengthened-cover
predicate and the more general logarithmic obstruction.
-/
noncomputable section
namespace ErdosProblems.Erdos257.PaperCompleteR8
open ErdosProblems.Erdos257.PaperCompleteR7

/-- Every strengthened cover in the paper defines literal arbitrary-weight data. -/
def logBudgetCover_of_strengthened (C : PositiveCoverData)
    (hC : C.StrengthenedCostSummable) (A : Set ℕ) (hA : A ⊆ C.host) :
    LogBudgetCover A where
  frame := C.frame
  weight := coverThreshold 1
  exponent := C.exponent
  coefficient := C.coefficient
  frame_positive := C.frame_positive
  weight_positive := fun j => coverThreshold_pos (by norm_num) j
  weight_sum := by
    simpa only [tsum_coverThreshold] using (summable_coverThreshold 1).hasSum
  exponent_bounds := C.exponent_bounds
  coefficient_nonneg := C.coefficient_nonneg
  column_summable := C.column_summable
  covers := fun a ha => hA ha
  majorises := C.majorises
  budget_summable := by
    have hs := summable_coverScaledCost C hC (by norm_num : (0 : ℝ) < 1)
    have heq : (fun j => (∑' d : ℕ, C.coefficient j d / (d : ℝ)) /
        (coverThreshold 1 j ^ C.exponent j) / ((2 : ℝ) ^ C.exponent j - 1)) =
        coverScaledCost C 1 := by
      funext j
      unfold coverScaledCost coverScale PositiveCoverData.cost coverBase
      rw [Real.rpow_neg (coverThreshold_pos (by norm_num : (0 : ℝ) < 1) j).le]
      simp only [div_eq_mul_inv]
      ring
    rw [heq]
    exact hs

/-- Restriction changes only the coverage field, not any analytic budget. -/
def LogBudgetCover.restrict {A B : Set ℕ} (C : LogBudgetCover A) (hBA : B ⊆ A) :
    LogBudgetCover B :=
  { C with covers := fun b hb => C.covers b (hBA hb) }

/-- The general no-cover conclusion excludes the paper's concrete cover class. -/
theorem not_hasStrengthenedPositiveCover_of_isEmpty (A : Set ℕ)
    (hA : IsEmpty (LogBudgetCover A)) : ¬ HasStrengthenedPositiveCover A := by
  rintro ⟨C, hAC, hC⟩
  letI : IsEmpty (LogBudgetCover A) := hA
  exact isEmptyElim (logBudgetCover_of_strengthened C hC A hAC)

/-- A superset of a no-cover support cannot admit any finite-cost cover. -/
theorem no_logBudgetCover_of_subset {A B : Set ℕ} (hAB : A ⊆ B)
    (hA : IsEmpty (LogBudgetCover A)) : IsEmpty (LogBudgetCover B) := by
  refine ⟨fun C => ?_⟩
  letI : IsEmpty (LogBudgetCover A) := hA
  exact isEmptyElim (C.restrict hAB)

end ErdosProblems.Erdos257.PaperCompleteR8
end
