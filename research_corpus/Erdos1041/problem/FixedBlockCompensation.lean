import Mathlib

/-!
# Erdős 1041: fixed-block compensation kernel

This file checks the finite allocation step used by the fixed-block monodromy
consumer.  A whole-fibre length budget selects a moved sheet once the fixed
sheets pay their baseline cost.  The analytic construction of such a loop and
its geometric length estimates remain outside this scalar kernel.
-/

namespace ErdosProblems.Erdos1041

/-- If the total moved mass is at most `C` times the number of moved sheets,
then one moved sheet has mass at most `C`. -/
theorem exists_moved_le_of_sum_le_card_mul
    {α : Type*} [DecidableEq α]
    (M : Finset α) (hM : M.Nonempty) (L : α → ℝ) (C : ℝ)
    (hsum : ∑ i ∈ M, L i ≤ M.card * C) :
    ∃ i ∈ M, L i ≤ C := by
  by_contra h
  push_neg at h
  have hstrict : ∑ i ∈ M, C < ∑ i ∈ M, L i := by
    exact Finset.sum_lt_sum_of_nonempty hM (fun i hi => h i hi)
  simp only [Finset.sum_const, nsmul_eq_mul] at hstrict
  exact (not_lt_of_ge hsum) hstrict

/-- Subtracting the fixed-sheet baseline from the whole-fibre budget leaves
the same baseline budget on the moved block.  This is the exact compensation
identity behind the monodromy allocation step. -/
theorem moved_sum_le_of_whole_budget_and_fixed_baseline
    (movedCard fixedCard : ℕ) (movedSum fixedSum C : ℝ)
    (hwhole : movedSum + fixedSum ≤ (movedCard + fixedCard) * C)
    (hfixed : fixedCard * C ≤ fixedSum) :
    movedSum ≤ movedCard * C := by
  norm_num at hwhole hfixed ⊢
  linarith

/-- Without assuming that the fixed sheets pay the full baseline, the exact
unpaid fixed-sheet slack is the only loss in the moved-block budget. -/
theorem moved_sum_le_baseline_add_fixed_slack
    (movedCard fixedCard : ℕ) (movedSum fixedSum C : ℝ)
    (hwhole : movedSum + fixedSum ≤ (movedCard + fixedCard) * C) :
    movedSum ≤ movedCard * C + (fixedCard * C - fixedSum) := by
  norm_num at hwhole ⊢
  linarith

/-- A strict margin in the whole-fibre budget pays the fixed-sheet slack
before the moved block incurs any loss.  Thus `margin > fixedSlack` is the
exact scalar interface needed for a strict moved-sheet conclusion. -/
theorem moved_sum_le_baseline_add_fixed_slack_sub_margin
    (movedCard fixedCard : ℕ) (movedSum fixedSum C margin : ℝ)
    (hwhole : movedSum + fixedSum ≤ (movedCard + fixedCard) * C - margin) :
    movedSum ≤ movedCard * C + (fixedCard * C - fixedSum) - margin := by
  norm_num at hwhole ⊢
  linarith

/-- A whole-fibre average bound together with a fixed-sheet baseline selects
an entire moved lift.  In the geometric consumer that lift joins distinct
roots because its sheet is moved by monodromy. -/
theorem exists_moved_le_of_whole_budget_and_fixed_baseline
    {α : Type*} [DecidableEq α]
    (M : Finset α) (hM : M.Nonempty) (L : α → ℝ)
    (fixedCard : ℕ) (fixedSum C : ℝ)
    (hwhole : (∑ i ∈ M, L i) + fixedSum ≤ (M.card + fixedCard) * C)
    (hfixed : fixedCard * C ≤ fixedSum) :
    ∃ i ∈ M, L i ≤ C := by
  apply exists_moved_le_of_sum_le_card_mul M hM L C
  exact moved_sum_le_of_whole_budget_and_fixed_baseline
    M.card fixedCard (∑ i ∈ M, L i) fixedSum C hwhole hfixed

/-- The three-sheet countermodel is sharp: two moved lifts can both exceed
`C` while a shorter fixed lift absorbs exactly the whole-fibre budget. -/
theorem three_sheet_fixed_absorption
    (C δ : ℝ) :
    (C + δ) + (C + δ) + (C - 2 * δ) = 3 * C := by
  ring

end ErdosProblems.Erdos1041
