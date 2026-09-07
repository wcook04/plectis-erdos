import ErdosProblems.Erdos257.SelectedAncestryBudget

/-!
# Erdős #257: selected-ancestry tail survival

The sharp selected-ancestry conjecture `B_n > 0` is sufficient for the
rational-half construction, but it is stronger than the actual achievement-
set boundary.  This module records the exact weaker coordinate.

Let `E_n` be the positive correction in the complete Mersenne tail,

`E_n = mersenneTail n - 2^-n`,

and put `C_n = B_n + E_n`.  The budget/remainder conjugacy gives

`C_n = mersenneTail n - greedyRemainder(1/2,n)`.

Thus `C_n` is the literal surviving mass.  It is unchanged on a take and
loses exactly the skipped Mersenne coin on a skip.  Irrationality of every
complete Mersenne tail excludes the boundary case `C_n = 0`, so exact
half-membership is equivalent to `C_n > 0` at every depth, or equivalently

`B_n > -E_n`.

This is strictly weaker than `B_n > 0`.  The module changes the open producer;
it does not prove tail survival and does not settle Erdős #257.
-/

namespace ErdosProblems.Erdos257

open Set
open Erdos257PeriodNoncollapse

/-- Real form of the exact rational budget/remainder conjugacy. -/
theorem halfSelectedAncestryBudget_cast_eq_dyadic_sub_remainder
    (n : ℕ) :
    (halfSelectedAncestryBudgetRat n : ℝ) =
      ((1 : ℝ) / 2) ^ n -
        greedyMersenneRemainder (1 / 2 : ℝ) n := by
  have hbudgetQ :=
    halfGreedyRemainderRat_eq_dyadic_sub_selectedAncestryBudget n
  have hbudgetR :
      ((greedyMersenneRemainderRat (1 / 2 : ℚ) n : ℚ) : ℝ) =
        ((halfDyadicWeightRat n -
          halfSelectedAncestryBudgetRat n : ℚ) : ℝ) := by
    exact_mod_cast hbudgetQ
  rw [cast_greedyMersenneRemainderRat] at hbudgetR
  simp only [halfDyadicWeightRat, Rat.cast_sub, Rat.cast_div,
    Rat.cast_one, Rat.cast_pow, Rat.cast_ofNat] at hbudgetR
  have hdyadic : ((1 : ℝ) / 2) ^ n = 1 / (2 : ℝ) ^ n := by
    simp
  rw [hdyadic]
  linarith

/-- Every complete Mersenne tail is irrational.  Removing a finite rational
prefix from the Erdős--Borwein constant cannot make it rational. -/
theorem mersenneTail_ne_ratCast (n : ℕ) (q : ℚ) :
    mersenneTail n ≠ (q : ℝ) := by
  intro htail
  have hprefix : mersennePrefixMass n =
      ((∑ k ∈ Finset.range n, mersenneWeightRat (k + 1) : ℚ) : ℝ) := by
    unfold mersennePrefixMass
    push_cast
    exact Finset.sum_congr rfl fun k _ =>
      (cast_mersenneWeightRat (k + 1)).symm
  apply irrational_erdosBorweinMersenneConstant.ne_rat
    ((∑ k ∈ Finset.range n, mersenneWeightRat (k + 1)) + q)
  rw [erdosBorweinMersenneConstant_eq_prefix_add_tail n, htail, hprefix]
  push_cast
  rfl

/-- The rational ancestry budget can never land exactly on the negative
irrational correction tail. -/
theorem halfSelectedAncestryBudget_ne_neg_correctionTail (n : ℕ) :
    (halfSelectedAncestryBudgetRat n : ℝ) ≠
      -mersenneCorrectionTail n := by
  intro heq
  apply mersenneTail_ne_ratCast n
    (halfDyadicWeightRat n - halfSelectedAncestryBudgetRat n)
  have hdyadic : (halfDyadicWeightRat n : ℝ) = ((1 : ℝ) / 2) ^ n := by
    simp [halfDyadicWeightRat]
  unfold mersenneCorrectionTail at heq
  push_cast
  rw [hdyadic]
  linarith

/-- Exact weak survival boundary in ancestry coordinates.  The weak
remainder inequality becomes strict on the budget side because equality
would make a complete Mersenne tail rational. -/
theorem halfGreedy_survives_iff_selectedAncestryBudget_gt_neg_correctionTail
    (n : ℕ) :
    greedyMersenneRemainder (1 / 2 : ℝ) n ≤ mersenneTail n ↔
      -mersenneCorrectionTail n <
        (halfSelectedAncestryBudgetRat n : ℝ) := by
  have hbudget :=
    halfSelectedAncestryBudget_cast_eq_dyadic_sub_remainder n
  have hne := halfSelectedAncestryBudget_ne_neg_correctionTail n
  unfold mersenneCorrectionTail
  constructor
  · intro hsurvive
    have hle : -(mersenneTail n - ((1 : ℝ) / 2) ^ n) ≤
        (halfSelectedAncestryBudgetRat n : ℝ) := by
      linarith
    exact lt_of_le_of_ne hle (Ne.symm hne)
  · intro hbudgetLower
    linarith

/-- The complement budget is the ancestry budget enlarged by the entire
unresolved correction tail. -/
noncomputable def halfSelectedAncestryComplementBudget (n : ℕ) : ℝ :=
  (halfSelectedAncestryBudgetRat n : ℝ) + mersenneCorrectionTail n

/-- The complement budget is exactly the complete future mass minus the
actual greedy remainder. -/
theorem halfSelectedAncestryComplementBudget_eq_tail_sub_remainder
    (n : ℕ) :
    halfSelectedAncestryComplementBudget n =
      mersenneTail n - greedyMersenneRemainder (1 / 2 : ℝ) n := by
  rw [halfSelectedAncestryComplementBudget,
    halfSelectedAncestryBudget_cast_eq_dyadic_sub_remainder]
  unfold mersenneCorrectionTail
  ring

/-- All-scale deterministic law: a take transports the complement budget
unchanged, while a skip spends exactly the omitted Mersenne coin. -/
theorem halfSelectedAncestryComplementBudget_succ (n : ℕ) :
    halfSelectedAncestryComplementBudget (n + 1) =
      if mersenneWeight (n + 1) ≤
          greedyMersenneRemainder (1 / 2 : ℝ) n then
        halfSelectedAncestryComplementBudget n
      else
        halfSelectedAncestryComplementBudget n -
          mersenneWeight (n + 1) := by
  have htail := mersenneTail_eq_weight_add n
  rw [halfSelectedAncestryComplementBudget_eq_tail_sub_remainder,
    greedyMersenneRemainder_succ,
    halfSelectedAncestryComplementBudget_eq_tail_sub_remainder]
  by_cases htake : mersenneWeight (n + 1) ≤
      greedyMersenneRemainder (1 / 2 : ℝ) n
  · rw [if_pos htake, if_pos htake]
    linarith
  · rw [if_neg htake, if_neg htake]
    linarith

/-- The weakest exact selected-ancestry producer exposed by this coordinate:
the complement budget remains strictly positive at every depth. -/
def HalfSelectedAncestryTailSurvival : Prop :=
  ∀ n : ℕ, 0 < halfSelectedAncestryComplementBudget n

/-- The selected-ancestry tail-survival condition is not merely sufficient:
it is exactly the rational-half membership problem. -/
theorem half_mem_mersenneAchievementSet_iff_selectedAncestryTailSurvival :
    (1 / 2 : ℝ) ∈ mersenneAchievementSet ↔
      HalfSelectedAncestryTailSurvival := by
  rw [mem_mersenneAchievementSet_iff_greedy_survival]
  simp only [show (0 : ℝ) ≤ 1 / 2 by norm_num, true_and]
  change (∀ n : ℕ,
      greedyMersenneRemainder (1 / 2 : ℝ) n ≤ mersenneTail n) ↔
    ∀ n : ℕ, 0 < halfSelectedAncestryComplementBudget n
  apply forall_congr'
  intro n
  rw [halfSelectedAncestryComplementBudget_eq_tail_sub_remainder]
  have hne := halfSelectedAncestryBudget_ne_neg_correctionTail n
  have hbudget :=
    halfSelectedAncestryBudget_cast_eq_dyadic_sub_remainder n
  unfold mersenneCorrectionTail at hne
  constructor
  · intro hsurvive
    have hnonneg : 0 ≤ mersenneTail n -
        greedyMersenneRemainder (1 / 2 : ℝ) n := by linarith
    apply lt_of_le_of_ne hnonneg
    intro hzero
    apply hne
    linarith
  · intro hpos
    linarith

/-- Equivalent direct producer statement in the original ancestry budget. -/
theorem half_mem_mersenneAchievementSet_iff_budget_gt_neg_correctionTail :
    (1 / 2 : ℝ) ∈ mersenneAchievementSet ↔
      ∀ n : ℕ,
        -mersenneCorrectionTail n <
          (halfSelectedAncestryBudgetRat n : ℝ) := by
  rw [mem_mersenneAchievementSet_iff_greedy_survival]
  simp only [show (0 : ℝ) ≤ 1 / 2 by norm_num, true_and]
  apply forall_congr'
  exact halfGreedy_survives_iff_selectedAncestryBudget_gt_neg_correctionTail

/-- A cofinal supply of first negative budget crossings is a direct producer
for the exact tail-survival interface.  The cofinal premise remains explicit;
this consumer does not prove that supply for the actual orbit. -/
theorem halfSelectedAncestryTailSurvival_of_cofinal_first_negative_crossings
    (hcross : ∀ K : ℕ, ∃ n : ℕ,
      K ≤ n ∧
      0 ≤ halfSelectedAncestryBudgetRat n ∧
      halfSelectedAncestryBudgetRat (n + 1) < 0) :
    HalfSelectedAncestryTailSurvival := by
  exact
    (half_mem_mersenneAchievementSet_iff_selectedAncestryTailSurvival).mp
      (half_mem_mersenneAchievementSet_of_cofinal_first_negative_crossings hcross)

#print axioms halfSelectedAncestryBudget_cast_eq_dyadic_sub_remainder
#print axioms mersenneTail_ne_ratCast
#print axioms halfSelectedAncestryBudget_ne_neg_correctionTail
#print axioms halfGreedy_survives_iff_selectedAncestryBudget_gt_neg_correctionTail
#print axioms halfSelectedAncestryComplementBudget_succ
#print axioms half_mem_mersenneAchievementSet_iff_selectedAncestryTailSurvival
#print axioms half_mem_mersenneAchievementSet_iff_budget_gt_neg_correctionTail
#print axioms halfSelectedAncestryTailSurvival_of_cofinal_first_negative_crossings

end ErdosProblems.Erdos257
