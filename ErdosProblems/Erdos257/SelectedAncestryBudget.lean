import Erdos257PeriodNoncollapse.GreedyTrapDynamics

/-!
# Erdős #257: the selected-ancestry budget at the rational half

For the greedy orbit pinned at `1/2`, split every Mersenne weight into its
binary skeleton and positive correction

`1 / (2^n - 1) = 2^-n + e_n`.

The budget `B_n` below starts at `B_0 = 1/2`; a taken rank deposits `e_n`,
while a skipped rank spends `2^-n`.  The exact identity

`r_n = 2^-n - B_n`

conjugates the half-greedy residual to this selected-ancestry account.  Thus
the sharpened phase ceiling `2^n r_n < 1` is exactly `B_n > 0`.  A first
negative crossing can occur only on a skip, and lands in the narrow interval
`(-e_n,0)`.

The final section packages a deliberately stronger remaining producer:
one skip in every sufficiently late dyadic block `(N,2N]`.  Such a supply
immediately gives infinitely many skipped ranks and hence a rational-half
counterexample.  This module does not prove that producer and does not settle
Erdős #257.
-/

namespace ErdosProblems.Erdos257

open Erdos257PeriodNoncollapse
open Set

/-- The exact binary skeleton `2^-n`, kept rational. -/
def halfDyadicWeightRat (n : ℕ) : ℚ :=
  1 / (2 : ℚ) ^ n

/-- The positive excess of the `n`th Mersenne weight over its binary
skeleton. -/
def mersenneCorrectionRat (n : ℕ) : ℚ :=
  mersenneWeightRat n - halfDyadicWeightRat n

/-- The selected-ancestry budget for the rational half-greedy orbit.

At a take the Mersenne correction is deposited.  At a skip the unused binary
digit is spent.  The apparently exceptional initial value makes the same
recursion valid at rank one: rank one is skipped and `B_1 = 0`. -/
def halfSelectedAncestryBudgetRat : ℕ → ℚ
  | 0 => 1 / 2
  | n + 1 =>
      if mersenneWeightRat (n + 1) ≤
          greedyMersenneRemainderRat (1 / 2 : ℚ) n then
        halfSelectedAncestryBudgetRat n + mersenneCorrectionRat (n + 1)
      else
        halfSelectedAncestryBudgetRat n - halfDyadicWeightRat (n + 1)

@[simp] theorem halfDyadicWeightRat_zero : halfDyadicWeightRat 0 = 1 := by
  norm_num [halfDyadicWeightRat]

/-- Adjacent binary skeletons differ by the exact factor two. -/
theorem halfDyadicWeightRat_eq_two_mul_succ (n : ℕ) :
    halfDyadicWeightRat n = 2 * halfDyadicWeightRat (n + 1) := by
  unfold halfDyadicWeightRat
  rw [pow_succ]
  have hpow : (2 : ℚ) ^ n ≠ 0 := by positivity
  field_simp [hpow]

/-- Reassemble a Mersenne weight from its binary digit and correction. -/
theorem mersenneWeightRat_eq_dyadic_add_correction (n : ℕ) :
    mersenneWeightRat n =
      halfDyadicWeightRat n + mersenneCorrectionRat n := by
  simp only [mersenneCorrectionRat]
  ring

/-- Every positive-rank correction is strictly positive. -/
theorem mersenneCorrectionRat_pos {n : ℕ} (hn : 0 < n) :
    0 < mersenneCorrectionRat n := by
  have hpow : (0 : ℚ) < (2 : ℚ) ^ n := by positivity
  have hone : (1 : ℚ) < (2 : ℚ) ^ n :=
    one_lt_pow₀ (by norm_num) hn.ne'
  have hden : (0 : ℚ) < (2 : ℚ) ^ n - 1 := by linarith
  have hlt : (2 : ℚ) ^ n - 1 < (2 : ℚ) ^ n := by linarith
  rw [mersenneCorrectionRat, sub_pos]
  unfold mersenneWeightRat halfDyadicWeightRat
  exact one_div_lt_one_div_of_lt hden hlt

/-- Exact budget/remainder conjugacy at every scale. -/
theorem halfGreedyRemainderRat_eq_dyadic_sub_selectedAncestryBudget
    (n : ℕ) :
    greedyMersenneRemainderRat (1 / 2 : ℚ) n =
      halfDyadicWeightRat n - halfSelectedAncestryBudgetRat n := by
  induction n with
  | zero => norm_num [halfDyadicWeightRat, halfSelectedAncestryBudgetRat]
  | succ n ih =>
      rw [greedyMersenneRemainderRat_succ]
      unfold halfSelectedAncestryBudgetRat
      by_cases htake :
          mersenneWeightRat (n + 1) ≤
            greedyMersenneRemainderRat (1 / 2 : ℚ) n
      · rw [if_pos htake, if_pos htake, ih,
          mersenneWeightRat_eq_dyadic_add_correction,
          halfDyadicWeightRat_eq_two_mul_succ]
        ring
      · rw [if_neg htake, if_neg htake, ih,
          halfDyadicWeightRat_eq_two_mul_succ]
        ring

/-- The greedy decision itself in budget coordinates. -/
theorem halfGreedy_take_iff_selectedAncestryBudget_le
    (n : ℕ) :
    mersenneWeightRat (n + 1) ≤
        greedyMersenneRemainderRat (1 / 2 : ℚ) n ↔
      halfSelectedAncestryBudgetRat n ≤
        halfDyadicWeightRat (n + 1) - mersenneCorrectionRat (n + 1) := by
  have hdyadic := halfDyadicWeightRat_eq_two_mul_succ n
  rw [halfGreedyRemainderRat_eq_dyadic_sub_selectedAncestryBudget,
    mersenneWeightRat_eq_dyadic_add_correction]
  constructor <;> intro h <;> linarith

/-- Definitional take/skip update, exposed without unfolding recursive
occurrences of the budget. -/
theorem halfSelectedAncestryBudgetRat_succ_raw (n : ℕ) :
    halfSelectedAncestryBudgetRat (n + 1) =
      if mersenneWeightRat (n + 1) ≤
          greedyMersenneRemainderRat (1 / 2 : ℚ) n then
        halfSelectedAncestryBudgetRat n + mersenneCorrectionRat (n + 1)
      else
        halfSelectedAncestryBudgetRat n - halfDyadicWeightRat (n + 1) :=
  rfl

/-- Budget-only form of the selected-ancestry recurrence. -/
theorem halfSelectedAncestryBudgetRat_succ (n : ℕ) :
    halfSelectedAncestryBudgetRat (n + 1) =
      if halfSelectedAncestryBudgetRat n ≤
          halfDyadicWeightRat (n + 1) - mersenneCorrectionRat (n + 1) then
        halfSelectedAncestryBudgetRat n + mersenneCorrectionRat (n + 1)
      else
        halfSelectedAncestryBudgetRat n - halfDyadicWeightRat (n + 1) := by
  rw [halfSelectedAncestryBudgetRat_succ_raw]
  by_cases htake : mersenneWeightRat (n + 1) ≤
      greedyMersenneRemainderRat (1 / 2 : ℚ) n
  · rw [if_pos htake,
      if_pos ((halfGreedy_take_iff_selectedAncestryBudget_le n).1 htake)]
  · have hbudget : ¬ halfSelectedAncestryBudgetRat n ≤
        halfDyadicWeightRat (n + 1) - mersenneCorrectionRat (n + 1) := by
      intro h
      exact htake ((halfGreedy_take_iff_selectedAncestryBudget_le n).2 h)
    rw [if_neg htake, if_neg hbudget]

/-- The scaled half-greedy phase is exactly one minus the scaled ancestry
budget. -/
theorem halfGreedy_scaledRat_eq_one_sub_selectedAncestryBudget (n : ℕ) :
    (2 : ℚ) ^ n * greedyMersenneRemainderRat (1 / 2 : ℚ) n =
      1 - (2 : ℚ) ^ n * halfSelectedAncestryBudgetRat n := by
  rw [halfGreedyRemainderRat_eq_dyadic_sub_selectedAncestryBudget]
  have hpow : (2 : ℚ) ^ n ≠ 0 := by positivity
  unfold halfDyadicWeightRat
  field_simp [hpow]

/-- The sharp phase ceiling is precisely positivity of the ancestry budget. -/
theorem halfGreedy_scaledRat_lt_one_iff_budget_pos (n : ℕ) :
    (2 : ℚ) ^ n * greedyMersenneRemainderRat (1 / 2 : ℚ) n < 1 ↔
      0 < halfSelectedAncestryBudgetRat n := by
  rw [halfGreedy_scaledRat_eq_one_sub_selectedAncestryBudget]
  have hpow : (0 : ℚ) < (2 : ℚ) ^ n := by positivity
  constructor <;> intro h <;> nlinarith

/-- A first negative budget crossing cannot be a take.  It is a skip landing
strictly between `-e_(n+1)` and zero. -/
theorem halfSelectedAncestryBudgetRat_first_negative_crossing
    {n : ℕ}
    (hnonneg : 0 ≤ halfSelectedAncestryBudgetRat n)
    (hneg : halfSelectedAncestryBudgetRat (n + 1) < 0) :
    ¬ mersenneWeightRat (n + 1) ≤
        greedyMersenneRemainderRat (1 / 2 : ℚ) n ∧
      -mersenneCorrectionRat (n + 1) <
        halfSelectedAncestryBudgetRat (n + 1) ∧
      halfSelectedAncestryBudgetRat (n + 1) =
        halfSelectedAncestryBudgetRat n - halfDyadicWeightRat (n + 1) := by
  have hcorr : 0 < mersenneCorrectionRat (n + 1) :=
    mersenneCorrectionRat_pos (by omega)
  have hskip : ¬ mersenneWeightRat (n + 1) ≤
      greedyMersenneRemainderRat (1 / 2 : ℚ) n := by
    intro htake
    have hstep := halfSelectedAncestryBudgetRat_succ_raw n
    rw [if_pos htake] at hstep
    rw [hstep] at hneg
    linarith
  have hupdate : halfSelectedAncestryBudgetRat (n + 1) =
      halfSelectedAncestryBudgetRat n - halfDyadicWeightRat (n + 1) := by
    rw [halfSelectedAncestryBudgetRat_succ_raw, if_neg hskip]
  have hthreshold :
      halfDyadicWeightRat (n + 1) - mersenneCorrectionRat (n + 1) <
        halfSelectedAncestryBudgetRat n := by
    by_contra hnot
    have hle : halfSelectedAncestryBudgetRat n ≤
        halfDyadicWeightRat (n + 1) - mersenneCorrectionRat (n + 1) :=
      le_of_not_gt hnot
    exact hskip ((halfGreedy_take_iff_selectedAncestryBudget_le n).2 hle)
  refine ⟨hskip, ?_, hupdate⟩
  rw [hupdate]
  linarith

/- A budget crossing is an actual support witness, not merely a rational
   inequality.  This is the bridge consumed by achievement-set arguments. -/
theorem halfSelectedAncestryBudgetRat_first_negative_crossing_mem_skippedSupport
    {n : ℕ}
    (hnonneg : 0 ≤ halfSelectedAncestryBudgetRat n)
    (hneg : halfSelectedAncestryBudgetRat (n + 1) < 0) :
    n + 1 ∈ greedyMersenneSkippedSupport (1 / 2 : ℝ) := by
  rw [succ_mem_greedyMersenneSkippedSupport_iff]
  intro htake
  apply (halfSelectedAncestryBudgetRat_first_negative_crossing hnonneg hneg).1
  have htake' :
      ((mersenneWeightRat (n + 1) : ℚ) : ℝ) ≤
        ((greedyMersenneRemainderRat (1 / 2 : ℚ) n : ℚ) : ℝ) := by
    simpa only [cast_mersenneWeightRat, cast_greedyMersenneRemainderRat,
      Rat.cast_div, Rat.cast_one, Rat.cast_ofNat] using htake
  exact_mod_cast htake'

/- Cofinal first crossings are already enough for the exact endpoint.  The
   cofinal-crossing premise stays explicit: this theorem does not prove it. -/
theorem half_mem_mersenneAchievementSet_of_cofinal_first_negative_crossings
    (hcross : ∀ K : ℕ, ∃ n : ℕ,
      K ≤ n ∧
      0 ≤ halfSelectedAncestryBudgetRat n ∧
      halfSelectedAncestryBudgetRat (n + 1) < 0) :
    (1 / 2 : ℝ) ∈ mersenneAchievementSet := by
  rw [half_mem_mersenneAchievementSet_iff_greedySkippedSupport_infinite]
  apply Set.infinite_iff_exists_gt.mpr
  intro K
  obtain ⟨n, hnK, hnonneg, hneg⟩ := hcross K
  refine ⟨n + 1,
    halfSelectedAncestryBudgetRat_first_negative_crossing_mem_skippedSupport
      hnonneg hneg, ?_⟩
  exact lt_of_le_of_lt hnK (Nat.lt_succ_self n)

/-- A skip occurs somewhere in the dyadic block `(N,2N]`. -/
def HalfDyadicBlockHasSkip (N : ℕ) : Prop :=
  ∃ m : ℕ, N < m ∧ m ≤ 2 * N ∧
    m ∈ greedyMersenneSkippedSupport (1 / 2 : ℝ)

/-- The deliberately stronger open producer tested by the selected-ancestry
audit. -/
def EventuallyHalfDyadicBlockHasSkip : Prop :=
  ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N → 2 ≤ N → HalfDyadicBlockHasSkip N

/-- One skipped rank in every sufficiently late dyadic block already forces
the exact half into the Mersenne achievement set. -/
theorem half_mem_mersenneAchievementSet_of_eventually_dyadicBlockHasSkip
    (hblocks : EventuallyHalfDyadicBlockHasSkip) :
    (1 / 2 : ℝ) ∈ mersenneAchievementSet := by
  rw [half_mem_mersenneAchievementSet_iff_greedySkippedSupport_infinite]
  apply Set.infinite_iff_exists_gt.mpr
  intro K
  obtain ⟨N₀, hN₀⟩ := hblocks
  let N := max (max K N₀) 2
  obtain ⟨m, hNm, _, hskip⟩ := hN₀ N (by simp [N]) (by simp [N])
  refine ⟨m, hskip, ?_⟩
  exact lt_of_le_of_lt (by simp [N]) hNm

#print axioms halfGreedyRemainderRat_eq_dyadic_sub_selectedAncestryBudget
#print axioms halfSelectedAncestryBudgetRat_first_negative_crossing
#print axioms halfSelectedAncestryBudgetRat_first_negative_crossing_mem_skippedSupport
#print axioms half_mem_mersenneAchievementSet_of_cofinal_first_negative_crossings
#print axioms half_mem_mersenneAchievementSet_of_eventually_dyadicBlockHasSkip

end ErdosProblems.Erdos257
