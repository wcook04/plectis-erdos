import Erdos249257.HalfCylinderUpperResetBandCertificates
import Erdos249257.HalfCylinderIntegerGreedy

/-!
Paper-form restatements of two environments of the long Erdős #257 manuscript
`paper/reasoning-parts/erdos257/a257_front.tex`:

* `record:257bm-i14` (line 5002), "A finite band check for `13 ≤ d ≤ 30`";
* `record:257bm-i15` (line 5021), "A general perturbed greedy recurrence".

Every quantity is the paper's.  The reset charge at an actual upper reset is
`4 * overshoot + abovePulse`; the successor remainder at row `d + 1` is
`seamIntegerGreedyRemainder (d + 1)`.  For the abstract recurrence the old
integer values are `oldSum`, the perturbations are `pulse` with cap `B =
pulseCap`, the separation is `g = gap`, the update is `t(x) = 4 s(x) + p(x)`,
the new capacity is `4C + g`, and the extra weight is `W = 2g + 4`.
-/

namespace ErdosProblems.Erdos257.PaperCompleteR21

open Erdos249257 Erdos249257.HalfCylinderIntegerGreedy

/-! ## `record:257bm-i14`: the finite band check for `13 ≤ d ≤ 30` -/

/-- Long `record:257bm-i14`, first clause.  For every actual upper-reset index
`13 ≤ d ≤ 30` (an upper reset is `successorCarries`) and every `0 ≤ j ≤ d`,
either `2^{d-j+1}` is strictly below the reset charge, or the reset charge plus
the linear width `2(d+j)` is at most `2^{d-j+1}`. -/
theorem paper_finite_band_check_thirteen_to_thirty
    (d : ℕ) (hd13 : 13 ≤ d) (hd30 : d ≤ 30) (hd5 : 5 ≤ d)
    (hcarry : (seamAdjacentCut d hd5).successorCarries) :
    ∀ j : ℕ, j ≤ d →
      2 ^ (d - j + 1) <
          4 * (seamAdjacentCut d hd5).overshoot +
            (seamAdjacentCut d hd5).abovePulse ∨
        4 * (seamAdjacentCut d hd5).overshoot +
              (seamAdjacentCut d hd5).abovePulse + 2 * (d + j) ≤
          2 ^ (d - j + 1) :=
  seamUpperResetDyadicBandEscape_through_thirty d hd13 hd30 hd5 hcarry

/-- Long `record:257bm-i14`, second clause: the successor remainder at each row
`d + 1` for `13 ≤ d ≤ 30`, from `rem(14) = 392` through
`rem(31) = 4187487147`. -/
theorem paper_successor_remainders_fourteen_through_thirtyone :
    seamIntegerGreedyRemainder 14 = 392 ∧
      seamIntegerGreedyRemainder 15 = 34333 ∧
      seamIntegerGreedyRemainder 16 = 71791 ∧
      seamIntegerGreedyRemainder 17 = 156085 ∧
      seamIntegerGreedyRemainder 18 = 362187 ∧
      seamIntegerGreedyRemainder 19 = 924455 ∧
      seamIntegerGreedyRemainder 20 = 549353 ∧
      seamIntegerGreedyRemainder 21 = 100251 ∧
      seamIntegerGreedyRemainder 22 = 4595307 ∧
      seamIntegerGreedyRemainder 23 = 9992613 ∧
      seamIntegerGreedyRemainder 24 = 23193229 ∧
      seamIntegerGreedyRemainder 25 = 59218477 ∧
      seamIntegerGreedyRemainder 26 = 35546625 ∧
      seamIntegerGreedyRemainder 27 = 7968765 ∧
      seamIntegerGreedyRemainder 28 = 300310513 ∧
      seamIntegerGreedyRemainder 29 = 664371133 ∧
      seamIntegerGreedyRemainder 30 = 1583742700 ∧
      seamIntegerGreedyRemainder 31 = 4187487147 := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_,
    ?_⟩ <;> decide +kernel

/-- Long `record:257bm-i14`, third clause, in its exact conditional form: the
finite range is not the universal condition.  What the universal condition
would give is recorded here, so that the gap between the certified band
`13 ≤ d ≤ 30` and the hypothesis `∀ d ≥ 13` is explicit. -/
theorem paper_universal_band_condition_would_close_half
    (hband : SeamUpperResetDyadicBandEscape) :
    (1 / 2 : ℝ) ∈ mersenneAchievementSet :=
  half_mem_mersenneAchievementSet_of_upperResetDyadicBandEscape hband

/-- The universal hypothesis spelled out, for comparison with the finite band
check above: the same disjunction at every `d ≥ 13`, not only `d ≤ 30`. -/
theorem paper_universal_band_condition_unfolded :
    SeamUpperResetDyadicBandEscape ↔
      ∀ (d : ℕ) (hd5 : 5 ≤ d), 13 ≤ d →
        (seamAdjacentCut d hd5).successorCarries →
          ∀ j : ℕ, j ≤ d →
            2 ^ (d - j + 1) <
                4 * (seamAdjacentCut d hd5).overshoot +
                  (seamAdjacentCut d hd5).abovePulse ∨
              4 * (seamAdjacentCut d hd5).overshoot +
                    (seamAdjacentCut d hd5).abovePulse + 2 * (d + j) ≤
                2 ^ (d - j + 1) :=
  Iff.rfl

/-! ## `record:257bm-i15`: the general perturbed greedy recurrence -/

variable {α : Type*}

/-- Long `record:257bm-i15`, order preservation.  The structure hypothesis
`B < 3g` alone preserves the order of the updated values `t(x) = 4 s(x) + p(x)`.
-/
theorem paper_perturbed_order_preservation (F : PerturbedFamily α)
    {x y : α} (hxy : F.oldSum x < F.oldSum y) :
    F.newSum x < F.newSum y :=
  F.newSum_strictMono hxy

/-- Long `record:257bm-i15`, maximality clause with the additional hypothesis
`B < g`.  At the new capacity `C' = 4C + g` the selected updated value is
`t(x₊)` when `4o + p₊ ≤ g` and `t(x₋)` otherwise; it is admissible, and it is
the largest admissible updated value. -/
theorem paper_perturbed_prefixChoice_maximal (F : PerturbedFamily α) {C : ℕ}
    (K : F.AdjacentCut C) [Decidable K.successorCarries]
    (hcap : F.pulseCap < F.gap) :
    K.newCapacity = 4 * C + F.gap ∧
      K.successorCarries = (4 * K.overshoot + K.abovePulse ≤ F.gap) ∧
      K.prefixChoice = (if K.successorCarries then K.above else K.below) ∧
      F.newSum K.prefixChoice ≤ K.newCapacity ∧
      ∀ x : α, F.newSum x ≤ K.newCapacity →
        F.newSum x ≤ F.newSum K.prefixChoice := by
  refine ⟨rfl, rfl, rfl, ?_, fun x hx => K.prefixChoice_maximal hcap hx⟩
  by_cases hcarry : K.successorCarries
  · rw [PerturbedFamily.AdjacentCut.prefixChoice, if_pos hcarry]
    exact (K.above_newSum_le_capacity_iff).2 hcarry
  · rw [PerturbedFamily.AdjacentCut.prefixChoice, if_neg hcarry]
    exact K.below_newSum_le_capacity hcap

/-- Long `record:257bm-i15`, the exact three-branch remainder after testing the
extra weight `W = 2g + 4` by the take-if-possible rule. -/
theorem paper_perturbed_nextRemainder_three_branches (F : PerturbedFamily α)
    {C : ℕ} (K : F.AdjacentCut C) [Decidable K.successorCarries] :
    K.terminalWeight = 2 * F.gap + 4 ∧
      K.nextRemainder =
        if K.successorCarries then
          F.gap - (4 * K.overshoot + K.abovePulse)
        else if 4 * K.remainder + F.gap - K.belowPulse < K.terminalWeight then
          4 * K.remainder + F.gap - K.belowPulse
        else
          4 * K.remainder - F.gap - K.belowPulse - 4 :=
  ⟨rfl, K.nextRemainder_trichotomy⟩

/-- Long `record:257bm-i15`, the separation clause: under `4g - B ≥ W` every
earlier updated value plus the extra weight is at most the selected updated
value.  This is the extra hypothesis needed for a genuine maximum over both
choices of the extra weight, rather than the stated two-stage rule. -/
theorem paper_perturbed_separation_global_maximality (F : PerturbedFamily α)
    {C : ℕ} (K : F.AdjacentCut C) [Decidable K.successorCarries]
    (hsep : K.terminalWeight ≤ 4 * F.gap - F.pulseCap)
    {x : α} (hx : F.oldSum x < F.oldSum K.prefixChoice) :
    F.newSum x + K.terminalWeight ≤ F.newSum K.prefixChoice := by
  have h1 := F.separated hx
  have h2 := F.pulse_le x
  have h3 := F.pulseCap_lt_three_gap
  have hterm : K.terminalWeight = 2 * F.gap + 4 := rfl
  rw [hterm] at hsep ⊢
  unfold PerturbedFamily.newSum
  omega

/-- Long `record:257bm-i15`, the separation clause in the form the paper
states it: under `B < g` and `4g - B ≥ W` the two-stage rule really is the
maximum of `{t(x) + εW : x ∈ α, ε ∈ {0,1}}` below the new capacity.  The first
conjunct says the two-stage value is admissible; the next two say no
`ε = 0` and no `ε = 1` candidate beats it. -/
theorem paper_perturbed_two_stage_is_global_maximum (F : PerturbedFamily α)
    {C : ℕ} (K : F.AdjacentCut C) [Decidable K.successorCarries]
    (hcap : F.pulseCap < F.gap)
    (hsep : K.terminalWeight ≤ 4 * F.gap - F.pulseCap) :
    F.newSum K.prefixChoice +
          (if K.terminalWeight ≤ K.prefixRemainder then K.terminalWeight
            else 0) ≤ K.newCapacity ∧
      (∀ x : α, F.newSum x ≤ K.newCapacity →
        F.newSum x ≤
          F.newSum K.prefixChoice +
            (if K.terminalWeight ≤ K.prefixRemainder then K.terminalWeight
              else 0)) ∧
      (∀ x : α, F.newSum x + K.terminalWeight ≤ K.newCapacity →
        F.newSum x + K.terminalWeight ≤
          F.newSum K.prefixChoice +
            (if K.terminalWeight ≤ K.prefixRemainder then K.terminalWeight
              else 0)) := by
  have hadm : F.newSum K.prefixChoice ≤ K.newCapacity := by
    by_cases hcarry : K.successorCarries
    · rw [PerturbedFamily.AdjacentCut.prefixChoice, if_pos hcarry]
      exact (K.above_newSum_le_capacity_iff).2 hcarry
    · rw [PerturbedFamily.AdjacentCut.prefixChoice, if_neg hcarry]
      exact K.below_newSum_le_capacity hcap
  have hpr : K.prefixRemainder = K.newCapacity - F.newSum K.prefixChoice :=
    K.prefixRemainder_eq_capacity_sub_choice
  refine ⟨?_, ?_, ?_⟩
  · split_ifs with h <;> omega
  · intro x hx
    have hmax := K.prefixChoice_maximal hcap hx
    split_ifs with h <;> omega
  · intro x hx
    have hx' : F.newSum x ≤ K.newCapacity :=
      le_trans (Nat.le_add_right _ _) hx
    have hmax := K.prefixChoice_maximal hcap hx'
    rcases lt_trichotomy (F.oldSum x) (F.oldSum K.prefixChoice) with
      hlt | heq | hgt
    · have hgap := paper_perturbed_separation_global_maximality F K hsep hlt
      split_ifs with h <;> omega
    · have hxeq : x = K.prefixChoice := F.oldSum_injective heq
      subst hxeq
      split_ifs with h <;> omega
    · have hstrict := F.newSum_strictMono hgt
      omega

/-! ### The counterexample showing that `B < g` cannot be dropped -/

/-- Old values `0, 2, 4`. -/
def weakCapOldSum : Fin 3 → ℕ := fun i => 2 * (i : ℕ)

/-- Perturbations `0, 3, 0`. -/
def weakCapPulse : Fin 3 → ℕ := fun i => if (i : ℕ) = 1 then 3 else 0

/-- The family with `g = 2`, `B = 3`: it satisfies `B < 3g` but not `B < g`. -/
def weakCapFamily : PerturbedFamily (Fin 3) where
  oldSum := weakCapOldSum
  pulse := weakCapPulse
  gap := 2
  pulseCap := 3
  gap_pos := by norm_num
  pulse_le := by
    intro x
    unfold weakCapPulse
    split <;> omega
  oldSum_injective := by
    intro x y h
    unfold weakCapOldSum at h
    exact Fin.ext (by omega)
  separated := by
    intro x y h
    unfold weakCapOldSum at h ⊢
    omega
  pulseCap_lt_three_gap := by norm_num

/-- The adjacent pair at capacity `C = 2`: `x₋` is the old value `2`, `x₊` is
the old value `4`. -/
def weakCapCut : weakCapFamily.AdjacentCut 2 where
  below := 1
  above := 2
  below_admissible := by decide
  below_maximal := by decide
  above_strict := by decide
  above_minimal := by decide

/-- The updated value selected at capacity `C' = 4C + g = 10` is `t(x₋) = 11`,
which exceeds `C'`, although the updated value `t` of the old value `0` is `0`
and therefore admissible.  So the maximality statement genuinely needs `B < g`
and does not follow from the structure hypothesis `B < 3g`. -/
theorem paper_perturbed_weak_cap_counterexample :
    ¬ weakCapFamily.pulseCap < weakCapFamily.gap ∧
      weakCapFamily.pulseCap < 3 * weakCapFamily.gap ∧
      ¬ weakCapCut.successorCarries ∧
      weakCapCut.newCapacity = 10 ∧
      weakCapFamily.newSum weakCapCut.below = 11 ∧
      ¬ weakCapFamily.newSum weakCapCut.below ≤ weakCapCut.newCapacity ∧
      weakCapFamily.newSum (0 : Fin 3) ≤ weakCapCut.newCapacity := by
  refine ⟨by decide, by decide, ?_, by decide, by decide, by decide, by decide⟩
  show ¬ (4 * weakCapCut.overshoot + weakCapCut.abovePulse ≤ weakCapFamily.gap)
  decide

/-- With no successor carry the rule selects the lower candidate, so the
counterexample above is about the value the rule actually selects. -/
theorem prefixChoice_eq_below (F : PerturbedFamily α) {C : ℕ}
    (K : F.AdjacentCut C) [Decidable K.successorCarries]
    (h : ¬ K.successorCarries) :
    K.prefixChoice = K.below := by
  rw [PerturbedFamily.AdjacentCut.prefixChoice, if_neg h]

#print axioms paper_finite_band_check_thirteen_to_thirty
#print axioms paper_successor_remainders_fourteen_through_thirtyone
#print axioms paper_universal_band_condition_would_close_half
#print axioms paper_universal_band_condition_unfolded
#print axioms paper_perturbed_order_preservation
#print axioms paper_perturbed_prefixChoice_maximal
#print axioms paper_perturbed_nextRemainder_three_branches
#print axioms paper_perturbed_separation_global_maximality
#print axioms paper_perturbed_two_stage_is_global_maximum
#print axioms paper_perturbed_weak_cap_counterexample
#print axioms prefixChoice_eq_below

end ErdosProblems.Erdos257.PaperCompleteR21
