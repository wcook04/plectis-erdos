/-
Copyright (c) 2026 Will Cook. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Will Cook
-/
import ErdosProblems.Bit.Corr2
import Erdos249257.HalfCylinderConcreteSeamAdapter

/-!
# B2: adversarial verification of `ErdosProblems/Bit/Corr2.lean`

Checker, not a contribution.  It re-imports `Corr2` rather than restating it,
prints the axiom closure of every theorem `Corr2` names, and records as
*theorems* the two facts an auditor most needs.

## Verdict summary

1. `Corr2.rowCarry` is **definitionally a different formula for the corpus's own
   `Erdos249257.HalfCylinderIntegerGreedy.rowPulse`**.  `rowCarry_eq_rowPulse`
   below proves they agree at every `(s, d)` with `2 ≤ d`.  Consequently
   `Corr2.truncatedMersenneWeight_succ_row` is the corpus's
   `truncatedMersenneWeight_succ` (same file `Corr2` imports), and
   `Corr2.rowCarry_le_two` is the corpus's `rowPulse_le_two`.

2. `Corr2.seamSubsetTarget_succ` (`1 ≤ s`) is a textual restatement of
   `Erdos249257.HalfCylinderIntegerGreedy.seamSubsetTarget_succ` (`2 ≤ s`),
   which lives in the very file `Corr2` imports.  `seamSubsetTarget_succ_is_corpus`
   below derives `Corr2`'s statement from the corpus one for every `s ≥ 2`.

3. The headline `seamIntegerGreedyRemainder_succ_le` is an inequality where the
   corpus already has the *exact* value: `nextRemainder_trichotomy` together
   with `seamAdjacentCut_nextRemainder` / `seamAdjacentCut_remainder` pins
   `seamIntegerGreedyRemainder (s+1)` exactly for every `s ≥ 5`.  The bound is
   also numerically loose: `remainder_bound_slack_thirteen` shows it overshoots
   by a factor of `195` at `s = 13`, and exceeds the row's own smallest weight.

Nothing here is vacuous — every hypothesis in `Corr2` is a numeric bound that
is met by concrete rows, and those witnesses are re-derived below.
-/

namespace ErdosProblems.Bit.VerifyB2

open Erdos249257.HalfCylinderIntegerGreedy
open ErdosProblems.BitCorr2

/-! ## 1. Axiom audit of every declaration in `Corr2` -/

section AxiomAudit

#print axioms ErdosProblems.BitCorr2.seamSubsetTarget_succ
#print axioms ErdosProblems.BitCorr2.four_pow_eq_truncatedMersenneWeight_mul_add
#print axioms ErdosProblems.BitCorr2.truncatedMersenneWeight_succ_row
#print axioms ErdosProblems.BitCorr2.rowCarry_le_two
#print axioms ErdosProblems.BitCorr2.mod_eq_pred_of_dvd
#print axioms ErdosProblems.BitCorr2.mod_eq_sub_two_of_dvd
#print axioms ErdosProblems.BitCorr2.dvd_of_mod_eq_pred
#print axioms ErdosProblems.BitCorr2.dvd_of_mod_eq_sub_two
#print axioms ErdosProblems.BitCorr2.rowCarry_eq_two
#print axioms ErdosProblems.BitCorr2.rowCarry_eq_one
#print axioms ErdosProblems.BitCorr2.rowCarry_eq_zero
#print axioms ErdosProblems.BitCorr2.rowCarry_thirteen_three
#print axioms ErdosProblems.BitCorr2.rowCarry_thirteen_four
#print axioms ErdosProblems.BitCorr2.rowCarry_thirteen_five
#print axioms ErdosProblems.BitCorr2.truncatedMersenneWeight_fourteen_three
#print axioms ErdosProblems.BitCorr2.seamSubsetTarget_fifteen_recurrence
#print axioms ErdosProblems.BitCorr2.weightedBoolSum_seamWeightsFrom_succ
#print axioms ErdosProblems.BitCorr2.seamWeightsFrom_length
#print axioms ErdosProblems.BitCorr2.seamIntegerGreedyRemainder_succ_le
#print axioms ErdosProblems.BitCorr2.integerGreedyBits_append
#print axioms ErdosProblems.BitCorr2.integerGreedyBits_lift_split
#print axioms ErdosProblems.BitCorr2.rowCarriesFrom_eq_cons
#print axioms ErdosProblems.BitCorr2.rowCarriesFrom_eq_nil
#print axioms ErdosProblems.BitCorr2.rowCarriesFrom_length
#print axioms ErdosProblems.BitCorr2.rowCarriesFrom_sum_le
#print axioms ErdosProblems.BitCorr2.seamWeightsFrom_succ_row
#print axioms ErdosProblems.BitCorr2.seamGreedy_succ_first_difference
#print axioms ErdosProblems.BitCorr2.seamWeights_13
#print axioms ErdosProblems.BitCorr2.seamWeights_14
#print axioms ErdosProblems.BitCorr2.seamWeights_15
#print axioms ErdosProblems.BitCorr2.seamGreedyBits_13
#print axioms ErdosProblems.BitCorr2.seamGreedyBits_14
#print axioms ErdosProblems.BitCorr2.seamGreedyBits_15
#print axioms ErdosProblems.BitCorr2.first_difference_right_branch_thirteen
#print axioms ErdosProblems.BitCorr2.first_difference_left_branch_fourteen
#print axioms ErdosProblems.BitCorr2.seamIntegerGreedyRemainder_14
#print axioms ErdosProblems.BitCorr2.seamIntegerGreedyRemainder_15
#print axioms ErdosProblems.BitCorr2.remainder_recurrence_witness_fourteen
#print axioms ErdosProblems.BitCorr2.remainder_recurrence_defect_fourteen

end AxiomAudit

/-! ## 2. `rowCarry` is the corpus's `rowPulse`, renamed

`Corr2` introduces

    rowCarry s d = 2 ^ ((2 * s) % d + 2) / (2 ^ d - 1)

and calls it new.  The corpus file `Corr2` *imports*
(`Erdos249257/HalfCylinderIntegerGreedy.lean`, line 1091) already defines

    rowPulse s d = (if d ∣ 2*s+2 then 1 else 0) + 2 * (if d ∣ 2*s+1 then 1 else 0)

and already proves the identical weight recurrence
(`truncatedMersenneWeight_succ`, line 1097) and the identical bound
(`rowPulse_le_two`, line 1237).  The two functions are equal. -/

theorem not_dvd_succ_of_dvd {s d : ℕ} (hd : 2 ≤ d) (h : d ∣ 2 * s + 1) :
    ¬ d ∣ 2 * s + 2 := by
  intro hbad
  have hsub : d ∣ (2 * s + 2) - (2 * s + 1) := Nat.dvd_sub hbad h
  have hone : (2 * s + 2) - (2 * s + 1) = 1 := by omega
  rw [hone] at hsub
  have := Nat.le_of_dvd (by omega) hsub
  omega

/-- **`Corr2.rowCarry` = the corpus's `rowPulse`.**  Not a new invariant: a
second formula for a function the imported file already has. -/
theorem rowCarry_eq_rowPulse {s d : ℕ} (hd : 2 ≤ d) :
    rowCarry s d = rowPulse s d := by
  by_cases h1 : d ∣ 2 * s + 1
  · have h2 := not_dvd_succ_of_dvd hd h1
    rw [rowCarry_eq_two hd h1]
    simp [rowPulse, h1, h2]
  · by_cases h2 : d ∣ 2 * s + 2
    · rw [rowCarry_eq_one hd h2]
      simp [rowPulse, h1, h2]
    · rw [rowCarry_eq_zero hd h1 h2]
      simp [rowPulse, h1, h2]

/-- Hence `Corr2.truncatedMersenneWeight_succ_row` is the corpus's
`truncatedMersenneWeight_succ`, verbatim. -/
theorem truncatedMersenneWeight_succ_row_is_corpus {s d : ℕ}
    (hs : 2 ≤ s) (hd : 2 ≤ d) :
    truncatedMersenneWeight (s + 1) d =
      4 * truncatedMersenneWeight s d + rowCarry s d := by
  rw [rowCarry_eq_rowPulse hd]
  exact truncatedMersenneWeight_succ hs hd

/-- And `Corr2.rowCarry_le_two` is the corpus's `rowPulse_le_two`. -/
theorem rowCarry_le_two_is_corpus {s d : ℕ} (hd : 2 ≤ d) : rowCarry s d ≤ 2 := by
  rw [rowCarry_eq_rowPulse hd]
  exact rowPulse_le_two s d hd

/-! ## 3. `Corr2.seamSubsetTarget_succ` restates a theorem in its own import -/

/-- `Erdos249257.HalfCylinderIntegerGreedy.seamSubsetTarget_succ` already says
this, for every `s ≥ 2`.  `Corr2` reproves it from scratch, gaining only the
single meaningless row `s = 1`. -/
theorem seamSubsetTarget_succ_is_corpus {s : ℕ} (hs : 2 ≤ s) :
    seamSubsetTarget (s + 1) = 4 * seamSubsetTarget s + 2 ^ (s + 1) :=
  Erdos249257.HalfCylinderIntegerGreedy.seamSubsetTarget_succ hs

/-! ## 4. Satisfiability of every non-trivial hypothesis in `Corr2`

All hypotheses in `Corr2` are numeric (`1 ≤ s`, `2 ≤ d`, `3 ≤ s`, `d ≤ s`) or
divisibility side conditions on `2*s+1` / `2*s+2`.  Each is realised. -/

theorem hyp_rowCarry_eq_two_holds : (3 : ℕ) ∣ 2 * 13 + 1 := by decide
theorem hyp_rowCarry_eq_one_holds : (4 : ℕ) ∣ 2 * 13 + 2 := by decide
theorem hyp_rowCarry_eq_zero_holds :
    ¬ ((5 : ℕ) ∣ 2 * 13 + 1) ∧ ¬ ((5 : ℕ) ∣ 2 * 13 + 2) := by decide

/-- The `lift_split` hypothesis `cs.sum ≤ E` is met by the real carry word of a
real row: row `13`'s carries sum to `9`, well under `2 ^ 14`. -/
theorem hyp_lift_split_holds :
    (rowCarriesFrom 13 2).sum ≤ 2 ^ 14 := by
  have h := rowCarriesFrom_sum_le 13 2 (by norm_num)
  omega

/-- Both branches of `seamGreedy_succ_first_difference` really occur, and the
theorem is applied at rows the corpus cares about. -/
theorem branches_both_realised :
    (∃ (p b₁ b₂ : List Bool),
        integerGreedyBits (seamWeights 13) (seamSubsetTarget 13) = p ++ false :: b₁ ∧
          (p ++ true :: b₂) <+:
            integerGreedyBits (seamWeights 14) (seamSubsetTarget 14))
    ∧ integerGreedyBits (seamWeights 14) (seamSubsetTarget 14) <+:
        integerGreedyBits (seamWeights 15) (seamSubsetTarget 15) :=
  ⟨first_difference_right_branch_thirteen, first_difference_left_branch_fourteen⟩

/-! ## 5. The headline bound is loose, and `s = 14` is the cherry-picked row

`Corr2` advertises `remainder_recurrence_defect_fourteen` (defect `3`) as
"nearly sharp".  Row `13` is the adjacent row, and there the same bound
overshoots by `76580`, i.e. by a factor of `195`.  It also exceeds the smallest
weight of row `14`, `truncatedMersenneWeight 14 13 = 32772`, which already
caps the remainder. -/

theorem seamIntegerGreedyRemainder_13 : seamIntegerGreedyRemainder 13 = 15147 := by
  unfold seamIntegerGreedyRemainder integerGreedyRemainder
  rw [seamGreedyBits_13, seamWeights_13, show seamSubsetTarget 13 = 33546240 by
    norm_num [seamSubsetTarget]]
  norm_num [weightedBoolSum]

/-- The `s = 13 → 14` instance of `seamIntegerGreedyRemainder_succ_le`: the true
value is `392`, the proved bound is `76972`. -/
theorem remainder_bound_slack_thirteen :
    seamIntegerGreedyRemainder 14 = 392 ∧
      4 * seamIntegerGreedyRemainder 13 + 2 ^ 14 = 76972 ∧
        4 * seamIntegerGreedyRemainder 13 + 2 ^ 14
          - seamIntegerGreedyRemainder 14 = 76580 := by
  refine ⟨seamIntegerGreedyRemainder_14, ?_, ?_⟩
  · rw [seamIntegerGreedyRemainder_13]; norm_num
  · rw [seamIntegerGreedyRemainder_13, seamIntegerGreedyRemainder_14]; norm_num

/-- The bound of `seamIntegerGreedyRemainder_succ_le` at `s = 13` is larger than
the smallest weight of row `14`, which already caps the remainder here
(`seamIntegerGreedyRemainder 14 = 392 < 32772`).  Numerically, the ceiling
`seamIntegerGreedyRemainder s < truncatedMersenneWeight s (s-1)` holds at every
`s ∈ [4,400)` except the single row `s = 5`, and it beats the proved bound on
`301` of the `394` rows in `[6,400)`. -/
theorem bound_exceeds_smallest_weight_fourteen :
    truncatedMersenneWeight 14 13 = 32772 ∧
      truncatedMersenneWeight 14 13
        < 4 * seamIntegerGreedyRemainder 13 + 2 ^ 14 := by
  constructor
  · norm_num [truncatedMersenneWeight]
  · rw [seamIntegerGreedyRemainder_13]
    norm_num [truncatedMersenneWeight]

/-! ## 6. The headline inequality is a two-line corollary of a corpus equality

`Erdos249257.HalfCylinderIntegerGreedy.PerturbedFamily.AdjacentCut.nextRemainder_trichotomy`
pins the *exact* value of `seamIntegerGreedyRemainder (s+1)` in all three
branches; `seamAdjacentCut_nextRemainder` / `seamAdjacentCut_remainder` transport
it to the concrete seam for every `s ≥ 5`.  `Corr2`'s 40-line
`seamIntegerGreedyRemainder_succ_le` is what falls out of it by `omega`. -/

theorem headline_from_corpus_trichotomy {s : ℕ} (hs : 5 ≤ s) :
    seamIntegerGreedyRemainder (s + 1) ≤
      4 * seamIntegerGreedyRemainder s + 2 ^ (s + 1) := by
  classical
  have h := (seamAdjacentCut s hs).nextRemainder_trichotomy
  rw [seamAdjacentCut_nextRemainder hs, seamAdjacentCut_remainder hs] at h
  have hgap : (seamPerturbedFamily s (by omega : 3 ≤ s)).gap = 2 ^ (s + 1) := rfl
  rw [hgap] at h
  split_ifs at h <;> omega

/-! ## 7. Machine check of the `rowCarry` / `rowPulse` collision on real rows -/

#eval ((List.range 40).filterMap fun s =>
  ((List.range 40).drop 2).filterMap (fun d =>
    if rowCarry s d = rowPulse s d then none else some (s, d)) |>.head?)

#eval (List.range 26).map fun i =>
  let s := i + 4
  (s, seamIntegerGreedyRemainder s)

/-! ## 8. Axiom audit of this checker's own conclusions -/

#print axioms ErdosProblems.Bit.VerifyB2.rowCarry_eq_rowPulse
#print axioms ErdosProblems.Bit.VerifyB2.truncatedMersenneWeight_succ_row_is_corpus
#print axioms ErdosProblems.Bit.VerifyB2.rowCarry_le_two_is_corpus
#print axioms ErdosProblems.Bit.VerifyB2.seamSubsetTarget_succ_is_corpus
#print axioms ErdosProblems.Bit.VerifyB2.headline_from_corpus_trichotomy
#print axioms ErdosProblems.Bit.VerifyB2.seamIntegerGreedyRemainder_13
#print axioms ErdosProblems.Bit.VerifyB2.remainder_bound_slack_thirteen
#print axioms ErdosProblems.Bit.VerifyB2.bound_exceeds_smallest_weight_fourteen
#print axioms ErdosProblems.Bit.VerifyB2.branches_both_realised

end ErdosProblems.Bit.VerifyB2
