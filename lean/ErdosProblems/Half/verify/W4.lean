/-
Copyright (c) 2026 Will Cook. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Will Cook
-/
import ErdosProblems.Half.H4

/-!
Adversarial verification scratch file for `ErdosProblems/Half/H4.lean`.
Nothing here is a contribution; it is an audit.
-/

namespace Erdos249257

namespace SkipH4

open HalfCylinderIntegerGreedy

/-! ## 1. Axiom audit of every theorem in H4 -/

#print axioms blockAll
#print axioms rowOk_of_block
#print axioms exists_largestFalseRank_of_rowOk
#print axioms largestFalseRank_near_terminal
#print axioms largestSkipLateAt_block
#print axioms largestSkipHalfAt_block
#print axioms highAll
#print axioms largestFalseRank_near_terminal_high
#print axioms largestSkipLateAt_high
#print axioms largestSkipHalfAt_high
#print axioms largestSkipHalfAt_3001
#print axioms largestSkipHalfAt_survivorWindow
#print axioms largestSkipHalfAt_landingRow
#print axioms no_refutation_on_block
#print axioms not_forall_not_largestSkipHalfAt_landingRow
#print axioms allRight_landingRow_conclusion_is_unconditional
#print axioms half_mem_of_eventually_largestSkipHalfAt
#print axioms half_mem_of_largestFalseRank_near_terminal

-- upstream, load-bearing
#print axioms SkipD3.isLargestFalseRank_of_rowChk
#print axioms SkipD1.half_mem_of_cofinal_largestSkipHalfAt
#print axioms SkipD1.allRight_landingExcess_two_forces_halfSkip_landingRow
#print axioms Erdos249257.seamWordSupport_add_eq_of_eventually_right

/-! ## 2. Does the certificate have teeth?

If `rowChk` were vacuously true the whole file would be worthless.  It is not:
at the same rows it accepts the tabulated rank it rejects the neighbours, and
it rejects the terminal rank at rows where the terminal rank is selected. -/

set_option maxRecDepth 100000 in
example : SkipD3.rowChk 63 62 = true := by decide +kernel

set_option maxRecDepth 100000 in
example : SkipD3.rowChk 63 61 = false := by decide +kernel

set_option maxRecDepth 100000 in
example : SkipD3.rowChk 63 60 = false := by decide +kernel

/-! Row `81` has `d₀ = 75`, five below the terminal rank `80`.  So the largest
false rank is *not* trivially `s - 1`, and the predicate really reads the data. -/
set_option maxRecDepth 100000 in
example : SkipD3.rowChk 81 75 = true := by decide +kernel

set_option maxRecDepth 100000 in
example : SkipD3.rowChk 81 80 = false := by decide +kernel

set_option maxRecDepth 100000 in
example : SkipD3.rowChk 81 76 = false := by decide +kernel

/-! And the terminal rank of row `81` is genuinely *selected* — the greedy is
not simply skipping everything at the top. -/
set_option maxRecDepth 100000 in
example : (80 : ℕ) ∈ seamWordSupport (seamGreedyWord 81) :=
  (SkipD3.mem_support_iff (by norm_num) (by norm_num)).mpr (by decide +kernel)

/-! The tabulated value really is `75`, not `80`. -/
set_option maxRecDepth 100000 in
example : d0At 81 = 75 := by decide

/-! ## 3. Non-vacuity of H4's own hypotheses

Every hypothesis H4 assumes is a numeric range on `s`.  Witnesses exist. -/

example : SkipD1.LargestSkipHalfAt 61 := largestSkipHalfAt_block (by norm_num) (by norm_num)
example : SkipD1.LargestSkipHalfAt 500 := largestSkipHalfAt_block (by norm_num) (by norm_num)
example : LargestSkipLateAt 500 := largestSkipLateAt_block (by norm_num) (by norm_num)
example : SkipD1.LargestSkipHalfAt 3001 := largestSkipHalfAt_3001

/-! ## 4. Section 4 is one theorem stated four times

`no_refutation_on_block` is the literal contrapositive of
`largestSkipHalfAt_landingRow`; `not_forall_not_...` is its instance at
`D = 60`; and `allRight_landingRow_conclusion_is_unconditional` is the same
statement conjoined with a proposition it trivially implies.  Each is
re-derivable from `largestSkipHalfAt_landingRow` alone, with no appeal to
`SkipD1` at all. -/

example : ¬ ∃ D : ℕ, 60 ≤ D ∧ D ≤ 499 ∧ ¬ SkipD1.LargestSkipHalfAt (D + 1) := by
  rintro ⟨D, hD, hD', hcon⟩
  exact hcon (largestSkipHalfAt_landingRow D hD hD')

/-- The first conjunct of `allRight_landingRow_conclusion_is_unconditional` is a
consequence of its second conjunct by pure logic — `SkipD1` is not needed. -/
example (D : ℕ) (hD : 60 ≤ D) (hD' : D ≤ 499) :
    (∀ _h : (∀ s : ℕ, D + 1 ≤ s →
        seamGreedyWord (s + 1) = (seamGreedyWord s).extend true),
      ∀ _h' : Recon257.seamExcess (D + 1) = 2,
        SkipD1.LargestSkipHalfAt (D + 1)) ∧
      SkipD1.LargestSkipHalfAt (D + 1) :=
  ⟨fun _ _ => largestSkipHalfAt_landingRow D hD hD',
    largestSkipHalfAt_landingRow D hD hD'⟩

/-! ## 5. The vacuity is much sharper than H4 claims

H4 says `SkipD1.allRight_landingExcess_two_forces_halfSkip_landingRow` excludes
nothing on `60 ≤ D ≤ 499` because its *conclusion* is unconditionally true
there.  The real situation is stronger: on that range its *hypothesis* is
outright **false**.

Under an all-right tail from `D+1` the seam support at every later row is
`support (D+1) ∪ Ico (D+1) s` (`seamWordSupport_add_eq_of_eventually_right`),
so every rank in `[D+1, s)` is selected.  H4's own kernel certificate at row
`3001` says rank `3000` is *skipped*.  For `D ≤ 499` we have
`D + 1 ≤ 3000 < 3001`, so the two are incompatible. -/

theorem audit_no_allRight_tail_below_500
    (D : ℕ) (hD5 : 5 ≤ D) (hD' : D ≤ 499) :
    ¬ (∀ s : ℕ, D + 1 ≤ s →
        seamGreedyWord (s + 1) = (seamGreedyWord s).extend true) := by
  intro hright
  have hskip : (3000 : ℕ) ∉ seamWordSupport (seamGreedyWord 3001) :=
    (largestFalseRank_near_terminal_high (s := 3001) (d := 3000) (by decide)).1.2.2.1
  have hsupp := seamWordSupport_add_eq_of_eventually_right (D + 1) (by omega) hright
    (3001 - (D + 1))
  rw [show D + 1 + (3001 - (D + 1)) = 3001 from by omega] at hsupp
  refine hskip ?_
  rw [hsupp]
  exact Finset.mem_union_right _ (Finset.mem_Ico.mpr ⟨by omega, by norm_num⟩)

/-- Consequently the `SkipD1` per-class theorem is vacuous in the strong sense
on the whole range H4 discusses: no `D` in `[60, 499]` satisfies its
`hright` hypothesis, so it is an implication from a refuted premise. -/
theorem audit_skipD1_landingRow_premise_is_false
    (D : ℕ) (hD : 60 ≤ D) (hD' : D ≤ 499) :
    ¬ (∀ s : ℕ, D + 1 ≤ s →
        seamGreedyWord (s + 1) = (seamGreedyWord s).extend true) :=
  audit_no_allRight_tail_below_500 D (by omega) hD'

/-- The refutation is not limited to `D ≤ 499`.  The single row-`3001`
certificate refutes an all-right tail beginning at **any** row `S` with
`5 ≤ S ≤ 3000` — the argument only needs one skipped rank `≥ S` at one row
`> S`, and rank `3000` at row `3001` is one. -/
theorem audit_no_allRight_tail_start_le_3000
    (S : ℕ) (hS : 5 ≤ S) (hS' : S ≤ 3000) :
    ¬ (∀ s : ℕ, S ≤ s →
        seamGreedyWord (s + 1) = (seamGreedyWord s).extend true) := by
  intro hright
  have hskip : (3000 : ℕ) ∉ seamWordSupport (seamGreedyWord 3001) :=
    (largestFalseRank_near_terminal_high (s := 3001) (d := 3000) (by decide)).1.2.2.1
  have hsupp := seamWordSupport_add_eq_of_eventually_right S hS hright (3001 - S)
  rw [show S + (3001 - S) = 3001 from by omega] at hsupp
  refine hskip ?_
  rw [hsupp]
  exact Finset.mem_union_right _ (Finset.mem_Ico.mpr ⟨by omega, by norm_num⟩)

/-- Hence every corpus theorem carrying an all-right-tail hypothesis from `D+1`
is an implication from a refuted premise for every `D ≤ 2999`, not merely for
`D ≤ 499`.  H4 had this in hand and stated only the weaker form. -/
theorem audit_skipD1_landingRow_premise_is_false_below_3000
    (D : ℕ) (hD : 60 ≤ D) (hD' : D ≤ 2999) :
    ¬ (∀ s : ℕ, D + 1 ≤ s →
        seamGreedyWord (s + 1) = (seamGreedyWord s).extend true) :=
  audit_no_allRight_tail_start_le_3000 (D + 1) (by omega) (by omega)

/-! ## 6. What is NOT established

`SeamGreedyEventuallyRight` is `∃ S, ∀ s ≥ S, …`.  Audit 5 refutes every start
`S ≤ 500`, and nothing above it, so it does **not** refute
`SeamGreedyEventuallyRight`, and therefore does **not** give
`1/2 ∈ mersenneAchievementSet`.  H4's section 5 is likewise conditional: its
hypotheses quantify over all `s ≥ 61`, and H4 verifies only `[61, 500]` plus
fourteen sampled rows.  The gap is infinite and no theorem in H4 narrows it.

Also, `half_mem_of_eventually_largestSkipHalfAt` is strictly *weaker* than the
`SkipD1` theorem it wraps: `SkipD1.half_mem_of_cofinal_largestSkipHalfAt`
already concludes from cofinally many rows, and "every row `≥ 61`" implies
"cofinally many".  The wrapper adds no reach. -/

example
    (h : ∀ s : ℕ, 61 ≤ s → SkipD1.LargestSkipHalfAt s) :
    (1 / 2 : ℝ) ∈ mersenneAchievementSet :=
  SkipD1.half_mem_of_cofinal_largestSkipHalfAt
    (fun B => ⟨max B 61, le_max_left _ _, h _ (le_max_right _ _)⟩)

#print axioms audit_no_allRight_tail_below_500
#print axioms audit_skipD1_landingRow_premise_is_false
#print axioms audit_no_allRight_tail_start_le_3000
#print axioms audit_skipD1_landingRow_premise_is_false_below_3000

end SkipH4

end Erdos249257
