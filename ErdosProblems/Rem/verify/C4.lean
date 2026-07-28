/-
Copyright (c) 2026 Will Cook. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Will Cook
-/
import ErdosProblems.Rem.C4

/-!
# Adversarial verification of `ErdosProblems/Rem/C4.lean`

Three jobs:

1. **Axiom audit** — `#print axioms` on every theorem C4 exports.
2. **Satisfiability** — `#eval` the non-trivial hypotheses on real data over a
   wide range of rows, plus a *proved* decidable certificate producer so the
   evaluation is not merely a proxy.
3. **Redundancy audit** — check C4's central lemmas against what the corpus
   already proves in the files C4 itself imports.
-/

namespace ErdosProblems.RemC4.Verify

open Erdos249257
open Erdos249257.HalfCylinderIntegerGreedy

/-! ## 1. Axiom audit -/

#print axioms ErdosProblems.RemC4.truncatedMersenneWeight_top_band
#print axioms ErdosProblems.RemC4.sum_seamWeightsFrom_top_band
#print axioms ErdosProblems.RemC4.integerGreedyRemainder_cons
#print axioms ErdosProblems.RemC4.greedy_allTrue
#print axioms ErdosProblems.RemC4.greedy_skip_tail
#print axioms ErdosProblems.RemC4.seamWeightsFrom_getElem?
#print axioms ErdosProblems.RemC4.seamWeightsFrom_drop
#print axioms ErdosProblems.RemC4.seamGreedyWord_getElem?
#print axioms ErdosProblems.RemC4.mem_seamWordSupport_iff_greedyBit
#print axioms ErdosProblems.RemC4.remainder_add_tail_lt_weight
#print axioms ErdosProblems.RemC4.three_mul_remainder_lt_of_lateSkip
#print axioms ErdosProblems.RemC4.remainder_lt_of_lateSkip
#print axioms ErdosProblems.RemC4.remainder_lt_of_terminal_skip
#print axioms ErdosProblems.RemC4.six_mul_remainder_lt_of_largestSkipLate
#print axioms ErdosProblems.RemC4.remainder_lt_of_largestSkipLate
#print axioms ErdosProblems.RemC4.remainder_lt_two_pow_succ_add_of_largestSkipLate
#print axioms ErdosProblems.RemC4.remainder_below_three_halfPoint_cofinally_of_half_mem
#print axioms ErdosProblems.RemC4.half_mem_sandwich
#print axioms ErdosProblems.RemC4.seamIntegerGreedyRemainder_fourteen
#print axioms ErdosProblems.RemC4.isLargestFalseRank_fourteen
#print axioms ErdosProblems.RemC4.remainder_fourteen_lt_sharp
#print axioms ErdosProblems.RemC4.remainder_fourteen_lt
#print axioms ErdosProblems.RemC4.remainder_twenty_lt

/-! ## 2. Satisfiability

### 2a. A *proved* certificate producer for `LargestSkipLateAt`

`lateCheck` is not an invented proxy: it is the definitional unfolding of the
corpus predicate through C4's own bridge `mem_seamWordSupport_iff_greedyBit`,
and `largestSkipLateAt_of_lateCheck` below proves the implication into the
corpus notion `Erdos249257.LargestSkipLateAt`. -/

/-- Concrete greedy bit word of row `s`, i.e. `(seamGreedyWord s).toList`. -/
def gbits (s : ℕ) : List Bool :=
  integerGreedyBits (seamWeights s) (seamSubsetTarget s)

theorem gbits_length (s : ℕ) : (gbits s).length = s - 2 := by
  rw [gbits, integerGreedyBits_length, seamWeights_length_eq]

/-- Decidable search for a late largest false rank.  Every clause is stated
directly on `(seamGreedyWord s).toList`, so nothing here is a proxy. -/
def lateCheck (s : ℕ) : Bool :=
  (List.range s).any fun D =>
    decide (2 ≤ D) && decide (2 * s < 3 * D) &&
      decide ((gbits s)[D - 2]? = some false) &&
      ((List.range s).all fun e =>
        decide (e ≤ D) || decide ((gbits s)[e - 2]? = some true))

/-- **Soundness.**  A `true` value of `lateCheck` produces the corpus
predicate `LargestSkipLateAt`, via C4's own support/bit bridge. -/
theorem largestSkipLateAt_of_lateCheck {s : ℕ} (h : lateCheck s = true) :
    LargestSkipLateAt s := by
  rw [lateCheck, List.any_eq_true] at h
  obtain ⟨D, hDmem, hD⟩ := h
  have hDs : D < s := List.mem_range.mp hDmem
  simp only [Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true,
    Bool.or_eq_true] at hD
  obtain ⟨⟨⟨hd2, hband⟩, hfalse⟩, hrest⟩ := hD
  refine ⟨D, ⟨hd2, hDs, ?_, ?_⟩, hband⟩
  · intro hmem
    have hbit : (gbits s)[D - 2]? = some true :=
      (ErdosProblems.RemC4.mem_seamWordSupport_iff_greedyBit hd2 hDs).mp hmem
    rw [hbit] at hfalse
    exact Bool.noConfusion (Option.some.inj hfalse)
  · intro e hDe hes
    have hd2e : 2 ≤ e := by omega
    refine (ErdosProblems.RemC4.mem_seamWordSupport_iff_greedyBit hd2e hes).mpr ?_
    rcases hrest e (List.mem_range.mpr hes) with hle | htrue
    · omega
    · exact htrue

/-! ### 2b. The hypothesis class, evaluated on real data

`lateRows lo hi` lists the rows of `[lo, hi)` where the C4 hypothesis
`LargestSkipLateAt` is certified, `badRows` lists those where it is not. -/

def lateRows (lo hi : ℕ) : List ℕ :=
  ((List.range hi).drop lo).filter fun s => lateCheck s

def badRows (lo hi : ℕ) : List ℕ :=
  ((List.range hi).drop lo).filter fun s => !(lateCheck s)

-- Rows in `[4, 120)` where `LargestSkipLateAt` FAILS.  Everything else is late.
#eval badRows 4 120
-- How many rows in `[4, 120)` are late:
#eval (lateRows 4 120).length

/-! ### 2c. The *conclusions*, evaluated on the same data

This is the decisive measurement.  If the headline conclusion
`ρ s < 3 * 2 ^ s` also holds at every row where the hypothesis FAILS, then the
bound is not detecting lateness at all, and the `#257` "necessary condition"
built on it constrains nothing. -/

/-- Rows of `[lo, hi)` violating C4's headline `ρ s < 3 * 2 ^ s`. -/
def violatesHeadline (lo hi : ℕ) : List ℕ :=
  ((List.range hi).drop lo).filter fun s =>
    decide (3 * 2 ^ s ≤ seamIntegerGreedyRemainder s)

/-- Rows of `[lo, hi)` violating C4's sharp form `ρ s < 2^(s+1) + 2^(s-2)`. -/
def violatesSharp (lo hi : ℕ) : List ℕ :=
  ((List.range hi).drop lo).filter fun s =>
    decide (2 ^ (s + 1) + 2 ^ (s - 2) ≤ seamIntegerGreedyRemainder s)

/-- Rows of `[lo, hi)` violating the PRE-EXISTING `Bit/R2` ceiling
`3 ρ s < 7 * 2 ^ s + 4`. -/
def violatesR2Ceiling (lo hi : ℕ) : List ℕ :=
  ((List.range hi).drop lo).filter fun s =>
    decide (7 * 2 ^ s + 4 ≤ 3 * seamIntegerGreedyRemainder s)

-- Empty lists here mean the conclusion holds unconditionally on the range,
-- late rows and bad rows alike.
#eval violatesHeadline 4 120
#eval violatesSharp 4 120
#eval violatesR2Ceiling 4 120

-- The four rows of `[4,120)` where the hypothesis FAILS, with the headline
-- conclusion evaluated at each of them anyway: (s, rho, rho < 3*2^s,
-- 3*rho < 7*2^s+4).
#eval (badRows 4 120).map fun s =>
  (s, seamIntegerGreedyRemainder s,
   decide (seamIntegerGreedyRemainder s < 3 * 2 ^ s),
   decide (3 * seamIntegerGreedyRemainder s < 7 * 2 ^ s + 4))

-- Ratio `rho s / 2 ^ s` in hundredths.  C4's headline constant is 300;
-- the pre-existing R2 ceiling is 233; C4's sharp form is 225.
#eval (List.range 121).drop 4 |>.map fun s =>
  (s, 100 * seamIntegerGreedyRemainder s / 2 ^ s)

-- Worst ratio (in hundredths) attained on `[4, 121)`.
#eval ((List.range 121).drop 4 |>.map fun s =>
  100 * seamIntegerGreedyRemainder s / 2 ^ s).foldl max 0

-- The *sufficient* condition of `Bit/R2` (`rho s <= 2 ^ s`) — how often it
-- actually holds, which is the part nobody has proved cofinally.
#eval (((List.range 120).drop 4).filter fun s =>
  decide (seamIntegerGreedyRemainder s ≤ 2 ^ s)).length

/-! ### 2d. Fresh proved witnesses beyond C4's two certificates

C4 only exhibits rows `14` and `20` (both re-used from the corpus).  Here are
new ones, proved by kernel reduction through the soundness theorem above. -/

theorem largestSkipLateAt_thirty : LargestSkipLateAt 30 :=
  largestSkipLateAt_of_lateCheck (by decide +kernel)

theorem largestSkipLateAt_fortyThree : LargestSkipLateAt 43 :=
  largestSkipLateAt_of_lateCheck (by decide +kernel)

theorem largestSkipLateAt_sixtyOne : LargestSkipLateAt 61 :=
  largestSkipLateAt_of_lateCheck (by decide +kernel)

#print axioms largestSkipLateAt_thirty
#print axioms largestSkipLateAt_sixtyOne
#print axioms largestSkipLateAt_fortyThree

/-! ## 3. Redundancy audit

C4's module docstring says the size law it supplies is *missing* from the
corpus, and that before it "the only unconditional upper bound on that
remainder at an arbitrary row was the trivial `ρ s ≤ 2^(2s-1) - 2^s`".

Both claims are checked here against the corpus C4 imports. -/

/-- C4's `three_mul_remainder_lt_of_lateSkip` is, statement for statement, the
pre-existing corpus theorem `Erdos249257.three_mul_remainder_lt_exactLateGap`
(modulo the removable side condition `5 ≤ s`).  This term-mode proof uses the
corpus lemma only. -/
theorem corpus_already_proves_C4_core
    {s D : ℕ} (hs : 5 ≤ s)
    (hD : IsLargestFalseRank (seamGreedyWord s) D) (hband : 2 * s < 3 * D) :
    3 * seamIntegerGreedyRemainder s < 3 * 2 ^ (s + 1) + 2 * 4 ^ (s - D) + 4 :=
  Erdos249257.three_mul_remainder_lt_exactLateGap hs hD hband

/-- C4's headline `remainder_lt_of_largestSkipLate` (`ρ s < 3 * 2 ^ s`) is
*strictly weaker* than the pre-existing `Bit/R2` ceiling
`ObeysRemainderCeiling s` (`ρ s < (7/3) * 2 ^ s`), which C4 imports and never
mentions.  Derived here from R2 alone. -/
theorem corpus_already_proves_C4_headline
    {s : ℕ} (hs : 5 ≤ s) (h : LargestSkipLateAt s) :
    seamIntegerGreedyRemainder s < 3 * 2 ^ s := by
  have hceil := ErdosProblems.BitR2.three_mul_remainder_lt_of_largestSkipLateAt hs h
  rw [ErdosProblems.BitR2.ObeysRemainderCeiling] at hceil
  have hbig : (4 : ℕ) ≤ 2 ^ s := by
    calc (4 : ℕ) = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ s := Nat.pow_le_pow_right (by norm_num) (by omega)
  omega

/-- C4's `#257` "necessary condition" is a three-line corollary of two corpus
theorems C4 imports (`Skip/D2`'s equivalence and `Bit/R2`'s ceiling).  No part
of C4's new machinery is needed. -/
theorem corpus_already_proves_C4_necessary_condition
    (h : (1 / 2 : ℝ) ∈ mersenneAchievementSet) :
    ∀ N : ℕ, ∃ s : ℕ, N ≤ s ∧ seamIntegerGreedyRemainder s < 3 * 2 ^ s := by
  intro N
  obtain ⟨s, hsN, hlate⟩ :=
    AngleD2.half_mem_iff_unboundedLargestSkipLate.mp h (max N 5)
  exact ⟨s, le_trans (le_max_left N 5) hsN,
    corpus_already_proves_C4_headline (le_trans (le_max_right N 5) hsN) hlate⟩

#print axioms corpus_already_proves_C4_core
#print axioms corpus_already_proves_C4_headline
#print axioms corpus_already_proves_C4_necessary_condition

/-- What IS new: C4's `six_mul_remainder_lt_of_largestSkipLate`
(`6 ρ < 13 * 2 ^ s + 8`, i.e. `ρ < (13/6) 2 ^ s`) does imply R2's ceiling
(`3 ρ < 7 * 2 ^ s + 4`, i.e. `ρ < (7/3) 2 ^ s`) and is strictly sharper.  So
the genuine delta of this file is the constant `7/3 → 13/6`, about 7%. -/
theorem C4_six_mul_is_sharper_than_R2_ceiling
    {s : ℕ} (h : LargestSkipLateAt s) :
    ErdosProblems.BitR2.ObeysRemainderCeiling s := by
  have h6 := ErdosProblems.RemC4.six_mul_remainder_lt_of_largestSkipLate h
  rw [ErdosProblems.BitR2.ObeysRemainderCeiling]
  omega

#print axioms C4_six_mul_is_sharper_than_R2_ceiling

-- Note the internal inconsistency: the file labels
-- `remainder_lt_two_pow_succ_add_of_largestSkipLate` (`ρ < 2.25 * 2^s`) "the
-- sharp headline", but `six_mul_remainder_lt_of_largestSkipLate` in the same
-- file already gives `ρ < 2.167 * 2^s`, and the *stated* headline
-- `remainder_lt_of_largestSkipLate` is `ρ < 3 * 2^s`, weaker than all of them
-- and weaker than the imported R2 ceiling.

-- Rows of `[4,120)` violating C4's tightest form `6 ρ < 13 * 2^s + 8`.
#eval (((List.range 120).drop 4).filter fun s =>
  decide (13 * 2 ^ s + 8 ≤ 6 * seamIntegerGreedyRemainder s))

/-! ## 4. Erdős #257 status check

C4 does *not* prove `RemainderReachesHalfPointCofinally`, and does not prove
`1/2 ∈ mersenneAchievementSet`.  `half_mem_sandwich` is a conjunction of two
implications; its first component is literally the imported R2 theorem and its
second is the corollary re-derived above.  Neither side is discharged. -/

-- The first component of `half_mem_sandwich` is verbatim the imported R2
-- theorem; nothing in C4 contributes to it.
example : ErdosProblems.BitR2.RemainderReachesHalfPointCofinally →
    (1 / 2 : ℝ) ∈ mersenneAchievementSet :=
  ErdosProblems.BitR2.half_mem_of_remainderReachesHalfPointCofinally

-- Neither `RemainderReachesHalfPointCofinally` nor `1/2 ∈ mersenneAchievementSet`
-- is discharged anywhere in C4.  #257 remains open.

end ErdosProblems.RemC4.Verify
