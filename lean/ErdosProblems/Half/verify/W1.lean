/-
Copyright (c) 2026 Will Cook. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Will Cook
-/
import ErdosProblems.Half.H1

/-!
# W1: adversarial verification of `ErdosProblems/Half/H1.lean`

This file is a *checker*, not a contribution.  It

* re-imports `H1` (rather than restating any of it), so every `#print axioms`
  below reports the real dependency closure, including the closure through
  `ErdosProblems.Skip.D1` and `Erdos249257.HalfCylinderMiddleCarryLowerBound`;
* prints the axioms of every theorem `H1` names in its module docstring;
* independently re-derives the non-vacuity witnesses, rather than trusting
  `H1`'s prose;
* records, as theorems, the two vacuity facts an auditor most needs:
  the half zone's minimum correction is *attained* (so `le_halfGapCorrection`
  is sharp, not a throwaway), and the landing hypothesis `hland` **fails** at
  the one row `H1` certifies, so the two `hland` theorems are conditional on
  something never exhibited.
-/

namespace ErdosProblems.Half.VerifyW1

open Erdos249257
open Erdos249257.HalfCylinderIntegerGreedy
open ErdosProblems.HalfH1

/-! ## 1. Axiom audit of every main theorem -/

section AxiomAudit

#print axioms ErdosProblems.HalfH1.truncatedMersenneWeight_eq_threeTerm_of_halfRank
#print axioms ErdosProblems.HalfH1.seven_mul_cubeSuffixSum_add_boundary
#print axioms ErdosProblems.HalfH1.seamWeightsFrom_sum_halfZone
#print axioms ErdosProblems.HalfH1.twentyOne_mul_tailWeight_add_exactHalfGap
#print axioms ErdosProblems.HalfH1.halfGapCorrection_lt_twentyOne_mul_gap
#print axioms
  ErdosProblems.HalfH1.twentyOne_mul_largestSkipLowerWeight_add_exactHalfGap_eq_upperWeight
#print axioms
  ErdosProblems.HalfH1.seamAdjacentCut_above_eq_largestSkipUpperWord_of_halfZone
#print axioms ErdosProblems.HalfH1.twentyOne_mul_remainder_add_overshoot_eq_exactHalfGap
#print axioms ErdosProblems.HalfH1.twentyOne_dvd_halfGapCorrection
#print axioms ErdosProblems.HalfH1.twentyOne_mul_remainder_add_overshoot_eq_skipHalfGap
#print axioms ErdosProblems.HalfH1.skipHalfGapCorrection_pos_and_lt
#print axioms ErdosProblems.HalfH1.gap_strictly_between_of_largestSkipHalf
#print axioms ErdosProblems.HalfH1.twentyOne_mul_overshoot_add_fortyTwo_eq_skipHalfGap
#print axioms ErdosProblems.HalfH1.landing_forces_correction_window
#print axioms ErdosProblems.HalfH1.le_halfGapCorrection
#print axioms ErdosProblems.HalfH1.landing_congruence_is_trivial
#print axioms ErdosProblems.HalfH1.isLargestFalseRank_eleven_seven
#print axioms ErdosProblems.HalfH1.seamAdjacentCut_gap_eleven
#print axioms ErdosProblems.HalfH1.inHalfZone_or_late_of_half

end AxiomAudit

/-! ## 2. Non-vacuity, re-derived rather than trusted

`H1` asserts in prose that the half zone is inhabited and reachable.  Each
claim is re-established here from scratch.
-/

/-- The half zone is inhabited at its extreme corner `s - d = 1`, `2 s = 3 d`. -/
theorem inHalfZone_three_two : InHalfZone 3 2 := ⟨by norm_num, by norm_num, by norm_num⟩

/-- `le_halfGapCorrection` is **sharp**: `105` is attained, at `(s,d) = (3,2)`.
So the "size route is dead" argument is not resting on a loose bound. -/
theorem halfGapCorrection_three_two : halfGapCorrection 3 2 = 105 := by
  norm_num [halfGapCorrection]

/-- Independent confirmation that `H1`'s own lower bound is met with equality
there, i.e. the bound cannot be improved. -/
theorem le_halfGapCorrection_sharp :
    105 ≤ halfGapCorrection 3 2 ∧ halfGapCorrection 3 2 = 105 :=
  ⟨le_halfGapCorrection inHalfZone_three_two, halfGapCorrection_three_two⟩

/-- The hypotheses of the headline identity really are simultaneously
satisfiable: `s = 11` is a half-late row in `SkipD1`'s sense. -/
theorem largestSkipHalfAt_eleven : SkipD1.LargestSkipHalfAt 11 :=
  ⟨7, isLargestFalseRank_eleven_seven, by norm_num⟩

/-- Re-derivation of the `s = 11` conclusion through the *combined*
(`skipHalfGapCorrection`) route rather than the half-zone-only route, as a
cross-check that the two branches agree where they meet. -/
theorem gap_eleven_via_combined (hs : 5 ≤ 11) :
    (seamAdjacentCut 11 hs).remainder + (seamAdjacentCut 11 hs).overshoot = 4270 := by
  have hid := twentyOne_mul_remainder_add_overshoot_eq_skipHalfGap hs
    isLargestFalseRank_eleven_seven (by norm_num : (11 : ℕ) < 2 * 7)
  have hcorr : skipHalfGapCorrection 11 7 = 3654 := by
    norm_num [skipHalfGapCorrection, halfGapCorrection]
  have hpow : (2 : ℕ) ^ (11 + 1) = 4096 := by norm_num
  rw [hcorr, hpow] at hid
  omega

/-- And the resulting value does sit strictly between the two dyadic gaps,
so `gap_strictly_between_of_largestSkipHalf` is non-vacuous at a real row. -/
theorem gap_eleven_strictly_between (hs : 5 ≤ 11) :
    2 ^ (11 + 1) <
        (seamAdjacentCut 11 hs).remainder + (seamAdjacentCut 11 hs).overshoot ∧
      (seamAdjacentCut 11 hs).remainder + (seamAdjacentCut 11 hs).overshoot <
        2 ^ (11 + 2) :=
  gap_strictly_between_of_largestSkipHalf hs isLargestFalseRank_eleven_seven
    (by norm_num)

/-! ## 3. The vacuity finding: the landing hypothesis is not met at the
certified row

`twentyOne_mul_overshoot_add_fortyTwo_eq_skipHalfGap` and
`landing_forces_correction_window` both carry the hypothesis

    hland : seamIntegerGreedyRemainder s = 2 ^ (s + 1) + 2

`H1` never exhibits a row where `hland` holds.  It does not hold at `s = 11`,
the only row `H1` certifies, and a machine scan (`5 ≤ s ≤ 80`) finds no row
where it holds at all.  The two theorems are therefore conditional on an
unexhibited hypothesis — legitimate as a proof-by-contradiction scaffold, but
they close nothing on their own.
-/

/-- The actual greedy remainder at the certified row. -/
theorem seamIntegerGreedyRemainder_eleven : seamIntegerGreedyRemainder 11 = 2485 := by
  decide +kernel

/-- So the landing hypothesis **fails** at `s = 11`. -/
theorem landing_fails_eleven : seamIntegerGreedyRemainder 11 ≠ 2 ^ (11 + 1) + 2 := by
  rw [seamIntegerGreedyRemainder_eleven]; norm_num

/-- Consequently `twentyOne_mul_overshoot_add_fortyTwo_eq_skipHalfGap` is not
applicable at the one row `H1` certifies. -/
theorem landing_theorem_not_applicable_at_eleven :
    ¬ ∃ _h : seamIntegerGreedyRemainder 11 = 2 ^ (11 + 1) + 2, True := by
  rintro ⟨h, -⟩
  exact landing_fails_eleven h

/-! ## 4. The gap identity is not a restatement of the corpus's late identity

At `s = 11` the largest false rank `7` is genuinely *not* in the two-thirds
zone, so the corpus's `three_mul_remainder_add_overshoot_eq_exactLateGap`
does not apply and `H1`'s branch is doing real work.
-/

theorem eleven_seven_not_late : ¬ (2 * 11 < 3 * 7) := by norm_num

theorem eleven_seven_half_not_late : InHalfZone 11 7 ∧ ¬ (2 * 11 < 3 * 7) :=
  ⟨inHalfZone_eleven_seven, eleven_seven_not_late⟩

/-! ## 5. Does `H1` touch the achievement set?

It does not.  Nothing in `H1` mentions `mersenneAchievementSet`,
`SeamGreedyEventuallyRight`, or an all-right tail, so the
"`hright` combined with `1/2 ∈ mersenneAchievementSet`" failure mode cannot
arise here.  Recorded as a fact about the statement `H1` *does* prove: its
strongest unconditional output is a two-sided bound on one integer, with no
membership consequence attached.
-/

theorem headline_is_a_gap_bound_only
    {s d : ℕ} (hs : 5 ≤ s)
    (hd : IsLargestFalseRank (seamGreedyWord s) d) (hhalf : s < 2 * d) :
    2 ^ (s + 1) <
        (seamAdjacentCut s hs).remainder + (seamAdjacentCut s hs).overshoot ∧
      (seamAdjacentCut s hs).remainder + (seamAdjacentCut s hs).overshoot <
        2 ^ (s + 2) :=
  gap_strictly_between_of_largestSkipHalf hs hd hhalf

end ErdosProblems.Half.VerifyW1
