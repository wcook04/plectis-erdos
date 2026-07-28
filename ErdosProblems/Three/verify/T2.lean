/-
Adversarial verification of ErdosProblems/Three/T2.lean.
Axiom audit + satisfiability probes + proved-vs-measured audit.
Not part of the paper.
-/
import ErdosProblems.Three.T2

open Erdos249257
open Erdos249257.HalfCylinderIntegerGreedy
open ErdosProblems.ThreeT2

/-! ## 1. Axiom audit: every theorem of T2 -/

#print axioms ErdosProblems.ThreeT2.two_pow_le_adjacentGap
#print axioms ErdosProblems.ThreeT2.adjGapExcess_spec
#print axioms ErdosProblems.ThreeT2.successorCarries_iff
#print axioms ErdosProblems.ThreeT2.three_mul_two_pow_le_of_successorCarries
#print axioms ErdosProblems.ThreeT2.middleBranch_remainder_succ_eq
#print axioms ErdosProblems.ThreeT2.upperBranch_remainder_succ_eq
#print axioms ErdosProblems.ThreeT2.upperBranch_remainder_succ_eq'
#print axioms ErdosProblems.ThreeT2.middleCond_iff
#print axioms ErdosProblems.ThreeT2.upperOrMiddle_iff
#print axioms ErdosProblems.ThreeT2.branch_trichotomy
#print axioms ErdosProblems.ThreeT2.not_upperOrMiddle_iff
#print axioms ErdosProblems.ThreeT2.rightBranch_remainder_succ_eq_of_triggers
#print axioms ErdosProblems.ThreeT2.remainder_succ_perturbed_doubling
#print axioms ErdosProblems.ThreeT2.remainder_succ_perturbed_doubling_of_not_carry
#print axioms ErdosProblems.ThreeT2.three_mul_adjGapExcess_eq_exactLateGap
#print axioms ErdosProblems.ThreeT2.twentyOne_mul_adjGapExcess_eq_skipHalfGap
#print axioms ErdosProblems.ThreeT2.skipHalfGapCorrection_le
#print axioms ErdosProblems.ThreeT2.twentyOne_mul_carryDefect_le
#print axioms ErdosProblems.ThreeT2.four_pow_cube_le_of_late
#print axioms ErdosProblems.ThreeT2.hitAt_succ_of_successorCarries
#print axioms ErdosProblems.ThreeT2.half_mem_of_carryCofinally
#print axioms ErdosProblems.ThreeT2.successorCarries_of_numeric
#print axioms ErdosProblems.ThreeT2.shadow_of_not_carry_run
#print axioms ErdosProblems.ThreeT2.half_le_y
#print axioms ErdosProblems.ThreeT2.hitAt_iff_y_le_one
#print axioms ErdosProblems.ThreeT2.y_succ
#print axioms ErdosProblems.ThreeT2.y_shadow
#print axioms ErdosProblems.ThreeT2.y_shadow_interval
#print axioms ErdosProblems.ThreeT2.two_pow_mul_y
#print axioms ErdosProblems.ThreeT2.shadow_interval_covers
#print axioms ErdosProblems.ThreeT2.exists_no_carry_above_of_not_half_mem
#print axioms ErdosProblems.ThreeT2.shadow_of_not_half_mem
#print axioms ErdosProblems.ThreeT2.not_successorCarries_of_four_mul_remainder_lt
#print axioms ErdosProblems.ThreeT2.middleTrigger_of_four_mul_remainder_lt
#print axioms ErdosProblems.ThreeT2.middleBranch_remainder_succ_eq_of_small

-- Witness section
#print axioms ErdosProblems.ThreeT2.Witness.remainder_thirteen
#print axioms ErdosProblems.ThreeT2.Witness.remainder_fourteen
#print axioms ErdosProblems.ThreeT2.Witness.remainder_fifteen
#print axioms ErdosProblems.ThreeT2.Witness.remainder_nineteen
#print axioms ErdosProblems.ThreeT2.Witness.remainder_twenty
#print axioms ErdosProblems.ThreeT2.Witness.remainder_twentyfive
#print axioms ErdosProblems.ThreeT2.Witness.remainder_twentysix
#print axioms ErdosProblems.ThreeT2.Witness.remainder_thirtyone
#print axioms ErdosProblems.ThreeT2.Witness.remainder_thirtytwo
#print axioms ErdosProblems.ThreeT2.Witness.middleTrigger_fourteen
#print axioms ErdosProblems.ThreeT2.Witness.not_successorCarries_fourteen
#print axioms ErdosProblems.ThreeT2.Witness.belowPulse_fourteen
#print axioms ErdosProblems.ThreeT2.Witness.right_triggers_nine
#print axioms ErdosProblems.ThreeT2.Witness.belowPulse_nine
#print axioms ErdosProblems.ThreeT2.Witness.successorCarries_thirteen
#print axioms ErdosProblems.ThreeT2.Witness.successorCarries_nineteen
#print axioms ErdosProblems.ThreeT2.Witness.successorCarries_twentyfive
#print axioms ErdosProblems.ThreeT2.Witness.successorCarries_thirtyone
#print axioms ErdosProblems.ThreeT2.Witness.carry_rows
#print axioms ErdosProblems.ThreeT2.Witness.carryDefect_thirteen
#print axioms ErdosProblems.ThreeT2.Witness.carryDefect_nineteen
#print axioms ErdosProblems.ThreeT2.Witness.carryDefect_twentyfive
#print axioms ErdosProblems.ThreeT2.Witness.carryDefect_thirtyone
#print axioms ErdosProblems.ThreeT2.Witness.carryDefect_thirteen_large
#print axioms ErdosProblems.ThreeT2.Witness.adjGapExcess_late_bound_fifteen
#print axioms ErdosProblems.ThreeT2.Witness.carryDefect_bound_fifteen
#print axioms ErdosProblems.ThreeT2.Witness.isLargestFalseRank_thirteen_seven
#print axioms ErdosProblems.ThreeT2.Witness.isLargestFalseRank_fifteen_fourteen
#print axioms ErdosProblems.ThreeT2.Witness.adjGapExcess_fifteen
#print axioms ErdosProblems.ThreeT2.Witness.adjGapExcess_thirteen
#print axioms ErdosProblems.ThreeT2.Witness.abovePulse_thirteen
#print axioms ErdosProblems.ThreeT2.Witness.carryDefect_thirteen_forces_low_rank
#print axioms ErdosProblems.ThreeT2.Witness.hitAt_fourteen
#print axioms ErdosProblems.ThreeT2.Witness.remainder_sixteen
#print axioms ErdosProblems.ThreeT2.Witness.remainder_eighteen
#print axioms ErdosProblems.ThreeT2.Witness.carryFree_run_fourteen
#print axioms ErdosProblems.ThreeT2.Witness.shadow_witness
#print axioms ErdosProblems.ThreeT2.Witness.y_shadow_witness

-- Imported chain that the #257 claim rests on.
#print axioms ErdosProblems.BitR2.half_mem_of_remainderReachesHalfPointCofinally
#print axioms Erdos249257.AngleD2.half_mem_iff_unboundedLargestSkipLate
#print axioms Erdos249257.HalfCylinderIntegerGreedy.PerturbedFamily.AdjacentCut.nextRemainder_trichotomy
#print axioms ErdosProblems.HalfH1.twentyOne_mul_remainder_add_overshoot_eq_skipHalfGap
#print axioms Erdos249257.three_mul_remainder_add_overshoot_eq_exactLateGap

/-! ## 2. Statement shapes: what is actually quantified -/

#check @ErdosProblems.ThreeT2.half_mem_of_carryCofinally
#check @ErdosProblems.ThreeT2.shadow_of_not_half_mem
#check @ErdosProblems.ThreeT2.y_shadow
#check @ErdosProblems.ThreeT2.remainder_succ_perturbed_doubling
#check @ErdosProblems.ThreeT2.twentyOne_mul_carryDefect_le
#print ErdosProblems.ThreeT2.CarryCofinally
#print ErdosProblems.ThreeT2.MiddleTrigger
#print ErdosProblems.ThreeT2.adjGapExcess
#print Erdos249257.HalfCylinderIntegerGreedy.PerturbedFamily.AdjacentCut.successorCarries
#print ErdosProblems.BitR2.RemainderReachesHalfPointCofinally

/-! ## 3. Is the "new" criterion actually new, or strictly stronger?

`CarryCofinally` implies `RemainderReachesHalfPointCofinally`, by exactly the
route T2 itself uses.  So T2's criterion is a *special case* of `Bit/R2`'s, not
a complement to it: anything that discharges `CarryCofinally` already
discharges the weaker hypothesis.  Proved here, not asserted. -/

theorem carryCofinally_imp_halfPoint
    (h : ErdosProblems.ThreeT2.CarryCofinally) :
    ErdosProblems.BitR2.RemainderReachesHalfPointCofinally := by
  intro N
  obtain ⟨s, hs1, hs5, hc⟩ := h (max N 5)
  exact ⟨s + 1, by omega, by omega, hitAt_succ_of_successorCarries hs5 hc⟩

#print axioms carryCofinally_imp_halfPoint

/-! ## 4. SATISFIABILITY on real data.

`R s = seamIntegerGreedyRemainder s` via the computable `BitR3.rem`. -/

def R (s : ℕ) : ℕ := ErdosProblems.BitR3.rem s

/-- Necessary condition for a carry (`three_mul_two_pow_le_of_successorCarries`,
contrapositive of `not_successorCarries_of_four_mul_remainder_lt`). -/
def carryNec (s : ℕ) : Bool := decide (3 * 2 ^ (s + 1) ≤ 4 * R s)

/-- Sufficient condition for a carry (`successorCarries_of_numeric`). -/
def carrySuf (s : ℕ) : Bool :=
  decide (R (s + 1) + 2 ^ (s + 1) + 4 + 2 * (s - 2) < 4 * R s) &&
  decide (R (s + 1) + 2 * (s - 2) < 4 * R s + 2 ^ (s + 1))

/-- Sufficient condition for `MiddleTrigger`. -/
def midSuf (s : ℕ) : Bool := decide (4 * R s < 2 ^ (s + 1) + 4)

/-- Necessary condition for `MiddleTrigger` (`belowPulse ≤ 2 (s-2)`). -/
def midNec (s : ℕ) : Bool := decide (4 * R s < 2 ^ (s + 1) + 4 + 2 * (s - 2))

/-- Body of `RemainderReachesHalfPointCofinally` at `s`: a hit. -/
def hitAt (s : ℕ) : Bool := decide (R s ≤ 2 ^ s)

def rows (lo hi : ℕ) : List ℕ := (List.range (hi + 1 - lo)).map (· + lo)

def filt (p : ℕ → Bool) (lo hi : ℕ) : List ℕ := (rows lo hi).filter p

-- (a) Does the carry EVER fire?  How often, and out to how far?
#eval filt carrySuf 5 60
#eval (filt carrySuf 5 60).length
#eval filt carrySuf 61 160
#eval (filt carrySuf 61 160).length
#eval (filt carrySuf 5 160).length

-- (b) Does the carry FAIL to fire?  (If it always fired, `CarryCofinally`
--     would be a theorem and #257 would be resolved.)
#eval filt (fun s => !carrySuf s) 5 60
#eval (filt (fun s => !carrySuf s) 5 160).length

-- (c) Do the necessary and sufficient carry tests agree on all observed rows?
--     If yes, the carry set is pinned exactly on this range.
#eval filt (fun s => carryNec s != carrySuf s) 5 160
#eval (filt carryNec 5 160).length

-- (d) `MiddleTrigger`: both truth values, over the range.
#eval filt midSuf 5 160
#eval (filt midSuf 5 160).length
#eval filt (fun s => midNec s != midSuf s) 5 160

-- (e) Right branch = neither trigger.  Does it dominate?
#eval (filt (fun s => !carryNec s && !midNec s) 5 160).length

-- (f) Hits (`RemainderReachesHalfPointCofinally`'s body) vs carry-successors.
--     If the hit set is strictly larger, `CarryCofinally` is strictly stronger.
#eval filt hitAt 5 160
#eval (filt hitAt 5 160).length
#eval filt (fun s => carrySuf s) 5 160 |>.map (· + 1)
-- hits that are NOT the successor of a carry row:
#eval filt (fun s => hitAt s && !(decide (5 ≤ s) && carrySuf (s - 1))) 6 160

-- (g) Longest observed carry-free run in [5,160] (the shadowing horizon).
#eval ((rows 5 160).foldl
  (fun (acc : ℕ × ℕ) s =>
    if carrySuf s then (0, acc.2) else (acc.1 + 1, max acc.2 (acc.1 + 1)))
  (0, 0)).2

/-! ## 5. The carry defect `4 g s + q s`, recomputed independently.

On a carry row `ρ (s+1) + 3 * 2 ^ (s+1) + (4 g + q) = 4 ρ s`, so the defect is
`4 ρ s - ρ (s+1) - 3 * 2 ^ (s+1)`.  This reproduces T2's four kernel numbers
without going through any of T2's lemmas. -/

def carryDefect (s : ℕ) : Int :=
  4 * (R s : Int) - (R (s + 1) : Int) - 3 * (2 : Int) ^ (s + 1)

#eval (carryDefect 13, carryDefect 19, carryDefect 25, carryDefect 31)
#eval (filt carrySuf 5 60).map (fun s => (s, carryDefect s))

/-- Normalised defect `(4 g + q) / 2 ^ (s+2)` as a Float, on carry rows: this is
the deviation of the third branch from `y ↦ 2 y - 2` in `y`. -/
def carryDefectNorm (s : ℕ) : Float :=
  Float.ofInt (carryDefect s) / Float.ofNat (2 ^ (s + 2))

#eval (filt carrySuf 5 60).map (fun s => (s, carryDefectNorm s))

/-! ## 6. Is `twentyOne_mul_carryDefect_le` sharper than the trivial bound?

The carry branch itself gives `4 g + q ≤ 2 ^ (s+1)` (from
`upperBranch_remainder_succ_eq`), so `21 (4 g + q) ≤ 21 * 2 ^ (s+1)`.  Compare
that with T2's `128 * 4 ^ (s-d) + 42 s + 160` at the certified `(s,d)` pairs. -/

def t2Bound (s d : ℕ) : ℕ := 128 * 4 ^ (s - d) + 42 * s + 160
def trivBound (s : ℕ) : ℕ := 21 * 2 ^ (s + 1)

-- s = 13, d = 7 (bottom of the half zone, certified in T2).
#eval (t2Bound 13 7, trivBound 13, 21 * carryDefect 13,
       decide (t2Bound 13 7 < trivBound 13))
-- s = 15, d = 14 (late row, certified in T2).
#eval (t2Bound 15 14, trivBound 15, decide (t2Bound 15 14 < trivBound 15))
-- Where in the half zone does T2's bound actually beat the trivial one?
#eval (rows 8 40).flatMap (fun s =>
  (rows ((s + 2) / 2) (s - 1)).filter (fun d =>
    decide (s < 2 * d) && decide (t2Bound s d < trivBound s)) |>.map (fun d => (s, d)))
#eval (rows 8 40).map (fun s =>
  (s, (rows ((s + 2) / 2) (s - 1)).filter (fun d =>
        decide (s < 2 * d) && !decide (t2Bound s d < trivBound s)) |>.length))

/-! ## 7. Every numeral T2 asserts, recomputed from `BitR3.rem` alone -/

#eval (R 9, R 10, R 13, R 14, R 15, R 16, R 17, R 18, R 19, R 20)
#eval (R 25, R 26, R 31, R 32)
-- belowPulse 14 = 3 : ρ15 + p = 4 ρ14 + 2^15
#eval (4 * R 14 + 2 ^ 15 - R 15)
-- belowPulse 9 = 1 : ρ10 + 2^10 + p + 4 = 4 ρ9
#eval (4 * R 9 - R 10 - 2 ^ 10 - 4)
-- adjGapExcess 13 = 2760, abovePulse 13 = 4 :  4 g + q = 11044
#eval (carryDefect 13, (carryDefect 13 - 4) / 4)
-- 21 * g 13 = skipHalfGapCorrection 13 7
#eval (ErdosProblems.HalfH1.skipHalfGapCorrection 13 7, 21 * 2760)
-- 3 * g 15 = 2 * 4 ^ (15 - 14) + 4 = 12, so g 15 = 4
#eval (2 * 4 ^ (15 - 14) + 4, 3 * 4)
-- shadow_witness numbers M = 15, D = 1241
#eval (R 19 + 2 ^ 19 + 15 * 2 ^ 20 + 1241, 4 ^ 5 * R 14 + 2 ^ 24)
-- carry-free run [14,19): none of 14..18 carries, 13 and 19 do
#eval (rows 13 19).map (fun s => (s, carryNec s, carrySuf s))
-- y_shadow displacement at the witness run: δ = D / 2 ^ (N+2k+1) ≤ (N+1)/2 ^ (N+1)
#eval (Float.ofNat 1241 / Float.ofNat (2 ^ 25),
       Float.ofNat 15 / Float.ofNat (2 ^ 15))

/-! ## 7b. Row 13 is NOT the worst carry row: row 5 is worse.

T2 headlines `s = 13` as the row where the conjugacy is "quantitatively false".
Row `5`, also a carry row and also inside T2's range `s ≥ 5`, has a *larger*
normalised defect. -/

#eval (R 5, R 6, carryDefect 5)
/-- Deviation of the third branch from `u ↦ 2 u - 3`, in `u`: `E / 2 ^ (s+1)`. -/
def defectInU (s : ℕ) : Float :=
  Float.ofInt (carryDefect s) / Float.ofNat (2 ^ (s + 1))
#eval (filt carrySuf 5 60).map (fun s => (s, defectInU s))

/-! ## 8. What is NOT discharged.

Two hypotheses in T2 are left open, not one as its "Non-vacuity" section says:

* `CarryCofinally` — open (T2 says so).
* `hnot : (1/2 : ℝ) ∉ mersenneAchievementSet`, the hypothesis of
  `exists_no_carry_above_of_not_half_mem` and `shadow_of_not_half_mem`.  That is
  exactly the negative branch of Erdős #257 and no instance is exhibited; those
  two theorems are conditional on an open problem and could be vacuous.

Neither `1/2 ∈ mersenneAchievementSet` nor
`RemainderReachesHalfPointCofinally` is inhabited anywhere in T2.  The
following two `example`s only restate the implications; they do not close
them. -/

example : ErdosProblems.ThreeT2.CarryCofinally →
    (1 / 2 : ℝ) ∈ mersenneAchievementSet :=
  ErdosProblems.ThreeT2.half_mem_of_carryCofinally

example (hnot : (1 / 2 : ℝ) ∉ mersenneAchievementSet) :
    ∃ N : ℕ, 5 ≤ N ∧ ∀ s : ℕ, N ≤ s → ∀ h : 5 ≤ s,
      ¬ (seamAdjacentCut s h).successorCarries :=
  ErdosProblems.ThreeT2.exists_no_carry_above_of_not_half_mem hnot

#eval "T2 proves neither CarryCofinally nor 1/2 in mersenneAchievementSet; \
#257 is NOT resolved by T2."
