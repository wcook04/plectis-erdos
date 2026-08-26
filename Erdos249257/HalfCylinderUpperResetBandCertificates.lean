import Erdos249257.HalfCylinderMiddleCarryLowerBound

namespace Erdos249257

open HalfCylinderIntegerGreedy

/-!
# Finite upper-reset forbidden-band certificates

This module computes the first nontrivial segment of the exact arithmetic
producer `SeamUpperResetDyadicBandEscape`.  It is intentionally stated in
the producer's own coordinates, so that a successful finite check extends
the endpoint-facing route rather than introducing another conditional
socket.  The cofinal continuation should reuse
`upperResetCharge_signedDistance_eq_remainderBoundary` and
`producerCarry_insert_seamAboveSupport_eq_neg_upperCoordinate`; completing
the producer feeds `half_mem_mersenneAchievementSet_of_upperResetDyadicBandEscape`.
-/

/-! ## Exact floor-coordinate bridge -/

/-- On an upper transition, the next greedy floor error absorbs precisely
the pulse of the old above word.  This is the floor-error form of the same
reset whose integer form is `seamUpperBranch_remainder_add_resetCharge_eq`. -/
theorem seamUpperBranch_nextFloorError_add_abovePulse_eq
    (s : ℕ) (hs : 5 ≤ s)
    (hcarry : (seamAdjacentCut s hs).successorCarries) :
    seamGreedyFloorError (s + 1) +
        ((seamAdjacentCut s hs).abovePulse : ℚ) =
      4 * seamAboveFloorError s hs := by
  unfold seamGreedyFloorError seamAboveFloorError
  rw [seamGreedyWord_succ_eq_upperBranch s hs hcarry,
    seamWordFloorError_extend_false (by omega)]
  change
    (4 * seamWordFloorError (seamAdjacentCut s hs).above -
        ((seamAdjacentCut s hs).abovePulse : ℚ)) +
      ((seamAdjacentCut s hs).abovePulse : ℚ) =
        4 * seamWordFloorError (seamAdjacentCut s hs).above
  ring

/-- The rationally corrected upper charge is the integer reset charge plus
the next floor error.  Thus the integer forbidden bands and the rational
floor orbit differ by one explicit, already bounded error term. -/
theorem seamUpperBranch_correctedCharge_eq_resetCharge_add_nextFloorError
    (s : ℕ) (hs : 5 ≤ s)
    (hcarry : (seamAdjacentCut s hs).successorCarries) :
    4 * (((seamAdjacentCut s hs).overshoot : ℚ) +
          seamAboveFloorError s hs) =
      (4 * (seamAdjacentCut s hs).overshoot +
          (seamAdjacentCut s hs).abovePulse : ℕ) +
        seamGreedyFloorError (s + 1) := by
  have hbalance :=
    seamUpperBranch_nextFloorError_add_abovePulse_eq s hs hcarry
  push_cast
  linarith

/-- Exact dyadic-distance translation from the upper reset charge to the
corrected floor coordinate.  This is the cofinal continuation coordinate
for `SeamUpperResetDyadicBandEscape`: it converts distance from every
dyadic boundary into a statement about `seamGreedyFloorZ (s+1)`. -/
theorem seamUpperBranch_correctedDyadicDistance_eq_floorZ
    {s j : ℕ} (hs : 5 ≤ s)
    (hcarry : (seamAdjacentCut s hs).successorCarries) :
    ((2 ^ (s - j + 1) : ℕ) : ℚ) -
        4 * (((seamAdjacentCut s hs).overshoot : ℚ) +
          seamAboveFloorError s hs) =
      seamGreedyFloorZ (s + 1) +
        ((2 ^ (s - j + 1) : ℕ) : ℚ) -
          ((2 ^ (s + 1) : ℕ) : ℚ) := by
  rw [seamGreedyFloorZ_succ_upper s hs hcarry]
  push_cast
  ring

/-- Every upper reset from row `13` through row `30` avoids every danger
band relevant to a following right run.  One exact successor-remainder
certificate is shared across all band indices in each row, rather than
recomputing the same greedy orbit separately for every `(d,j)` pair. -/
theorem seamUpperResetDyadicBandEscape_through_thirty
    (d : ℕ) (hd13 : 13 ≤ d) (hd30 : d ≤ 30)
    (hd5 : 5 ≤ d)
    (hcarry : (seamAdjacentCut d hd5).successorCarries) :
    ∀ j : ℕ, j ≤ d →
      2 ^ (d - j + 1) <
          4 * (seamAdjacentCut d hd5).overshoot +
            (seamAdjacentCut d hd5).abovePulse ∨
          4 * (seamAdjacentCut d hd5).overshoot +
              (seamAdjacentCut d hd5).abovePulse + 2 * (d + j) ≤
          2 ^ (d - j + 1) := by
  intro j hj
  rw [seamUpperReset_band_iff_successorRemainder_avoids hd5 hj hcarry]
  interval_cases d
  · have hrem : seamIntegerGreedyRemainder 14 = 392 := by decide
    rw [hrem]
    interval_cases j <;> norm_num
  · have hrem : seamIntegerGreedyRemainder 15 = 34333 := by decide
    rw [hrem]
    interval_cases j <;> norm_num
  · have hrem : seamIntegerGreedyRemainder 16 = 71791 := by decide
    rw [hrem]
    interval_cases j <;> norm_num
  · have hrem : seamIntegerGreedyRemainder 17 = 156085 := by decide
    rw [hrem]
    interval_cases j <;> norm_num
  · have hrem : seamIntegerGreedyRemainder 18 = 362187 := by decide
    rw [hrem]
    interval_cases j <;> norm_num
  · have hrem : seamIntegerGreedyRemainder 19 = 924455 := by decide
    rw [hrem]
    interval_cases j <;> norm_num
  · have hrem : seamIntegerGreedyRemainder 20 = 549353 := by decide
    rw [hrem]
    interval_cases j <;> norm_num
  · have hrem : seamIntegerGreedyRemainder 21 = 100251 := by decide
    rw [hrem]
    interval_cases j <;> norm_num
  · have hrem : seamIntegerGreedyRemainder 22 = 4595307 := by decide
    rw [hrem]
    interval_cases j <;> norm_num
  · have hrem : seamIntegerGreedyRemainder 23 = 9992613 := by decide
    rw [hrem]
    interval_cases j <;> norm_num
  · have hrem : seamIntegerGreedyRemainder 24 = 23193229 := by decide
    rw [hrem]
    interval_cases j <;> norm_num
  · have hrem : seamIntegerGreedyRemainder 25 = 59218477 := by decide
    rw [hrem]
    interval_cases j <;> norm_num
  · have hrem : seamIntegerGreedyRemainder 26 = 35546625 := by decide
    rw [hrem]
    interval_cases j <;> norm_num
  · have hrem : seamIntegerGreedyRemainder 27 = 7968765 := by decide
    rw [hrem]
    interval_cases j <;> norm_num
  · have hrem : seamIntegerGreedyRemainder 28 = 300310513 := by decide
    rw [hrem]
    interval_cases j <;> norm_num
  · have hrem : seamIntegerGreedyRemainder 29 = 664371133 := by decide
    rw [hrem]
    interval_cases j <;> norm_num
  · have hrem : seamIntegerGreedyRemainder 30 = 1583742700 := by decide
    rw [hrem]
    interval_cases j <;> norm_num
  · have hrem : seamIntegerGreedyRemainder 31 = 4187487147 := by decide
    rw [hrem]
    interval_cases j <;> norm_num

#print axioms seamUpperResetDyadicBandEscape_through_thirty
#print axioms seamUpperBranch_nextFloorError_add_abovePulse_eq
#print axioms seamUpperBranch_correctedCharge_eq_resetCharge_add_nextFloorError
#print axioms seamUpperBranch_correctedDyadicDistance_eq_floorZ

end Erdos249257
