/-
Adversarial verification of ErdosProblems/Half/H2.lean.

Diagnostics only.  No new mathematical claims are asserted here; every
`#eval` below recomputes, from the *imported* definitions, a fact that
H2.lean asserts in prose or in a certificate.  Nothing is redeclared.
-/
import ErdosProblems.Half.H2
import Erdos249257.HalfCylinderSkippedRankLimit

namespace HalfH2Verify

open Erdos249257
open Erdos249257.HalfCylinderIntegerGreedy

/-! ## 1. Axiom audit of every theorem in H2.lean -/

#print axioms Erdos249257.HalfH2.truncatedMersenneWeight_eq_threeTerm_of_halfRank
#print axioms Erdos249257.HalfH2.seven_mul_threePowerSuffixSum_add_boundary
#print axioms Erdos249257.HalfH2.seamWeightsFrom_sum_eq_threeTerm_of_halfRank
#print axioms
  Erdos249257.HalfH2.twentyOne_mul_tailWeight_add_exactHalfGap_eq_twentyOne_mul_headWeight
#print axioms
  Erdos249257.HalfH2.twentyOne_mul_tailWeight_add_exactHalfGap_eq_twentyOne_mul_headWeight_floor
#print axioms Erdos249257.HalfH2.twentyOne_mul_largestSkipLowerWeight_add_exactHalfGap_eq_upperWeight
#print axioms Erdos249257.HalfH2.twentyOne_mul_remainder_lt_exactHalfGap
#print axioms Erdos249257.HalfH2.truncatedMersenneWeight_pred_eq_two_mul_landing
#print axioms Erdos249257.HalfH2.landing_add_tailWeight_lt_truncatedWeight
#print axioms Erdos249257.HalfH2.landing_lt_truncatedWeight
#print axioms Erdos249257.HalfH2.landing_satisfies_exactLateGap_strip
#print axioms Erdos249257.HalfH2.landing_satisfies_exactHalfGap_strip
#print axioms Erdos249257.HalfH2.isLargestFalseRank_thirteen_seven
#print axioms Erdos249257.HalfH2.thirteen_seven_halfZone
#print axioms Erdos249257.HalfH2.twentyOne_mul_remainder_thirteen_lt_exactHalfGap
#print axioms Erdos249257.HalfH2.isLargestFalseRank_sixtyOne_sixty
#print axioms Erdos249257.HalfH2.largestSkipHalfAt_sixtyOne
#print axioms Erdos249257.HalfH2.largestSkipHalfAt_thirteen
#print axioms Erdos249257.HalfH2.seamIntegerGreedyRemainder_eq_of_seamExcess_eq_two
#print axioms Erdos249257.HalfH2.landingRow_magnitude_consistent
#print axioms Erdos249257.HalfH2.landingRow_satisfies_exactLateGap_strip
#print axioms Erdos249257.HalfH2.landingRow_satisfies_exactHalfGap_strip

/-! ## 2. Statement audit -/

#check @Erdos249257.HalfH2.landing_add_tailWeight_lt_truncatedWeight
#check @Erdos249257.HalfH2.landingRow_magnitude_consistent
#check @Erdos249257.HalfH2.landingRow_satisfies_exactHalfGap_strip
#check @Erdos249257.HalfH2.twentyOne_mul_remainder_lt_exactHalfGap
#check @Erdos249257.HalfH2.landing_satisfies_exactLateGap_strip
#check @Erdos249257.HalfH2.landing_satisfies_exactHalfGap_strip

-- The pre-existing, unconditional corpus bound the H2 "strip invariant"
-- must beat in order to be new.
#check @seamIntegerGreedyRemainder_lt_truncatedWeight_of_false

-- The consumer that would turn `LargestSkipHalfAt` data into a solution.
#check @SkipD1.half_mem_of_cofinal_largestSkipHalfAt
#check @SkipD1.LargestSkipHalfAt
#check @Recon257.seamExcess

/-! ## 3. Independent recomputation of the concrete certificates -/

/-- Greedy bit list of row `s`; index `i` is rank `i + 2`. -/
def bits (s : ℕ) : List Bool :=
  integerGreedyBits (seamWeights s) (seamSubsetTarget s)

/-- Ranks of row `s` that the greedy declines. -/
def falseRanks (s : ℕ) : List ℕ :=
  (List.range (s - 2)).filterMap fun i =>
    if (bits s).getD i true then none else some (i + 2)

/-- Ranks of row `s` that the greedy selects. -/
def trueRanks (s : ℕ) : List ℕ :=
  (List.range (s - 2)).filterMap fun i =>
    if (bits s).getD i true then some (i + 2) else none

/-- Largest declined rank of row `s`, if any. -/
def largestFalseRank (s : ℕ) : Option ℕ := (falseRanks s).getLast?

/-- `s < 2 * d₀`, i.e. `LargestSkipHalfAt s`, computed. -/
def halfSkip (s : ℕ) : Bool :=
  match largestFalseRank s with
  | none => false
  | some d => decide (s < 2 * d)

/-- `d₀` lies in the three-term half-but-not-late zone. -/
def halfNotLate (s : ℕ) : Bool :=
  match largestFalseRank s with
  | none => false
  | some d => decide (2 * s < 4 * d) && decide (3 * d ≤ 2 * s)

section RowThirteen
-- H2 claims: largest false rank 7, lower prefix {2,3,6}.
#eval bits 13
#eval trueRanks 13
#eval falseRanks 13
#eval largestFalseRank 13
#eval (decide (2 * 13 < 4 * 7), decide (3 * 7 ≤ 2 * 13))
#eval (truncatedMersenneWeight 13 7,
       2 ^ (2 * 13 - 7) + 4 ^ (13 - 7) + 2 ^ (2 * 13 - 3 * 7))
end RowThirteen

section RowSixtyOne
-- H2 claims: largest false rank 60, with an explicitly listed prefix.
#eval largestFalseRank 61
#eval trueRanks 61
#eval falseRanks 61
-- Is rank 60 of row 61 in the NEW half zone, or in the OLD late zone?
#eval (decide (2 * 61 < 3 * 60), decide (2 * 61 < 4 * 60 ∧ 3 * 60 ≤ 2 * 61))
end RowSixtyOne

section SmallestWeight
-- `w(s, s-1) = 2 * (2^s + 2)`.
#eval (List.range 12).map fun k =>
  let s := k + 4
  (s, truncatedMersenneWeight s (s - 1), 2 * (2 ^ s + 2))
end SmallestWeight

/-! ## 4. The unproved prose claims in the H2 header -/

/-- Rows `5 ≤ s ≤ N` whose largest false rank is NOT above `s / 2`.
H2's header claims this is empty for `s ≤ 500`. -/
def halfSkipFailures (N : ℕ) : List ℕ :=
  ((List.range (N + 1)).filter fun s => decide (5 ≤ s)).filter fun s => !halfSkip s

/-- Rows `5 ≤ s ≤ N` whose largest false rank is half-but-not-late.
H2's header claims exactly `5, 11, 12, 13` for `s ≤ 500`. -/
def halfNotLateRows (N : ℕ) : List ℕ :=
  ((List.range (N + 1)).filter fun s => decide (5 ≤ s)).filter halfNotLate

/-- Rows `s ≤ N` satisfying the landing hypothesis `seamExcess s = 2`. -/
def landingRows (N : ℕ) : List ℕ :=
  (List.range (N + 1)).filter fun s =>
    decide (5 ≤ s) && decide (Recon257.seamExcess s = 2)

#eval halfSkipFailures 420
#eval halfNotLateRows 420
#eval landingRows 420

-- How far from `2` the landing excess actually runs on small rows.
#eval (List.range 40).filterMap fun s =>
  if 5 ≤ s then some (s, Recon257.seamExcess s) else none

/-! ## 5. Is the half-zone "strip invariant" actually sharper than what the
corpus already had, and is it sharper than the trivial `R < 2^(s+1) + 4`? -/

section StripStrength
-- (R 13, landing value 2^13+2, H2 half-strip RHS / 21, pre-existing corpus
--  bound w(13,7), trivial smallest-weight bound 2^14+4)
#eval (seamIntegerGreedyRemainder 13,
       2 ^ 13 + 2,
       (21 * 2 ^ 14 + 14 * 4 ^ 6 + 18 * 2 ^ 5 + 3 * 2 ^ 2 + 28) / 21,
       truncatedMersenneWeight 13 7,
       2 ^ 14 + 4)

-- Slack of the H2 half strip invariant at row 13 (positive ⇒ not tight).
#eval (21 * 2 ^ 14 + 14 * 4 ^ 6 + 18 * 2 ^ 5 + 3 * 2 ^ 2 + 28 : ℤ) -
      21 * (seamIntegerGreedyRemainder 13 : ℤ)

-- Does the actual remainder stay under `2^(s+1) + 4 = w(s, s-1)`?
#eval (List.range 36).filterMap fun s =>
  if 5 ≤ s then
    some (s, decide (seamIntegerGreedyRemainder s < 2 ^ (s + 1) + 4))
  else none

-- H2's claim that the minimal slack over `d` is attained at `d = s - 1`
-- and equals `R = 2^s + 2` exactly.
#eval (List.range 10).map fun k =>
  let s := k + 4
  (s, truncatedMersenneWeight s (s - 1) - (2 ^ s + 2), 2 ^ s + 2)
end StripStrength

end HalfH2Verify
