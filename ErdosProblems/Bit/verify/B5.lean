/-
Copyright (c) 2026 Will Cook. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Will Cook
-/
import ErdosProblems.Bit.R2

/-!
# B5: adversarial verification of `ErdosProblems/Bit/R2.lean`

Axiom audit plus in-kernel-language satisfiability sweep of every hypothesis
appearing in `Bit/R2.lean`.  Nothing here is a new mathematical claim; this
file exists to be *run*.
-/

namespace ErdosProblems.BitR2Verify

open ErdosProblems.BitR2
open Erdos249257
open Erdos249257.HalfCylinderIntegerGreedy

/-! ## 1. Axiom audit of the upstream reduction -/

#print axioms AngleD2.half_mem_iff_unboundedLargestSkipLate
#print axioms Erdos249257.rightBranch_remainder_succ_eq
#print axioms Erdos249257.three_mul_remainder_lt_exactLateGap
#print axioms Erdos249257.seamAdjacentCut_belowPulse_le
#print axioms Erdos249257.seamGreedy_terminal_false_iff_upperOrMiddle
#print axioms Erdos249257.mersenneAchievementSet
#print axioms Erdos249257.seamGreedyWord_succ_isLargestFalseRank_terminal_of_upperOrMiddle
#print axioms SkipD3.mem_support_iff
#print axioms largestSkipLateAt_fourteen
#print axioms BitCorr2.seamIntegerGreedyRemainder_14

/-! ## 2. Axiom audit of every theorem in `Bit/R2.lean` -/

#print axioms largestSkipLateAt_succ_of_upperOrMiddle
#print axioms not_upperOrMiddle_of_not_largestSkipLateAt_succ
#print axioms not_largestSkipLateAt_of_noLateSkip
#print axioms not_largestSkipLateAt_eleven
#print axioms not_largestSkipLateAt_twelve
#print axioms not_largestSkipLateAt_thirteen
#print axioms deficit_step
#print axioms deficit_iter
#print axioms exists_largestSkipLateAt_of_remainder_le_two_pow
#print axioms deficit_shrinks_along_rightRun
#print axioms half_mem_of_remainderReachesHalfPointCofinally
#print axioms surplus_step
#print axioms surplus_iter
#print axioms three_mul_remainder_lt_of_largestSkipLateAt
#print axioms not_surplus_run
#print axioms exists_largestSkipLateAt_of_surplus
#print axioms badRun_pins_remainder
#print axioms half_mem_of_remainderMissesHalfPointWindowCofinally

/-! ### Witnesses -/

#print axioms remainder_five
#print axioms remainder_six
#print axioms remainder_nine
#print axioms remainder_ten
#print axioms remainder_seventeen
#print axioms not_upperOrMiddle_of_mem_succ
#print axioms not_upperOrMiddle_six
#print axioms not_upperOrMiddle_nine
#print axioms deficit_step_witness
#print axioms deficit_iter_witness
#print axioms deficit_shrinks_witness
#print axioms surplus_step_witness
#print axioms surplus_iter_witness
#print axioms obeysRemainderCeiling_fourteen
#print axioms obeysRemainderCeiling_seventeen
#print axioms theoremA_witness
#print axioms theoremB_witness

/-! ## 3. Satisfiability sweep

Everything below uses the corpus's own `seamIntegerGreedyRemainder`,
`SkipD3.gb` and `noLateSkip` — no re-implementation. -/

/-- The terminal bit of row `s + 1`; `true` is exactly a right branch at `s`
(`seamGreedy_terminal_false_iff_upperOrMiddle`). -/
def rightBranchB (s : ℕ) : Bool := (SkipD3.gb (s + 1)).getD (s - 2) false

/-- Theorem A's hypothesis, as a Bool. -/
def belowHalfB (s : ℕ) : Bool := decide (seamIntegerGreedyRemainder s ≤ 2 ^ s)

/-- Theorem B's hypothesis (`rem s = 2 ^ s + σ` with `2 * s ≤ σ`), as a Bool. -/
def surplusBigB (s : ℕ) : Bool := decide (2 ^ s + 2 * s ≤ seamIntegerGreedyRemainder s)

/-- `ObeysRemainderCeiling`, as a Bool. -/
def ceilingB (s : ℕ) : Bool :=
  decide (3 * seamIntegerGreedyRemainder s < 7 * 2 ^ s + 4)

/-- The half-point window `(2 ^ s, 2 ^ s + 2 * s)` of `badRun_pins_remainder`. -/
def inWindowB (s : ℕ) : Bool :=
  decide (2 ^ s < seamIntegerGreedyRemainder s) &&
    decide (seamIntegerGreedyRemainder s < 2 ^ s + 2 * s)

def rows (lo hi : ℕ) : List ℕ := (List.range (hi + 1 - lo)).map (· + lo)
def hits (p : ℕ → Bool) (lo hi : ℕ) : List ℕ := (rows lo hi).filter p
def count (p : ℕ → Bool) (lo hi : ℕ) : ℕ := (hits p lo hi).length

/-- Longest run of consecutive rows in `[lo, hi]` on which `p` holds. -/
def longestRun (p : ℕ → Bool) (lo hi : ℕ) : ℕ :=
  ((rows lo hi).foldl (fun (acc : ℕ × ℕ) s =>
      if p s then (acc.1 + 1, max acc.2 (acc.1 + 1)) else (0, acc.2)) (0, 0)).2

-- Sanity: the corpus values proved inside `Bit/R2.lean`.
#eval (seamIntegerGreedyRemainder 5, seamIntegerGreedyRemainder 6,
       seamIntegerGreedyRemainder 9, seamIntegerGreedyRemainder 10,
       seamIntegerGreedyRemainder 17)   -- expect (71, 34, 541, 1135, 156085)

-- BAD ROWS: `noLateSkip s = true` certifies `¬ LargestSkipLateAt s`.
#eval hits noLateSkip 5 400                 -- expect [5, 11, 12, 13]
#eval longestRun noLateSkip 5 400           -- longest certified bad run

-- THEOREM A hypothesis `rem s ≤ 2 ^ s`.
#eval (count belowHalfB 5 400, 396)
#eval (hits belowHalfB 5 60)
#eval longestRun (fun s => !belowHalfB s) 5 400   -- longest gap between hits

-- THEOREM B hypothesis `rem s ≥ 2 ^ s + 2 * s`.
#eval (count surplusBigB 5 400, 396)
#eval longestRun (fun s => !surplusBigB s) 5 400

-- THE CEILING `3 * rem s < 7 * 2 ^ s + 4`: failures.
#eval hits (fun s => !ceilingB s) 5 400     -- expect []

-- THE HALF-POINT WINDOW of `badRun_pins_remainder`: occupancy.
#eval hits inWindowB 5 400                  -- expect [8]

-- RIGHT BRANCHES and their longest run (the `hblock` of `not_surplus_run`).
#eval (count rightBranchB 5 400, 396)
#eval longestRun rightBranchB 5 400

-- `badRun_pins_remainder` hypothesis: all of `[N+1, 3N+2]` bad.
-- `noLateSkip` certifies badness, so a hit here would be a genuine instance.
#eval hits (fun N => ((rows (N + 1) (3 * N + 2)).all noLateSkip)) 5 130

-- `not_surplus_run` right-branch block: right branch at `N + j` for all `j < 2N+2`.
#eval hits (fun N => ((rows N (3 * N + 1)).all rightBranchB)) 5 130

/-! ### The exact witness clause of `RemainderMissesHalfPointWindowCofinally` -/

/-- `5 ≤ s ∧ ObeysRemainderCeiling (3 * s + 2) ∧ ¬ inWindow s`: the property a
witness `s` of `RemainderMissesHalfPointWindowCofinally` must have. -/
def endpointWitnessB (s : ℕ) : Bool := ceilingB (3 * s + 2) && !inWindowB s

#eval (count endpointWitnessB 5 130, 126)            -- how many rows qualify
#eval hits (fun s => !endpointWitnessB s) 5 130      -- rows that FAIL to qualify

-- `SeamGreedyUpperOrMiddleAt s` holds iff the terminal bit of row `s+1` is
-- false (`seamGreedy_terminal_false_iff_upperOrMiddle`) — i.e. iff not a right
-- branch.  `Bit/R2.lean` exhibits no witness for this hypothesis of
-- `largestSkipLateAt_succ_of_upperOrMiddle`; it is nevertheless satisfiable.
#eval (count (fun s => !rightBranchB s) 5 400, 396)
#eval (hits (fun s => !rightBranchB s) 5 30)

end ErdosProblems.BitR2Verify
