/-
Copyright (c) 2026 Will Cook. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Will Cook
-/
import ErdosProblems.Bit.Corr3

/-! Adversarial verification scratch file for `ErdosProblems/Bit/Corr3.lean`.

Contains no proofs of its own: an axiom audit, statement dumps, and — the point
of the exercise — `#eval` satisfiability probes that check the hypotheses of
every theorem in `Corr3.lean` against the concrete greedy data, over a wide
range of the row parameter `s`.
-/

namespace Erdos249257
namespace BitCorr3

open HalfCylinderIntegerGreedy

/-! ## 1. Axiom audit: every theorem in Corr3.lean -/

#print axioms late_iff_lateFloor_le
#print axioms runNeeded_lower_bound
#print axioms mem_of_topTaken
#print axioms topTaken_eq_false_of_notMem
#print axioms largestSkipLateAt_iff_topTaken_false
#print axioms half_mem_iff_topRun_deficient
#print axioms rowOk_of_chunk
#print axioms chunk0
#print axioms chunk1
#print axioms chunk2
#print axioms chunk3
#print axioms chunk4
#print axioms chunk5
#print axioms chunk6
#print axioms rowOk_of_block
#print axioms exists_largestFalseRank_of_rowOk
#print axioms topRun_le_twelve_block
#print axioms largestSkipLateAt_block
#print axioms topTaken_runNeeded_false_block
#print axioms topRun_deficit
#print axioms topRun_record_1148
#print axioms highAll
#print axioms largestSkipLateAt_high
#print axioms largestSkipLateAt_1148
#print axioms largestSkipLateAt_8000
#print axioms topTaken_runNeeded_false_8000
#print axioms runNeeded_8000
#print axioms topRun_deficient_witness

/-! ## 2. Full elaborated statements — hunting for hidden hypotheses -/

#check @largestSkipLateAt_iff_topTaken_false
#check @half_mem_iff_topRun_deficient
#check @topRun_le_twelve_block
#check @topRun_deficit
#check @topRun_record_1148
#check @largestSkipLateAt_high
#check @topRun_deficient_witness
#print LargestSkipLateAt
#print IsLargestFalseRank
#print topTaken
#print runNeeded
#print lateFloor
#print rowOk
#print highTable

/-! ## 3. Satisfiability probes

`topRunOf s` recomputes the length of the run of consecutive takes at the top of
row `s` directly from the concrete greedy word, in one pass, without going
through `topTaken` (which recomputes `gb s` once per index).  By definition
`topTaken s r = true ↔ r ≤ topRunOf s`, so `topTaken s (runNeeded s) = false`
— the right-hand side of `largestSkipLateAt_iff_topTaken_false` and the body of
`half_mem_iff_topRun_deficient` — holds exactly when `topRunOf s < runNeeded s`.
-/

/-- Length of the run of consecutive `true`s at the top of the concrete greedy
word of row `s`. -/
def topRunOf (s : ℕ) : ℕ :=
  (((SkipD3.gb s).reverse.findIdx? (fun x => !x)).getD 0)

/-- The largest false rank read straight off the word. -/
def d0Of (s : ℕ) : ℕ := s - 1 - topRunOf s

/-- `(s, largest false rank, top run, K, is the run maximal?)`. -/
def probe (s : ℕ) : ℕ × ℕ × ℕ × ℕ × Bool :=
  (s, d0Of s, topRunOf s, runNeeded s, decide (runNeeded s ≤ topRunOf s))

-- 3a.  The rows of `[5, 400]` at which `topTaken s (runNeeded s) = true`, i.e.
-- at which the RHS of `largestSkipLateAt_iff_topTaken_false` FAILS.  Expected:
-- exactly `5, 11, 12, 13` — matching `¬ LargestSkipLateAt` at those four rows
-- (BitR2.not_largestSkipLateAt_eleven/twelve/thirteen) and nowhere else.
#eval ((List.range 396).map (fun k => 5 + k)).filter
  (fun s => decide (runNeeded s ≤ topRunOf s))

-- 3b.  Same range, the other way round: the count of rows where the file's
-- conclusion `topTaken s (runNeeded s) = false` DOES hold.  If this were small
-- the reformulation would be describing a rare event.
#eval (((List.range 396).map (fun k => 5 + k)).filter
  (fun s => decide (topRunOf s < runNeeded s))).length

-- 3c.  How far the top run is from the run the negative branch of #257 needs,
-- on a sweep through the certified block and beyond.  Third and fourth
-- components are `r(s)` and `K(s)`.
#eval (List.range 16).map (fun k => probe (501 + 46 * k))

-- 3d.  The extremal row of the block, and its neighbours.
#eval [probe 1147, probe 1148, probe 1149]

-- 3e.  The four exceptional small rows, in full.
#eval [probe 5, probe 11, probe 12, probe 13]

-- 3f.  Every row of the block: does the tabulated `d0At` agree with a fresh
-- recomputation, and is the top run really ≤ 12?  Expected `(0, 12)`:
-- zero disagreements, maximum top run 12.
#eval
  let rows := (List.range 700).map (fun k => 501 + k)
  ((rows.filter (fun s => decide (d0At s ≠ d0Of s))).length,
    rows.foldl (fun m s => max m (topRunOf s)) 0)

-- 3g.  The high rows of `highTable`, recomputed.
#eval [probe 3500, probe 4000, probe 4500, probe 5000, probe 6000, probe 7000,
  probe 8000]

-- 3h.  `rowOk` is exactly as wide as the table: true at both ends of the block,
-- false one step past it (the table lookup defaults to `0`).
#eval (rowOk 501, rowOk 1200, rowOk 1201, rowOk 500)

-- 3i.  The two numerals the file pins.
#eval (runNeeded 1148, runNeeded 8000, topTaken 1148 12, topTaken 1148 13)

-- 3j.  The doc header's claim about `s = 5` ("its top run is 0, not K").
-- `topTaken 5 (runNeeded 5)` decides it.
#eval (topRunOf 5, runNeeded 5, topTaken 5 (runNeeded 5))

end BitCorr3
end Erdos249257
