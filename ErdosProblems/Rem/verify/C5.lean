/-
Copyright (c) 2026 Will Cook. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Will Cook
-/
import ErdosProblems.Rem.C5

/-!
# C5 verify: adversarial audit of `ErdosProblems/Rem/C5.lean`

Axiom audit plus an in-kernel-language satisfiability sweep of every
non-trivial hypothesis appearing in `Rem/C5.lean`.  Nothing here is a new
mathematical claim; this file exists to be *run*.

Every predicate below is spelled out from `C5`'s own definitions
(`SkipsRank`, `seamEnteringRemainder`) and the corpus's own
(`seamWeights`, `seamWeightsFrom`, `truncatedMersenneWeight`,
`seamSubsetTarget`, `integerGreedyRemainder`, `integerGreedyBits`,
`seamIntegerGreedyRemainder`).  No proxy is introduced.
-/

namespace ErdosProblems.RemC5Verify

open Erdos249257
open Erdos249257.HalfCylinderIntegerGreedy
open ErdosProblems.RemC5

/-! ## 1. Axiom audit — every theorem of `Rem/C5.lean` -/

-- Abstract greedy calculus
#print axioms ErdosProblems.RemC5.greedyRemainder_nil
#print axioms ErdosProblems.RemC5.greedyRemainder_cons_take
#print axioms ErdosProblems.RemC5.greedyRemainder_cons_skip
#print axioms ErdosProblems.RemC5.greedyRemainder_eq_sub_sum
#print axioms ErdosProblems.RemC5.greedyRemainder_append
#print axioms ErdosProblems.RemC5.greedyRemainder_le_of_tailDominated

-- Seam structure
#print axioms ErdosProblems.RemC5.tail_sum_succ
#print axioms ErdosProblems.RemC5.tail_sum_le_weight
#print axioms ErdosProblems.RemC5.two_mul_weight_succ_le
#print axioms ErdosProblems.RemC5.seam_chain
#print axioms ErdosProblems.RemC5.seam_tailDominated
#print axioms ErdosProblems.RemC5.four_pow_eq_two_pow
#print axioms ErdosProblems.RemC5.four_pow_le_three_mul_head
#print axioms ErdosProblems.RemC5.target_le_two_mul_head

-- The positive bounds
#print axioms ErdosProblems.RemC5.seam_remainder_bound
#print axioms ErdosProblems.RemC5.seamIntegerGreedyRemainder_add_tail_le
#print axioms ErdosProblems.RemC5.four_pow_lt_weight_mul
#print axioms ErdosProblems.RemC5.eight_mul_remainder_le

-- Sharpness / the no-go
#print axioms ErdosProblems.RemC5.head_weight_small
#print axioms ErdosProblems.RemC5.tail_sum_small
#print axioms ErdosProblems.RemC5.four_mul_two_pow_le
#print axioms ErdosProblems.RemC5.head_lt_target
#print axioms ErdosProblems.RemC5.greedyRemainder_at_head_sub_one
#print axioms ErdosProblems.RemC5.counting_bound_sharp
#print axioms ErdosProblems.RemC5.exists_admissible_capacity_remainder_gt_two_pow

-- Localised bound
#print axioms ErdosProblems.RemC5.seamWeightsFrom_drop
#print axioms ErdosProblems.RemC5.seam_remainder_split
#print axioms ErdosProblems.RemC5.remainder_add_tail_le_of_skipsRank
#print axioms ErdosProblems.RemC5.obeysCeiling_of_skipsRank
#print axioms ErdosProblems.RemC5.weight_last
#print axioms ErdosProblems.RemC5.remainder_le_of_skipsLast
#print axioms ErdosProblems.RemC5.obeysCeiling_of_skipsLast
#print axioms ErdosProblems.RemC5.consecutive_gap_ge

-- Witnesses
#print axioms ErdosProblems.RemC5.skipsRank_eight
#print axioms ErdosProblems.RemC5.obeysCeiling_eight
#print axioms ErdosProblems.RemC5.skipsRank_eleven
#print axioms ErdosProblems.RemC5.obeysCeiling_eleven
#print axioms ErdosProblems.RemC5.skipsRank_twelve
#print axioms ErdosProblems.RemC5.obeysCeiling_twelve
#print axioms ErdosProblems.RemC5.ceiling_at_bad_rows
#print axioms ErdosProblems.RemC5.counting_bound_sharp_eight

/-! ## 2. Decidability of `C5`'s own hypothesis predicate -/

instance decSkipsRank (s a : ℕ) : Decidable (SkipsRank s a) :=
  inferInstanceAs (Decidable (seamEnteringRemainder s a < truncatedMersenneWeight s a))

def rows (lo hi : ℕ) : List ℕ := (List.range (hi + 1 - lo)).map (· + lo)
def hits (p : ℕ → Bool) (lo hi : ℕ) : List ℕ := (rows lo hi).filter p
def count (p : ℕ → Bool) (lo hi : ℕ) : ℕ := (hits p lo hi).length

/-- `SkipsRank s a`, as a Bool. -/
def skipsB (s a : ℕ) : Bool := decide (SkipsRank s a)

/-- The slack side-condition of `obeysCeiling_of_skipsRank`, verbatim. -/
def slackB (s a : ℕ) : Bool :=
  decide (3 * truncatedMersenneWeight s a
    < 7 * 2 ^ s + 4 + 3 * (seamWeightsFrom s (a + 1)).sum)

/-- Both hypotheses of `obeysCeiling_of_skipsRank` at `(s, a)`. -/
def fireB (s a : ℕ) : Bool := skipsB s a && slackB s a

/-- `Bit/R2.ObeysRemainderCeiling s`, as a Bool. -/
def ceilingB (s : ℕ) : Bool :=
  decide (3 * seamIntegerGreedyRemainder s < 7 * 2 ^ s + 4)

/-- The ranks of row `s` that `C5`'s `SkipsRank` declares skipped. -/
def skippedRanks (s : ℕ) : List ℕ := hits (skipsB s) 2 (s - 1)

/-- The ranks at which `obeysCeiling_of_skipsRank` actually fires at row `s`. -/
def firingRanks (s : ℕ) : List ℕ := hits (fireB s) 2 (s - 1)

/-! ## 3. Faithfulness: is `SkipsRank` really "the greedy declines rank `a`"?

`SkipsRank s a` is defined from `seamEnteringRemainder`, i.e. from a `take`.
Independent cross-check against the corpus's `integerGreedyBits`: the bit the
greedy actually assigns to rank `a` of row `s` sits at index `a - 2`. -/

def greedyBitAt (s a : ℕ) : Bool :=
  (integerGreedyBits (seamWeights s) (seamSubsetTarget s)).getD (a - 2) true

def faithfulAt (s : ℕ) : Bool := (rows 2 (s - 1)).all (fun a => skipsB s a == !greedyBitAt s a)

-- `true` means: on every row of `[3, 90]`, `SkipsRank s a` holds exactly when the
-- corpus greedy assigns `false` to rank `a`.  So `SkipsRank` is not a proxy.
#eval (rows 3 90).all faithfulAt

/-! ## 4. Sanity against the values `C5` proves in the kernel -/

#eval (seamWeights 8, seamWeights 11)      -- expect C5's `seamWeights_eight/_eleven`
#eval ((seamWeightsFrom 11 8).sum, (seamWeightsFrom 12 8).sum)   -- expect (28756, 123221)
#eval (seamSubsetTarget 8, seamSubsetTarget 11, seamSubsetTarget 12)
#eval integerGreedyRemainder (seamWeights 8) (truncatedMersenneWeight 8 2 - 1)  -- expect 4443
#eval (skipsB 8 7, skipsB 11 7, skipsB 12 7)   -- expect (true, true, true)

/-! ## 5. SATISFIABILITY of `SkipsRank` — the hypothesis of
`remainder_add_tail_le_of_skipsRank`, `obeysCeiling_of_skipsRank`. -/

-- Rows of `[3, 60]` that skip NO rank at all (hypothesis unsatisfiable there).
#eval hits (fun s => (skippedRanks s).isEmpty) 3 60          -- expect [3] only
-- How many rows in `[3, 120]` skip at least one rank.
#eval (count (fun s => !(skippedRanks s).isEmpty) 3 120, 118)
-- The actual skipped ranks, low rows.
#eval (rows 4 24).map (fun s => (s, skippedRanks s))
-- Skipped-rank counts at large rows.
#eval (rows 100 108).map (fun s => (s, (skippedRanks s).length))

/-! ## 6. SATISFIABILITY of `SkipsRank s (s - 1)` — hypothesis of
`remainder_le_of_skipsLast` / `obeysCeiling_of_skipsLast`. -/

#eval hits (fun s => skipsB s (s - 1)) 4 120
#eval (count (fun s => skipsB s (s - 1)) 4 120, 117)

/-! ## 7. Does `obeysCeiling_of_skipsRank` ever FIRE?
Both hypotheses (`SkipsRank` and the slack bound) at some rank. -/

-- Rows of `[3, 120]` where NO rank satisfies both hypotheses.
#eval hits (fun s => (firingRanks s).isEmpty) 3 120          -- expect [3, 5, 13]
#eval (count (fun s => !(firingRanks s).isEmpty) 3 120, 118)
#eval (rows 6 20).map (fun s => (s, firingRanks s))
#eval (rows 100 106).map (fun s => (s, firingRanks s))

-- The ceiling itself never fails on this range, so nothing false is being derived.
#eval hits (fun s => !ceilingB s) 3 200                       -- expect []

/-! ## 8. The unconditional bound `eight_mul_remainder_le`, and how far it is
from the truth and from the sibling file `Rem/C6`'s bound. -/

/-- `C5`'s conclusion `8 * rem s ≤ 4 ^ s`. -/
def c5BoundB (s : ℕ) : Bool := decide (8 * seamIntegerGreedyRemainder s ≤ 4 ^ s)

/-- `Rem/C6.eight_mul_remainder_lt`'s conclusion `8 * rem s < 2 ^ (2 * s - 1)`,
i.e. `rem s < 4 ^ s / 16` — strictly stronger than `C5`'s `rem s ≤ 4 ^ s / 8`. -/
def c6BoundB (s : ℕ) : Bool := decide (8 * seamIntegerGreedyRemainder s < 2 ^ (2 * s - 1))

/-- `Rem/C6.seamIntegerGreedyRemainder_lt_of_rank_five`: `rem s < 4 ^ s / 31`. -/
def c6RankFiveB (s : ℕ) : Bool := decide (seamIntegerGreedyRemainder s < 4 ^ s / 31)

#eval hits (fun s => !c5BoundB s) 6 160        -- expect [] : C5's bound holds
#eval hits (fun s => !c6BoundB s) 6 160        -- expect [] : C6's stronger bound also holds
#eval hits (fun s => !c6RankFiveB s) 6 160     -- expect [] : C6's much stronger bound holds too

-- How slack is `C5`'s bound?  Ratio `rem s / (4 ^ s / 8)` in parts per 10^6.
#eval (rows 6 40).map (fun s =>
  (s, (8 * 1000000 * seamIntegerGreedyRemainder s) / 4 ^ s))

-- The truth: `rem s` sits at roughly `2 ^ s`, not `4 ^ s / 8`.
-- `rem s * 1000 / 2 ^ s` (so 1000 == exactly the half point).
#eval (rows 6 40).map (fun s => (s, (1000 * seamIntegerGreedyRemainder s) / 2 ^ s))

/-! ## 9. The no-go: `counting_bound_sharp` and
`exists_admissible_capacity_remainder_gt_two_pow`. -/

/-- The capacity `C5` uses as its witness. -/
def sharpCap (s : ℕ) : ℕ := truncatedMersenneWeight s 2 - 1

/-- The remainder the descending greedy leaves at that capacity. -/
def sharpRem (s : ℕ) : ℕ := integerGreedyRemainder (seamWeights s) (sharpCap s)

/-- The witness clause of `exists_admissible_capacity_remainder_gt_two_pow`. -/
def noGoB (s : ℕ) : Bool :=
  decide (sharpCap s < seamSubsetTarget s) && decide (2 ^ s < sharpRem s)

/-- `counting_bound_sharp`'s conclusion. -/
def sharpB (s : ℕ) : Bool := decide (4 ^ s ≤ 21 * sharpRem s + 35)

#eval hits (fun s => !sharpB s) 3 160          -- expect []
#eval hits (fun s => !noGoB s) 6 160           -- expect []
-- The witness remainder as a fraction of `4 ^ s`, in parts per 10^6 (→ 1/16.66).
#eval (rows 6 40).map (fun s => (s, (1000000 * sharpRem s) / 4 ^ s))
-- And as a multiple of `2 ^ s`: the no-go margin grows without bound.
#eval (rows 6 30).map (fun s => (s, sharpRem s / 2 ^ s))

/-! ## 10. `consecutive_gap_ge` versus the corpus fact it restates.

`Erdos249257.HalfCylinderIntegerGreedy.seamWeights_gapDominates` already gives
`GapDominates (2 ^ (s + 1)) (seamWeights s)`, i.e. `2 ^ (s+1) + tail ≤ w`, which
implies `C5`'s `2 ^ (s+1) + w_{d+1} ≤ w_d`.  Check both numerically. -/

def c5GapB (s d : ℕ) : Bool :=
  decide (2 ^ (s + 1) + truncatedMersenneWeight s (d + 1) ≤ truncatedMersenneWeight s d)

def corpusGapB (s d : ℕ) : Bool :=
  decide (2 ^ (s + 1) + (seamWeightsFrom s (d + 1)).sum ≤ truncatedMersenneWeight s d)

#eval (rows 3 60).all (fun s => (rows 1 (s - 2)).all (fun d => c5GapB s d))
#eval (rows 3 60).all (fun s => (rows 1 (s - 1)).all (fun d => corpusGapB s d))

/-! ## 11. `TailDominated` / `greedyRemainder_le_of_tailDominated`: a concrete
instance of the abstract engine's hypotheses. -/

#eval (seamWeights 12).sum
#eval integerGreedyRemainder (seamWeights 12) (seamSubsetTarget 12)   -- expect 5836
#eval truncatedMersenneWeight 12 2 - (seamWeightsFrom 12 3).sum       -- the optimal head slack B

end ErdosProblems.RemC5Verify
