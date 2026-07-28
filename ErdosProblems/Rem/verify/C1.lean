/-
Adversarial verification of ErdosProblems/Rem/C1.lean.
Axiom audit + satisfiability probes.  Not part of the paper.
-/
import ErdosProblems.Rem.C1

open Erdos249257
open Erdos249257.HalfCylinderIntegerGreedy
open ErdosProblems.RemC1

/-! ## 1. Axiom audit: every theorem in C1 -/

#print axioms ErdosProblems.RemC1.le_of_descent_of_quadrupling
#print axioms ErdosProblems.RemC1.seamSubsetTarget_quadruples
#print axioms ErdosProblems.RemC1.descent_never_breaks_trivial_ceiling
#print axioms ErdosProblems.RemC1.descent_never_breaks_quartic_ceiling
#print axioms ErdosProblems.RemC1.surplusModel_stepLaw
#print axioms ErdosProblems.RemC1.surplusModel_constraints
#print axioms ErdosProblems.RemC1.exists_persistent_surplus_model
#print axioms ErdosProblems.RemC1.surplusModel_descent_under_trivial_ceiling
#print axioms ErdosProblems.RemC1.surplusModel_descent_under_quartic_ceiling
#print axioms ErdosProblems.RemC1.band_invariant
#print axioms ErdosProblems.RemC1.band_invariant_witness
#print axioms ErdosProblems.RemC1.surplus_25
#print axioms ErdosProblems.RemC1.ascent_25
#print axioms ErdosProblems.RemC1.surplus_31
#print axioms ErdosProblems.RemC1.ascent_31
#print axioms ErdosProblems.RemC1.surplus_37
#print axioms ErdosProblems.RemC1.ascent_37
#print axioms ErdosProblems.RemC1.exists_surplus_row_off_the_right_branch
#print axioms ErdosProblems.RemC1.three_surplus_rows_off_the_right_branch
#print axioms ErdosProblems.RemC1.half_mem_of_windowMissCofinally
#print axioms ErdosProblems.RemC1.windowMiss_25
#print axioms ErdosProblems.RemC1.windowMiss_31
#print axioms ErdosProblems.RemC1.windowMiss_37
#print axioms ErdosProblems.RemC1.windowMissCofinally_witness
#print axioms ErdosProblems.RemC1.windowMiss_where_halfPoint_criterion_is_silent
#print axioms ErdosProblems.RemC1.lateAt_17
#print axioms ErdosProblems.RemC1.rowLaw_holds_16
#print axioms ErdosProblems.RemC1.surplus_16
#print axioms ErdosProblems.RemC1.rowLaw_blind_at_16
#print axioms ErdosProblems.RemC1.sufficient_bound_is_sharp

-- Imported chain, for completeness.
#print axioms Erdos249257.AngleD2.half_mem_iff_unboundedLargestSkipLate
#print axioms Erdos249257.BitR1.largestSkipLateAt_succ_of_window_miss
#print axioms Erdos249257.BitR1.remainder_step_of_not_largestSkipLateAt
#print axioms Erdos249257.BitR1.remOf_eq
#print axioms Erdos249257.BitR1.lateAt_26
#print axioms Erdos249257.BitR1.lateAt_32
#print axioms Erdos249257.BitR1.lateAt_38
#print axioms Erdos249257.SkipD3.largestSkipLateAt_of_late_skip
#print axioms ErdosProblems.BitR2.half_mem_of_remainderReachesHalfPointCofinally

/-! ## 2. Statement shapes -/

#check @ErdosProblems.RemC1.half_mem_of_windowMissCofinally
#check @ErdosProblems.RemC1.exists_surplus_row_off_the_right_branch
#check @ErdosProblems.RemC1.rowLaw_blind_at_16
#check @ErdosProblems.RemC1.le_of_descent_of_quadrupling
#print ErdosProblems.RemC1.WindowMissCofinally
#print ErdosProblems.BitR2.RemainderReachesHalfPointCofinally

/-! ## 3. SATISFIABILITY on real data.

`R s = seamIntegerGreedyRemainder s`.  `windowMiss s` is the body of
`WindowMissCofinally`; `halfPoint s` is the body of
`RemainderReachesHalfPointCofinally`. -/

def R (s : ℕ) : ℕ := seamIntegerGreedyRemainder s

/-- Body of `WindowMissCofinally` at `s`. -/
def windowMiss (s : ℕ) : Bool :=
  !(decide (R (s + 1) + 2 ^ (s + 1) + 4 ≤ 4 * R s) &&
    decide (4 * R s ≤ R (s + 1) + 2 ^ (s + 1) + 2 * s))

/-- Body of `RemainderReachesHalfPointCofinally` at `s`. -/
def halfPoint (s : ℕ) : Bool := decide (R s ≤ 2 ^ s)

/-- The one-step defect `4 R s - R (s+1) - 2^(s+1)` as an integer (may be
negative, so use `Int`). -/
def defect (s : ℕ) : Int :=
  4 * (R s : Int) - (R (s + 1) : Int) - (2 : Int) ^ (s + 1)

/-- Surplus above the half point, as an integer. -/
def surplus (s : ℕ) : Int := (R s : Int) - (2 : Int) ^ s

/-- Rows in `[lo, hi]` where the window is missed. -/
def missRows (lo hi : ℕ) : List ℕ :=
  (List.range (hi + 1 - lo)).map (· + lo) |>.filter (fun s => windowMiss s)

/-- Rows in `[lo, hi]` where the window is NOT missed (criterion silent). -/
def hitRows (lo hi : ℕ) : List ℕ :=
  (List.range (hi + 1 - lo)).map (· + lo) |>.filter (fun s => !windowMiss s)

/-- Rows in `[lo, hi]` where `R s ≤ 2 ^ s` (BitR2's criterion fires). -/
def halfRows (lo hi : ℕ) : List ℕ :=
  (List.range (hi + 1 - lo)).map (· + lo) |>.filter (fun s => halfPoint s)

/-- Longest run of consecutive non-firing rows in `[lo,hi]`. -/
def longestGap (lo hi : ℕ) : ℕ :=
  ((List.range (hi + 1 - lo)).map (· + lo)).foldl
    (fun (acc : ℕ × ℕ) s =>
      if windowMiss s then (0, acc.2) else (acc.1 + 1, max acc.2 (acc.1 + 1)))
    (0, 0) |>.2

-- (a) Is `WindowMissCofinally`'s body ever true?  How often?  Is it ALWAYS true
--     (which would make the criterion a theorem, i.e. #257 solved) or NEVER
--     true (vacuous)?
#eval missRows 3 60
#eval (missRows 3 60).length
#eval hitRows 3 60
#eval longestGap 3 60
#eval missRows 61 140
#eval (missRows 61 140).length
#eval hitRows 61 140
#eval longestGap 3 140

-- (b) Is `RemainderReachesHalfPointCofinally`'s body ever true on real data?
#eval halfRows 5 140
#eval (halfRows 5 140).length

-- (c) Surplus above the half point, per row.
#eval (List.range 60).map (fun k => (k + 5, surplus (k + 5)))

-- (d) The one-step defect, per row: the window is `[4, 2s]`.
#eval (List.range 60).map (fun k => (k + 3, defect (k + 3)))

-- (e) Independent recomputation of every numeral certificate asserted in C1.
#eval (R 16, (2:ℕ) ^ 16, decide (R 16 > 2 ^ 16))               -- surplus_16
#eval (R 17, 4 * R 16, decide (R 17 + 2 ^ 17 + 4 ≤ 4 * R 16),
        decide (4 * R 16 ≤ R 17 + 2 ^ 17 + 2 * 16))            -- rowLaw_holds_16
#eval defect 16                                                -- claimed 7, in [4,32]
#eval (R 25, (2:ℕ) ^ 25, decide (R 25 > 2 ^ 25))               -- surplus_25
#eval decide (R 26 + 2 ^ 26 + 2 * 25 < 4 * R 25)               -- ascent_25
#eval (R 31, (2:ℕ) ^ 31, decide (R 31 > 2 ^ 31))
#eval decide (R 32 + 2 ^ 32 + 2 * 31 < 4 * R 31)
#eval (R 37, (2:ℕ) ^ 37, decide (R 37 > 2 ^ 37))
#eval decide (R 38 + 2 ^ 38 + 2 * 37 < 4 * R 37)
#eval (defect 25, defect 31, defect 37)
-- BitR4 / BitR3 silence at s = 16
#eval (decide (R 16 ≤ 2 ^ 15), decide (4 * R 16 ≤ 2 ^ 17), decide (R 16 ≤ 2 ^ 16))

-- (f) The blind-spot claim at s = 16: is rank 14 really skipped in row 17,
--     and is the largest false rank of row 17 really not the top rank 16?
#eval SkipD3.gb 17
#eval (SkipD3.gb 17).getD 12 false            -- rank 14  -> should be false
#eval (List.range 15).map (fun d => (d + 2, (SkipD3.gb 17).getD d false))
#eval SkipD3.rowChk 17 14

-- (g) Do the model's own hypotheses hold?  `surplusModel c s = 2^s + c`.
#eval (List.range 40).map (fun k =>
  let s := k + 5
  let c := 2
  let f : ℕ → ℕ := fun t => 2 ^ t + c
  (s, decide (2 ^ s < f s),
      decide (f (s+1) + 2 ^ (s+1) + 4 ≤ 4 * f s),
      decide (4 * f s ≤ f (s+1) + 2 ^ (s+1) + 2 * s),
      decide (3 * f s < 7 * 2 ^ s + 4),
      decide (f s < 2 ^ s + 2 * s),
      decide (2 ^ (s+1) + 4 ≤ 4 * f s),
      decide (f s ≤ 2 ^ (s+1)),
      decide (f s ≤ seamSubsetTarget s)))

-- (h) Does the REAL remainder satisfy `StepLaw` at the rows the model does?
--     (If it did everywhere, WindowMissCofinally would be FALSE.)
#eval (List.range 40).map (fun k =>
  let s := k + 5
  (s, decide (R (s+1) + 2 ^ (s+1) + 4 ≤ 4 * R s),
      decide (4 * R s ≤ R (s+1) + 2 ^ (s+1) + 2 * s)))

-- (i) `band_invariant`'s hypothesis on real data: is `R s` ever in
--     `[2^s+2, 2^s+4]`?
#eval (List.range 60).map (fun k =>
  let s := k + 5
  (s, decide (2 ^ s + 2 ≤ R s ∧ R s ≤ 2 ^ s + 4)))
#eval ((List.range 136).map (· + 5)).filter
        (fun s => decide (2 ^ s + 2 ≤ R s ∧ R s ≤ 2 ^ s + 4))
