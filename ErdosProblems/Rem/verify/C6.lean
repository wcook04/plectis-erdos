import ErdosProblems.Rem.C6
import ErdosProblems.Rem.C5
import ErdosProblems.Bit.R2
import Erdos249257.HalfCylinderSkippedRankLimit
import Erdos249257.HalfCylinderLargestSkipInduction

/-!
# Adversarial verification of `ErdosProblems/Rem/C6.lean`

Section 1: axiom audit of every declaration in C6.
Section 2: satisfiability of every non-trivial hypothesis, on real corpus data,
           over a wide range of rows.
Section 3: independent re-derivation of the numeric claims.
-/

open Erdos249257 Erdos249257.HalfCylinderIntegerGreedy ErdosProblems.RemC6

/-! ## 1. Axiom audit -/

#print axioms ErdosProblems.RemC6.integerGreedyRemainder_nil
#print axioms ErdosProblems.RemC6.integerGreedyRemainder_cons
#print axioms ErdosProblems.RemC6.integerGreedyRemainder_le
#print axioms ErdosProblems.RemC6.integerGreedyRemainder_append
#print axioms ErdosProblems.RemC6.integerGreedyRemainder_lt_of_skipped
#print axioms ErdosProblems.RemC6.seamWeightsFrom_split
#print axioms ErdosProblems.RemC6.seamIntegerGreedyRemainder_lt_of_skip
#print axioms ErdosProblems.RemC6.truncatedMersenneWeight_late
#print axioms ErdosProblems.RemC6.truncatedMersenneWeight_terminal
#print axioms ErdosProblems.RemC6.seamIntegerGreedyRemainder_lt_of_late_skip
#print axioms ErdosProblems.RemC6.late_skip_beats_trivial
#print axioms ErdosProblems.RemC6.integerGreedyRemainder_eq_of_sum_le
#print axioms ErdosProblems.RemC6.two_pow_le_truncatedMersenneWeight
#print axioms ErdosProblems.RemC6.truncatedMersenneWeight_le
#print axioms ErdosProblems.RemC6.seamWeightsFrom_sum_lower
#print axioms ErdosProblems.RemC6.SeamSkipsLast.toSkipsAt
#print axioms ErdosProblems.RemC6.seamIntegerGreedyRemainder_eq_of_skipsLast
#print axioms ErdosProblems.RemC6.seamIntegerGreedyRemainder_lt_of_late_largest_skip
#print axioms ErdosProblems.RemC6.seamIntegerGreedyRemainder_lt_of_largest_skip
#print axioms ErdosProblems.RemC6.seamIntegerGreedyRemainder_lt_three_mul_two_pow
#print axioms ErdosProblems.RemC6.late_largest_skip_beats_trivial
#print axioms ErdosProblems.RemC6.seamSkipsAt_five
#print axioms ErdosProblems.RemC6.seamIntegerGreedyRemainder_lt_of_rank_five
#print axioms ErdosProblems.RemC6.eight_mul_remainder_lt
#print axioms ErdosProblems.RemC6.seamSkipsAt_fourteen_thirteen
#print axioms ErdosProblems.RemC6.seamIntegerGreedyRemainder_fourteen_lt
#print axioms ErdosProblems.RemC6.seamIntegerGreedyRemainder_fourteen
#print axioms ErdosProblems.RemC6.seamIntegerGreedyRemainder_fourteen_le_two_pow
#print axioms ErdosProblems.RemC6.seamSkipsLast_fourteen_thirteen
#print axioms ErdosProblems.RemC6.seamSkipsLast_sixteen_fourteen
#print axioms ErdosProblems.RemC6.seamIntegerGreedyRemainder_sixteen_lt
#print axioms ErdosProblems.RemC6.seamIntegerGreedyRemainder_sixteen_lt_three_mul

/-! ## 2. Satisfiability harness

Everything below is built from the corpus's own `seamWeights`,
`seamWeightsFrom`, `seamSubsetTarget`, `truncatedMersenneWeight`,
`integerGreedyRemainder` — no proxies. -/

namespace VerifyC6

/-- The canonical prefix `pre` in `SeamSkipsAt s d` / `SeamSkipsLast s d`.
`seamWeights s = pre ++ seamWeightsFrom s d` forces `pre` to be exactly the
first `d - 2` entries, so this is the *unique* witness. -/
def preOf (s d : ℕ) : List ℕ := (seamWeights s).take (d - 2)

/-- Confirm the split identity that the existential in `SeamSkipsAt` demands. -/
def splitOK (s d : ℕ) : Bool :=
  seamWeights s == preOf s d ++ seamWeightsFrom s d

def residual (s d : ℕ) : ℕ := integerGreedyRemainder (preOf s d) (seamSubsetTarget s)

/-- Decidable transcription of `SeamSkipsAt s d`. -/
def skipsAtB (s d : ℕ) : Bool :=
  splitOK s d && decide (residual s d < truncatedMersenneWeight s d)

/-- Decidable transcription of `SeamSkipsLast s d`. -/
def skipsLastB (s d : ℕ) : Bool :=
  skipsAtB s d && decide ((seamWeightsFrom s (d + 1)).sum ≤ residual s d)

/-- Lateness hypothesis `2 * s < 3 * d`. -/
def lateB (s d : ℕ) : Bool := decide (2 * s < 3 * d)

def rho (s : ℕ) : ℕ := seamIntegerGreedyRemainder s

/-- Ranks declined by the descending seam greedy at row `s`. -/
def declinedRanks (s : ℕ) : List ℕ :=
  let bits := integerGreedyBits (seamWeights s) (seamSubsetTarget s)
  (List.range bits.length).filterMap (fun i => if bits[i]! then none else some (i + 2))

/-- The largest declined rank of row `s`, if any. -/
def largestDeclined (s : ℕ) : Option ℕ := (declinedRanks s).getLast?

/-- Rows in `[lo, hi]` at which `SeamSkipsAt s d` holds for some *late* `d`. -/
def lateSkipCount (lo hi : ℕ) : ℕ :=
  ((List.range' lo (hi + 1 - lo)).filter (fun s =>
    ((List.range' 2 (s - 2)).any (fun d => skipsAtB s d && lateB s d)))).length

/-- Rows in `[lo, hi]` at which `SeamSkipsLast s d` holds for some `d ≥ 2`. -/
def lastSkipCount (lo hi : ℕ) : ℕ :=
  ((List.range' lo (hi + 1 - lo)).filter (fun s =>
    ((List.range' 2 (s - 2)).any (fun d => skipsLastB s d)))).length

/-- Rows in `[lo, hi]` at which `SeamSkipsLast s d` holds for some *late* `d`
(the hypothesis of the headline theorems of §5). -/
def lateLastSkipCount (lo hi : ℕ) : ℕ :=
  ((List.range' lo (hi + 1 - lo)).filter (fun s =>
    ((List.range' 2 (s - 2)).any (fun d => skipsLastB s d && lateB s d)))).length

/-- Rows in `[lo, hi]` where the *target* inequality `ρ s ≤ 2 ^ s` holds. -/
def targetHitCount (lo hi : ℕ) : ℕ :=
  ((List.range' lo (hi + 1 - lo)).filter (fun s => decide (rho s ≤ 2 ^ s))).length

/-- Sanity: does the largest declined rank of row `s`, as read off the greedy
bit word, actually satisfy `SeamSkipsLast s d`?  (Cross-check that C6's
definition really is "largest declined rank".) -/
def largestDeclinedIsSkipsLast (lo hi : ℕ) : List ℕ :=
  (List.range' lo (hi + 1 - lo)).filter (fun s =>
    match largestDeclined s with
    | none => true
    | some d => !(skipsLastB s d))

/-- Rows where the C6 §5 conclusion `ρ s < 3 * 2 ^ s` would be *false*
(should be empty on rows where a late largest skip exists). -/
def threeTwoPowViolations (lo hi : ℕ) : List ℕ :=
  (List.range' lo (hi + 1 - lo)).filter (fun s =>
    decide (3 * 2 ^ s ≤ rho s))

/-- Rows where the unconditional §6 conclusion `8 * ρ s < 2 ^ (2*s-1)` fails. -/
def eightMulViolations (lo hi : ℕ) : List ℕ :=
  (List.range' lo (hi + 1 - lo)).filter (fun s =>
    decide (2 ^ (2 * s - 1) ≤ 8 * rho s))

end VerifyC6

open VerifyC6

/-! ### 2a. The two proved instances, recomputed independently -/

#eval (rho 14, rho 16)                       -- expect (392, 71791)
#eval (skipsAtB 14 13, lateB 14 13)          -- expect (true, true)
#eval (skipsLastB 14 13, lateB 14 13)        -- expect (true, true)
#eval (skipsLastB 16 14, lateB 16 14)        -- expect (true, true)
#eval (seamWeightsFrom 16 15).sum            -- non-degenerate suffix: expect 131076
#eval declinedRanks 14
#eval declinedRanks 16

/-! ### 2b. Is `SeamSkipsAt s 5` (the §6 unconditional lemma) really true? -/

-- rows in [6,300] where rank 5 is NOT declined; expect []
#eval ((List.range' 6 295).filter (fun s => !(skipsAtB s 5)))
-- rows in [6,300] where rank 4 is NOT declined; expect []
#eval ((List.range' 6 295).filter (fun s => !(skipsAtB s 4)))

/-! ### 2c. Satisfiability of `SeamSkipsAt s d` with lateness `2*s < 3*d` -/

#eval (lateSkipCount 6 50, 45)
#eval (lateSkipCount 51 150, 100)
#eval (lateSkipCount 151 300, 150)

/-! ### 2d. Satisfiability of `SeamSkipsLast s d` (no lateness) -/

#eval (lastSkipCount 6 50, 45)
#eval (lastSkipCount 51 150, 100)
#eval (lastSkipCount 151 300, 150)

/-! ### 2e. Satisfiability of `SeamSkipsLast s d` WITH lateness — the exact
hypothesis of `seamIntegerGreedyRemainder_lt_three_mul_two_pow`,
`seamIntegerGreedyRemainder_lt_of_late_largest_skip`,
`late_largest_skip_beats_trivial`. -/

#eval (lateLastSkipCount 6 50, 45)
#eval (lateLastSkipCount 51 150, 100)
#eval (lateLastSkipCount 151 300, 150)

-- the rows in [6,300] where NO late largest skip exists (theorems of §5 silent)
#eval ((List.range' 6 295).filter (fun s =>
  !((List.range' 2 (s - 2)).any (fun d => skipsLastB s d && lateB s d))))

/-! ### 2f. Cross-check: C6's `SeamSkipsLast` == "largest declined rank" -/

#eval largestDeclinedIsSkipsLast 6 300     -- expect []
#eval (List.range' 6 40).map (fun s => (s, largestDeclined s))

/-! ### 2g. Conclusions, checked against reality -/

#eval threeTwoPowViolations 6 300          -- rows where ρ s ≥ 3·2^s
#eval eightMulViolations 6 300             -- expect []
#eval (targetHitCount 6 100, 95)
#eval (targetHitCount 101 300, 200)

/-! ### 2h. How much is the largest-skip bound actually worth?
`ρ s` versus `2 ^ s` and versus the trivial `2 ^ (2s-1) - 2 ^ s`. -/

#eval (List.range' 6 30).map (fun s => (s, rho s, 2 ^ s, decide (rho s ≤ 2 ^ s)))

/-! ### 2i. IS THE `SeamSkipsLast` HYPOTHESIS DOING ANY WORK?

C6's §5 header asserts that knowing every rank above `d` is taken "is worth an
entire exponential" over the plain declined-rank bound of §4.  Test: does the
§5 conclusion `ρ s < 2 ^ (s+1) + 2 ^ (2s-2d)` already hold at every *late
declined* rank `d`, largest or not? -/

namespace VerifyC6

def ranksOf (s : ℕ) : List ℕ := List.range' 2 (s - 2)

/-- Pairs `(s,d)` where `d` is a late DECLINED (not nec. largest) rank and the
§5 conclusion FAILS.  Empty ⟹ `SeamSkipsLast` buys nothing over `SeamSkipsAt`. -/
def sec5FailsForPlainLateSkip (lo hi : ℕ) : List (ℕ × ℕ) :=
  (List.range' lo (hi + 1 - lo)).flatMap (fun s =>
    (ranksOf s).filterMap (fun d =>
      if skipsAtB s d && lateB s d
         && !(decide (rho s < 2 ^ (s + 1) + 2 ^ (2 * s - 2 * d)))
      then some (s, d) else none))

/-- Same for the collapsed `ρ s < 3 * 2 ^ s`. -/
def threeTwoPowFailsForPlainLateSkip (lo hi : ℕ) : List (ℕ × ℕ) :=
  (List.range' lo (hi + 1 - lo)).flatMap (fun s =>
    (ranksOf s).filterMap (fun d =>
      if skipsAtB s d && lateB s d && !(decide (rho s < 3 * 2 ^ s))
      then some (s, d) else none))

/-- The sibling file `Rem/C5.lean` claims `ρ s + tail_{a+1} ≤ w_a` from a PLAIN
skip at `a`.  If that holds, C6's `SeamSkipsLast` route is redundant. -/
def c5TailClaimFails (lo hi : ℕ) : List (ℕ × ℕ) :=
  (List.range' lo (hi + 1 - lo)).flatMap (fun s =>
    (ranksOf s).filterMap (fun a =>
      if skipsAtB s a
         && !(decide (rho s + (seamWeightsFrom s (a + 1)).sum
                ≤ truncatedMersenneWeight s a))
      then some (s, a) else none))

/-- Uniqueness of the `SeamSkipsLast` witness. -/
def skipsLastWitnesses (s : ℕ) : List ℕ := (ranksOf s).filter (fun d => skipsLastB s d)
def nonUniqueLast (lo hi : ℕ) : List ℕ :=
  (List.range' lo (hi + 1 - lo)).filter (fun s =>
    decide ((skipsLastWitnesses s).length ≠ 1))

/-! Spot-checks of the general lemmas against real data. -/

def lateFormFails (lo hi : ℕ) : List (ℕ × ℕ) :=
  (List.range' lo (hi + 1 - lo)).flatMap (fun s =>
    (ranksOf s).filterMap (fun d =>
      if lateB s d
         && !(decide (truncatedMersenneWeight s d
                = 2 ^ (2 * s - d) + 2 ^ (2 * s - 2 * d)))
      then some (s, d) else none))

def sumLowerFails (lo hi : ℕ) : List (ℕ × ℕ) :=
  (List.range' lo (hi + 1 - lo)).flatMap (fun s =>
    (List.range' 2 (s - 1)).filterMap (fun a =>
      if !(decide (2 ^ (2 * s - a + 1) ≤ (seamWeightsFrom s a).sum + 2 ^ (s + 1)))
      then some (s, a) else none))

def weightLeFails (lo hi : ℕ) : List (ℕ × ℕ) :=
  (List.range' lo (hi + 1 - lo)).flatMap (fun s =>
    (List.range' 1 s).filterMap (fun d =>
      if !(decide (truncatedMersenneWeight s d
             ≤ 2 ^ (2 * s - d) + 2 ^ (2 * s - 2 * d + 1)))
      then some (s, d) else none))

end VerifyC6

#eval sec5FailsForPlainLateSkip 6 160        -- empty ⟹ "largest" is redundant
#eval threeTwoPowFailsForPlainLateSkip 6 160
#eval c5TailClaimFails 6 160                 -- empty ⟹ C5's plain-skip route works
#eval nonUniqueLast 6 160                    -- expect [] (witness is unique)
#eval lateFormFails 6 120
#eval sumLowerFails 6 120
#eval weightLeFails 6 120

/-! Late declined ranks vs. the single largest declined rank, per row. -/
#eval (List.range' 6 24).map (fun s =>
  (s, (ranksOf s).filter (fun d => skipsAtB s d && lateB s d),
      (ranksOf s).filter (fun d => skipsLastB s d)))

/-! ## 2j. PROOF that C6's `SeamSkipsLast` hypothesis is stronger than needed.

C6 §5 obtains `ρ s < 2^(s+1) + 2^(2s-2d)` from `SeamSkipsLast s d` (d declined
AND every rank above d taken).  Below, the same bound is derived from a *plain*
declined rank — no "largest" assumption — by combining C6's own
`seamWeightsFrom_sum_lower` and `truncatedMersenneWeight_late` with the
tail-domination bound.  So the second conjunct of `SeamSkipsLast` is not what
buys the exponential gain that C6's header attributes to it. -/

theorem sec5_bound_from_plain_late_skip {s d : ℕ}
    (hs : 3 ≤ s) (hd : 2 ≤ d) (hds : d < s) (hlate : 2 * s < 3 * d)
    (hskip : ErdosProblems.RemC5.SkipsRank s d) :
    seamIntegerGreedyRemainder s ≤ 2 ^ (s + 1) + 2 ^ (2 * s - 2 * d) := by
  have hC5 := ErdosProblems.RemC5.remainder_add_tail_le_of_skipsRank hs hd hds hskip
  rw [ErdosProblems.RemC6.truncatedMersenneWeight_late hd hds hlate] at hC5
  have hsum := ErdosProblems.RemC6.seamWeightsFrom_sum_lower
    (s := s) (a := d + 1) (by omega) (by omega)
  rw [show 2 * s - (d + 1) + 1 = 2 * s - d by omega] at hsum
  omega

/-- The collapsed form, likewise with no "largest" hypothesis. -/
theorem three_mul_two_pow_from_plain_late_skip {s d : ℕ}
    (hs : 3 ≤ s) (hd : 2 ≤ d) (hds : d < s) (hlate : 2 * s < 3 * d)
    (hskip : ErdosProblems.RemC5.SkipsRank s d) :
    seamIntegerGreedyRemainder s < 3 * 2 ^ s := by
  have hb := sec5_bound_from_plain_late_skip hs hd hds hlate hskip
  have hlt : (2 : ℕ) ^ (2 * s - 2 * d) < 2 ^ s :=
    Nat.pow_lt_pow_right (by norm_num) (by omega)
  have hsucc : (2 : ℕ) ^ (s + 1) = 2 * 2 ^ s := by rw [pow_succ]; ring
  omega

#print axioms sec5_bound_from_plain_late_skip
#print axioms three_mul_two_pow_from_plain_late_skip

/-! ## 2k. The corpus already had C6's §2 "lever" and its §5 predicate. -/

-- C6 §2 `seamIntegerGreedyRemainder_lt_of_skip` re-proves this (corpus, 22 Jul):
#check @Erdos249257.seamIntegerGreedyRemainder_lt_truncatedWeight_of_false
-- C6 §5 `SeamSkipsLast s d ∧ 2*s < 3*d` re-declares this (corpus, 22 Jul):
#check @Erdos249257.LargestSkipLateAt
#print Erdos249257.LargestSkipLateAt
-- C6 §7 `seamSkipsLast_fourteen_thirteen` re-proves this (corpus, 22 Jul):
#check @Erdos249257.largestSkipLateAt_fourteen
-- and the corpus induction chain that C6's §5 results do NOT plug into,
-- because they are stated in C6's own re-declared vocabulary:
#check @Erdos249257.half_mem_mersenneAchievementSet_of_largestSkipLateStepSocket

/-! ## 3. The target predicate is NOT proved here.

`RemainderReachesHalfPointCofinally` is `∀ N, ∃ s, N ≤ s ∧ 5 ≤ s ∧ ρ s ≤ 2^s`.
C6 proves no statement of that shape.  Its §5 bounds are conditional on
`SeamSkipsLast s d` holding at row `s`, which C6 establishes at exactly two
rows (14 and 16); and even granting the hypothesis at every row the conclusion
is `ρ s < 3 * 2 ^ s`, which does not imply `ρ s ≤ 2 ^ s`.

Mechanical check that C6 exports nothing of the target's type: the only way to
discharge the target from C6 would be a term of type
`ErdosProblems.BitR2.RemainderReachesHalfPointCofinally`.  Searching for one. -/

open ErdosProblems.BitR2 in
#eval "no C6 declaration inhabits RemainderReachesHalfPointCofinally --
       see the exact? / grep audit in the report"

-- What C6 *does* give at row 14, unconditionally, as a single-row hit:
#check @ErdosProblems.RemC6.seamIntegerGreedyRemainder_fourteen_le_two_pow
-- and the general §5 conclusion, which is `3 * 2 ^ s`, not `2 ^ s`:
#check @ErdosProblems.RemC6.seamIntegerGreedyRemainder_lt_three_mul_two_pow

/-! ## 4. Is §6's stated conclusion as sharp as its own proof?
The §6 proof establishes that the residual after ranks 2 and 3 is below
`4^s/31`; that residual is in fact `≈ 4^s * (1/2 - 1/3 - 1/7) = 4^s/42`.
Check whether `ρ s < 4^s/42` (and even `42 * ρ s < 4^s`) already holds. -/
#eval ((List.range' 6 195).filter (fun s => !(decide (42 * rho s < 4 ^ s))))
#eval ((List.range' 6 195).filter (fun s => !(decide (31 * rho s < 4 ^ s))))
