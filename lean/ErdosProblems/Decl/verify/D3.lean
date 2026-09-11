/-
Copyright (c) 2026 Will Cook. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Will Cook
-/
import ErdosProblems.Decl.D3

/-!
# Adversarial verification of `ErdosProblems/Decl/D3.lean`

This file is a *checker*, not a contribution.  It

1. prints the axiom dependencies of every declaration of `D3`;
2. re-`#eval`s every numeral `D3` asserts, straight off the corpus definitions,
   so the `decide +kernel` certificates are cross-checked by the evaluator;
3. `#eval`s each non-trivial hypothesis of `D3` over a wide range of real rows,
   to establish satisfiability (or expose vacuity);
4. re-derives, inside Lean, the §5 sandwich margins at the certified rows.

Nothing here is imported by the corpus.
-/

namespace ErdosProblems.DeclD3Verify

open Erdos249257 Erdos249257.HalfCylinderIntegerGreedy Erdos249257.BitCorr
open ErdosProblems.DeclD3

/-! ## 1. Axiom audit — every declaration of `D3` -/

-- §1 the first late rank
#print axioms firstLate_late
#print axioms firstLate_least
#print axioms two_le_firstLate
#print axioms firstLate_lt
#print axioms firstLate_le
#print axioms firstLate_thirteen
#print axioms firstLate_twelve
#print axioms firstLate_fourteen
#print axioms firstLate_twenty

-- §2 the glue
#print axioms seamWeightsFrom_take_succ
#print axioms earlyWeights_succ
#print axioms lateEntryRemainder_eq_greedy
#print axioms lateEntryRemainder_succ
#print axioms lateEntryRemainder_two
#print axioms lateEntryRemainder_eq_seamResidualUpto
#print axioms hhigh_iff_residualInvariant

-- §3 the two closures
#print axioms hhigh_of_declined
#print axioms hhigh_succ_of_taken
#print axioms hhigh_of_taken_run

-- §4 the master inequality
#print axioms integerGreedyRemainder_ge
#print axioms seamWeightsFrom_sum_upper
#print axioms lateEntryRemainder_add_two_pow_le
#print axioms hhigh_of_seamRemainder_lt
#print axioms two_pow_le_seamRemainder_of_not_hhigh

-- §5 at the first late rank
#print axioms two_pow_firstLate_error_le
#print axioms hhigh_firstLate_of_seamRemainder_lt
#print axioms seamRemainder_ge_of_not_hhigh_firstLate
#print axioms hhigh_firstLate_sandwich
#print axioms seamRemainder_lt_two_pow_succ_of_declined

-- §6 certificates
#print axioms Concrete.seamWeights_thirteen
#print axioms Concrete.lateEntryRemainder_thirteen_nine
#print axioms Concrete.lateEntryRemainder_thirteen_eight
#print axioms Concrete.not_hhigh_thirteen_eight
#print axioms Concrete.eight_not_late_thirteen
#print axioms Concrete.eight_lt_firstLate_thirteen
#print axioms Concrete.hhigh_thirteen
#print axioms Concrete.lateCorrection_thirteen_nine
#print axioms Concrete.hlow_thirteen
#print axioms Concrete.seamRemainder_thirteen_small
#print axioms Concrete.hhigh_thirteen_derived
#print axioms Concrete.sandwich_thirteen
#print axioms Concrete.admissible_thirteen
#print axioms Concrete.lateEntryRemainder_thirteen_ten
#print axioms Concrete.lateEntryRemainder_thirteen_eleven
#print axioms Concrete.lateEntryRemainder_thirteen_twelve
#print axioms Concrete.taken_run_thirteen
#print axioms Concrete.hhigh_thirteen_twelve
#print axioms Concrete.lateEntryRemainder_fourteen_thirteen
#print axioms Concrete.truncatedMersenneWeight_fourteen_thirteen
#print axioms Concrete.declined_fourteen_thirteen
#print axioms Concrete.lateCorrection_fourteen_thirteen
#print axioms Concrete.hhigh_fourteen_thirteen
#print axioms Concrete.seamRemainder_fourteen_lt
#print axioms Concrete.seamWeights_seven
#print axioms Concrete.firstLate_seven
#print axioms Concrete.lateEntryRemainder_seven_five
#print axioms Concrete.lateCorrection_seven_five
#print axioms Concrete.not_hlow_seven
#print axioms Concrete.hhigh_seven

-- the imported statements D3 leans on
#print axioms ThreeT4.seamRemainder_lt_two_pow_succ
#print axioms ThreeT4.seamIntegerGreedyRemainder_eq_lateGreedy
#print axioms Three.T1.not_residualInvariant
#print axioms Three.T1.seamIntegerGreedyRemainder_thirteen
#print axioms RemC6.truncatedMersenneWeight_le
#print axioms RemC6.two_pow_le_truncatedMersenneWeight

/-! ## 2. Every numeral in `D3`, re-evaluated off the corpus definitions

If any of these prints `false`, a `decide +kernel` certificate in `D3` is
inconsistent with the compiler's own evaluation of the same definitions. -/

#eval (seamWeights 13 ==
  [22369621, 9586980, 4473924, 2164802, 1065220, 528416, 263172, 131328,
    65600, 32784, 16388])
#eval (seamWeights 7 == [5461, 2340, 1092, 528, 260])
#eval (lateEntryRemainder 13 9 == 261247)
#eval (lateEntryRemainder 13 8 == 524419)
#eval (lateEntryRemainder 13 10 == 129919)
#eval (lateEntryRemainder 13 11 == 64319)
#eval (lateEntryRemainder 13 12 == 31535)
#eval (lateEntryRemainder 14 13 == 392)
#eval (lateEntryRemainder 7 5 == 263)
#eval (lateCorrection 13 9 == 340)
#eval (lateCorrection 14 13 == 4)
#eval (lateCorrection 7 5 == 20)
#eval (truncatedMersenneWeight 14 13 == 32772)
#eval (seamIntegerGreedyRemainder 13 == 15147)
-- corpus anchors from BitCorr / T4, recomputed here
#eval (lateEntryRemainder 20 14 == 67662313)
#eval (lateEntryRemainder 14 10 == 392)
#eval (lateEntryRemainder 12 9 == 63264)

/-! ## 3. SATISFIABILITY of every non-trivial hypothesis, over real rows

`d₀ s` is `firstLate s`.  All predicates below are evaluated on the genuine
corpus objects. -/

def d0 (s : ℕ) : ℕ := 2 * s / 3 + 1

/-- `hhigh` at the first late rank. -/
def hhighD0 (s : ℕ) : Bool :=
  decide (lateEntryRemainder s (d0 s) < 2 ^ (2 * s - d0 s + 1))

/-- `hlow` at the first late rank — the hypothesis of `hhigh_firstLate_sandwich`. -/
def hlowD0 (s : ℕ) : Bool :=
  decide (lateCorrection s (d0 s) ≤ lateEntryRemainder s (d0 s) % 2 ^ (s + 1))

/-- The hypothesis of `hhigh_firstLate_of_seamRemainder_lt`. -/
def suff5 (s : ℕ) : Bool :=
  decide (seamIntegerGreedyRemainder s + 2 ^ (2 * s / 3 + 2) < 2 ^ (s + 1))

/-- The conclusion. -/
def rhoSmall (s : ℕ) : Bool := decide (seamIntegerGreedyRemainder s < 2 ^ (s + 1))

/-- The hypothesis of `hhigh_of_declined` / `seamRemainder_lt_two_pow_succ_of_declined`,
at the first late rank. -/
def declinedD0 (s : ℕ) : Bool :=
  decide (lateEntryRemainder s (d0 s) < truncatedMersenneWeight s (d0 s))

/-- Is there ANY late declined rank in row `s`? -/
def someDeclinedLate (s : ℕ) : Bool :=
  (List.range s).any fun d =>
    decide (2 ≤ d) && decide (d < s) && decide (2 * s < 3 * d) &&
      decide (lateEntryRemainder s d < truncatedMersenneWeight s d)

/-- `hhigh` at an arbitrary rank — used to locate the `∀ d` failures. -/
def hhighAt (s d : ℕ) : Bool := decide (lateEntryRemainder s d < 2 ^ (2 * s - d + 1))

def rows (lo hi : ℕ) : List ℕ := (List.range (hi + 1 - lo)).map (· + lo)

/-- Rows of `[lo,hi]` where the predicate FAILS. -/
def failures (p : ℕ → Bool) (lo hi : ℕ) : List ℕ := (rows lo hi).filter fun s => !(p s)

-- Satisfiability: each of these must be NON-EMPTY for the hypothesis to be live,
-- and the failure list tells us how often it is live.
#eval ("hhigh@d0 holds on", ((rows 6 220).filter hhighD0).length, "of", (rows 6 220).length)
#eval ("hlow@d0  holds on", ((rows 6 220).filter hlowD0).length, "of", (rows 6 220).length)
#eval ("suff5    holds on", ((rows 6 220).filter suff5).length, "of", (rows 6 220).length)
#eval ("rho<2^(s+1) on   ", ((rows 6 220).filter rhoSmall).length, "of", (rows 6 220).length)
#eval ("d0 declined on   ", ((rows 6 220).filter declinedD0).length, "of", (rows 6 220).length)
#eval ("some late decline", ((rows 6 220).filter someDeclinedLate).length, "of", (rows 6 220).length)

-- EXACT failure sets (not summary statistics)
#eval ("FAIL hhigh@d0   :", failures hhighD0 6 220)
#eval ("FAIL hlow@d0    :", failures hlowD0 6 220)
#eval ("FAIL suff5      :", failures suff5 6 220)
#eval ("FAIL rho<2^(s+1):", failures rhoSmall 6 220)
#eval ("FAIL someLateDec:", failures someDeclinedLate 6 220)

/-- Every `(s,d)` with `2 ≤ d < s`, `6 ≤ s ≤ hi`, where `hhigh` fails.  This is
the `∀ d` form; `D3` claims the sole failure is `(13,8)` in its coordinates. -/
def hhighAllFailures (hi : ℕ) : List (ℕ × ℕ) :=
  (rows 6 hi).flatMap fun s =>
    ((rows 2 (s - 1)).filter fun d => !(hhighAt s d)).map fun d => (s, d)

#eval ("FAIL hhigh forall-d, s<=120 :", hhighAllFailures 120)

-- The same failures, tagged with whether the rank is LATE.  `D3`'s §6 claim is
-- that the only failure is at a rank that is NOT late.
#eval (hhighAllFailures 120).map fun p => (p, decide (2 * p.1 < 3 * p.2))

/-! ### The vacuity question for `seamRemainder_ge_of_not_hhigh_firstLate`

Its hypothesis is `¬ hhigh at firstLate s`.  If `failures hhighD0` is empty on
every row tested, that theorem has **no known instance** and is vacuous as far as
computation can tell.  (It is the contrapositive of a live implication, so this
is a presentation point, not an error.) -/
#eval ("witnesses for  ¬hhigh@d0  in [6,220] :", failures hhighD0 6 220)

/-! ## 4. The §5 margins, re-derived numerically

`hhigh_of_seamRemainder_lt` derives `R < 2^(2s-d+1)` from
`ρ + 2^(2s-2d+2) < 2^(s+1)` via
`R + 2^(s+1) ≤ ρ + 2^(2s-d+1) + 2^(2s-2d+2)`.
Slack of the master inequality, and slack of the derived bound. -/

def masterSlack (s d : ℕ) : ℤ :=
  (seamIntegerGreedyRemainder s + 2 ^ (2 * s - d + 1) + 2 ^ (2 * s - 2 * d + 2) : ℤ)
    - (lateEntryRemainder s d + 2 ^ (s + 1) : ℤ)

/-- How much room the §5 route leaves at row `s`: the derived upper bound on `R`
minus the true `R`.  Must be `≥ 0`; small values mean the route is tight. -/
def derivedMargin (s : ℕ) : ℤ :=
  let d := d0 s
  ((seamIntegerGreedyRemainder s : ℤ) + 2 ^ (2 * s - 2 * d + 2) - 2 ^ (s + 1)
      + 2 ^ (2 * s - d + 1)) - (lateEntryRemainder s d : ℤ)

#eval ("masterSlack 13 9 (>=0 required):", masterSlack 13 9)
#eval ("derivedMargin 13:", derivedMargin 13)
#eval ("min masterSlack over [6,120] at d0:",
  ((rows 6 120).map fun s => masterSlack s (d0 s)).foldl min 999999999)

-- The relative margin the abstract claims: the additive error `2^(⌊2s/3⌋+2)`
-- against the target `2^(s+1)`.  This prints `⌊2s/3⌋+2` vs `s+1`.
#eval (rows 6 40).map fun s => (s, 2 * s / 3 + 2, s + 1)

/-! ### PROBE: is there ANY late rank anywhere at which `hhigh` fails?

`seamRemainder_ge_of_not_hhigh_firstLate` and the late-rank instances of
`two_pow_le_seamRemainder_of_not_hhigh` need `¬ hhigh` at a LATE rank.  The list
below is every `(s,d)`, `2 ≤ d ≤ s`, `6 ≤ s ≤ 120`, with `¬ hhigh`, tagged LATE. -/
def notHhighTagged (hi : ℕ) : List ((ℕ × ℕ) × Bool) :=
  (rows 6 hi).flatMap fun s =>
    ((rows 2 s).filter fun d => !(hhighAt s d)).map fun d => ((s, d), decide (2 * s < 3 * d))

#eval ("(s,d) with ¬hhigh, tagged LATE :", notHhighTagged 120)
#eval ("...of which LATE :",
  (notHhighTagged 120).filter fun p => p.2)

/-! ### PROBE: how often is `hhigh` at `d₀` free from §3, with no reference to `ρ`? -/
#eval ("d0 DECLINED (hhigh free via §3) :", ((rows 6 220).filter declinedD0).length,
  "of", (rows 6 220).length)

/-! ## 5. Does the §3 declined-rank route ever discharge the conclusion alone?

`seamRemainder_lt_two_pow_succ_of_declined` needs a LATE DECLINED rank plus
`hlow` there.  Count the rows of `[6,220]` where some late rank is declined AND
`hlow` holds at that rank — i.e. where `ρ s < 2^(s+1)` is unconditional. -/

def unconditionalRow (s : ℕ) : Bool :=
  (List.range s).any fun d =>
    decide (2 ≤ d) && decide (d ≤ s) && decide (2 * s < 3 * d) &&
      decide (lateEntryRemainder s d < truncatedMersenneWeight s d) &&
      decide (lateCorrection s d ≤ lateEntryRemainder s d % 2 ^ (s + 1))

#eval ("rows of [6,220] where D3 §3 gives rho<2^(s+1) UNCONDITIONALLY:",
  ((rows 6 220).filter unconditionalRow).length, "of", (rows 6 220).length)
#eval ("rows where it does NOT:", failures unconditionalRow 6 220)

end ErdosProblems.DeclD3Verify
