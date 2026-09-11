/-
Copyright (c) 2026 Will Cook. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Will Cook
-/
import ErdosProblems.Decl.D4

/-!
# Adversarial verification of `ErdosProblems/Decl/D4.lean`

Default position: disbelief.  Everything below is either a machine check or an
explicitly labelled measurement.

* §1 axiom audit of every one of `D4`'s 63 declarations;
* §2 satisfiability of every non-trivial hypothesis, on the genuine corpus
  objects, over a wide range of rows and *every* late rank (not just the first);
* §3 independent re-derivation of `D4`'s definitions and of every measurement in
  its header, with exact failure sets;
* §4 falsification probes: is the new hypothesis a restatement of the
  conclusion?  is the additive slack of §3 real?  is the counterexample real?
* §5 the one place `D4`'s prose outruns its Lean: `D4`'s §5 verdict cites
  `T1.IntervalCeiling.two_pow_lt`, which is a statement about rank `s - 1` only
  and does **not** imply what the verdict says.  The verdict is nevertheless
  true; the correct theorem is proved here
  (`IntervalCeiling.four_pow_le_at`, `no_intervalCeiling_certifies_hhigh`).
* §6 what is *not* established.
-/

namespace ErdosProblems.DeclD4.Verify

open Erdos249257
open Erdos249257.HalfCylinderIntegerGreedy
open Erdos249257.BitCorr
open ErdosProblems.DeclD4

/-! ## 1. Axiom audit

All 63 declarations of `D4`, including the two `def`s.  Expected everywhere:
`[propext, Classical.choice, Quot.sound]` — Mathlib's standard three — and in
particular no `sorryAx`, no `Lean.ofReduceBool` (which is what `native_decide`
would introduce), no bespoke axiom. -/

#print axioms ErdosProblems.DeclD4.mod_two_pow_le_mod_two_pow
#print axioms ErdosProblems.DeclD4.two_pow_le_mod_two_pow_succ_of_testBit
#print axioms ErdosProblems.DeclD4.Seven.seamWeights_seven
#print axioms ErdosProblems.DeclD4.Seven.five_is_first_late
#print axioms ErdosProblems.DeclD4.Seven.lateEntryRemainder_seven_five
#print axioms ErdosProblems.DeclD4.Seven.lateCorrection_seven_five
#print axioms ErdosProblems.DeclD4.Seven.hhigh_seven_five
#print axioms ErdosProblems.DeclD4.Seven.not_hlow_seven_five
#print axioms ErdosProblems.DeclD4.Seven.hlow_seven_five_deficit
#print axioms ErdosProblems.DeclD4.Seven.not_lateEntryAdmissible_seven_five
#print axioms ErdosProblems.DeclD4.Seven.seamIntegerGreedyRemainder_seven
#print axioms ErdosProblems.DeclD4.Seven.seven_is_a_hit
#print axioms ErdosProblems.DeclD4.Seven.lateEntryRemainder_seven_six
#print axioms ErdosProblems.DeclD4.Seven.lateCorrection_seven_six
#print axioms ErdosProblems.DeclD4.Seven.admissible_seven_six
#print axioms ErdosProblems.DeclD4.Seven.hlow_is_rank_dependent
#print axioms ErdosProblems.DeclD4.lateCorrection_lt_two_pow_two_mul
#print axioms ErdosProblems.DeclD4.hlow_of_testBit
#print axioms ErdosProblems.DeclD4.window_nonempty
#print axioms ErdosProblems.DeclD4.hlow_of_testBit_halfPoint
#print axioms ErdosProblems.DeclD4.testBit_false_of_not_hlow
#print axioms ErdosProblems.DeclD4.hlow_twenty_fourteen_from_bit
#print axioms ErdosProblems.DeclD4.lateGreedy_lt_of_high
#print axioms ErdosProblems.DeclD4.seamRemainder_lt_two_pow_succ_add
#print axioms ErdosProblems.DeclD4.seamRemainder_lt_of_high
#print axioms ErdosProblems.DeclD4.seamRemainder_lt_three_mul_two_pow_of_high
#print axioms ErdosProblems.DeclD4.seamWeightsFrom_seven_five
#print axioms ErdosProblems.DeclD4.sharpness_seven_five
#print axioms ErdosProblems.DeclD4.bitCorrection
#print axioms ErdosProblems.DeclD4.bitCorrection_eq_zero
#print axioms ErdosProblems.DeclD4.bitCorrection_eq_cons
#print axioms ErdosProblems.DeclD4.bitCorrection_le_lateCorrection
#print axioms ErdosProblems.DeclD4.bitCorrection_congr
#print axioms ErdosProblems.DeclD4.lateGreedy_eq_mod_sub_bitCorrection
#print axioms ErdosProblems.DeclD4.lateGreedy_le_mod_of_bitCorrection
#print axioms ErdosProblems.DeclD4.mod_le_lateGreedy_add
#print axioms ErdosProblems.DeclD4.BitAdmissible
#print axioms ErdosProblems.DeclD4.bitAdmissible_of_lateEntryAdmissible
#print axioms ErdosProblems.DeclD4.seamRemainder_le_mod
#print axioms ErdosProblems.DeclD4.seamRemainder_lt_two_pow_succ'
#print axioms ErdosProblems.DeclD4.seamRemainder_lt_two_pow_of_testBit_false'
#print axioms ErdosProblems.DeclD4.half_mem_of_bitAdmissible_halfPointBitClearCofinally
#print axioms ErdosProblems.DeclD4.Seven.bitCorrection_seven_five
#print axioms ErdosProblems.DeclD4.Seven.bitLow_seven_five
#print axioms ErdosProblems.DeclD4.Seven.bitAdmissible_seven_five
#print axioms ErdosProblems.DeclD4.Seven.testBit_seven_halfPoint
#print axioms ErdosProblems.DeclD4.Seven.seamRemainder_seven_lt
#print axioms ErdosProblems.DeclD4.Seven.separation_at_seven_five
#print axioms ErdosProblems.DeclD4.seamRemainder_eq_mod_sub
#print axioms ErdosProblems.DeclD4.seamRemainder_bounds'
#print axioms ErdosProblems.DeclD4.two_pow_le_seamRemainder_add_of_testBit_true'
#print axioms ErdosProblems.DeclD4.seamWeightsFrom_getElem?
#print axioms ErdosProblems.DeclD4.lateEntryRemainder_eq_integerGreedy
#print axioms ErdosProblems.DeclD4.integerGreedy_take_eq_seamResidual
#print axioms ErdosProblems.DeclD4.lateEntryRemainder_eq_seamResidualUpto
#print axioms ErdosProblems.DeclD4.hhigh_iff_seamResidualUpto
#print axioms ErdosProblems.DeclD4.hhigh_thirteen_nine
#print axioms ErdosProblems.DeclD4.seamResidualUpto_thirteen_eight
#print axioms ErdosProblems.DeclD4.bitAdmissible_fourteen
#print axioms ErdosProblems.DeclD4.bitAdmissible_twenty
#print axioms ErdosProblems.DeclD4.seamRemainder_twenty_lt'
#print axioms ErdosProblems.DeclD4.seamRemainder_twenty_lt_of_high
#print axioms ErdosProblems.DeclD4.seamRemainder_seven_lt_of_high

/-! ## 2. Satisfiability of every hypothesis, on real data

`D4` carries exactly three non-trivial hypothesis shapes:

* `hhigh   : lateEntryRemainder s d < 2 ^ (2 * s - d + 1)`  (§3, §5);
* `hlow    : lateCorrection s d ≤ lateEntryRemainder s d % 2 ^ (s + 1)`  (§1, §2);
* `hpay    : bitCorrection s C d ≤ C % 2 ^ (s + 1)`  (§4), packaged with `hhigh`
  into `BitAdmissible`.

Plus the cofinal hypothesis of
`half_mem_of_bitAdmissible_halfPointBitClearCofinally`, which is not decidable
and is discussed in §6. -/

instance decBitAdmissible (s d : ℕ) : Decidable (BitAdmissible s d) := by
  unfold BitAdmissible; infer_instance

instance decLateEntryAdmissible (s d : ℕ) :
    Decidable (ThreeT4.LateEntryAdmissible s d) := by
  unfold ThreeT4.LateEntryAdmissible; infer_instance

/-- The first late rank of row `s`, i.e. the least `d` with `2 * s < 3 * d`. -/
def firstLate (s : ℕ) : ℕ := 2 * s / 3 + 1

example (s : ℕ) : 2 * s < 3 * firstLate s := by unfold firstLate; omega
example (s : ℕ) : ¬ (2 * s < 3 * (firstLate s - 1)) := by unfold firstLate; omega

/-! **`BitAdmissible` at the first late rank, rows `6 … 420`.**  Printed:
`(rows tested, failure set)`.  A non-empty first component rules out a vacuous
sweep; the second is the exact failure set, not a summary statistic. -/
#eval
  let rows := (List.range 415).map (· + 6)
  (rows.length, rows.filter (fun s => !decide (BitAdmissible s (firstLate s))))

/-! **The same for `T4`'s `LateEntryAdmissible`.**  This is the comparison that
makes `D4`'s §4 a strengthening rather than a relabelling: the two failure sets
must differ, and they must differ exactly at `7`. -/
#eval
  let rows := (List.range 415).map (· + 6)
  (rows.filter (fun s => !decide (ThreeT4.LateEntryAdmissible s (firstLate s))),
   rows.filter (fun s => !decide (BitAdmissible s (firstLate s))))

/-! **All late ranks, not just the first**, rows `6 … 160`.  Failure sets of
`hhigh`, of `hlow` and of `hpay` over every `(s, d)` with `2 ≤ d ≤ s` and
`2 * s < 3 * d`.  Printed: `(pairs tested, hhigh failures, hlow failures,
hpay failures)`. -/
#eval
  let pairs := ((List.range 155).map (· + 6)).flatMap (fun s =>
    ((List.range (s + 1)).filter (fun d => 2 ≤ d && decide (2 * s < 3 * d))).map
      (fun d => (s, d)))
  (pairs.length,
   pairs.filter (fun p =>
     !decide (lateEntryRemainder p.1 p.2 < 2 ^ (2 * p.1 - p.2 + 1))),
   pairs.filter (fun p =>
     !decide (lateCorrection p.1 p.2 ≤ lateEntryRemainder p.1 p.2 % 2 ^ (p.1 + 1))),
   pairs.filter (fun p =>
     !decide (bitCorrection p.1 (lateEntryRemainder p.1 p.2) p.2
        ≤ lateEntryRemainder p.1 p.2 % 2 ^ (p.1 + 1))))

/-! **The `hlow` hypothesis of §2's sufficient condition.**  `hlow_of_testBit`
needs a set bit in the window `[2 * (s - d) + 1, s]`.  Failure set over rows
`6 … 420` at the first late rank, and — separately — the rows where the window
condition fails but `hlow` itself still holds.  `D4`'s header claims `{7, 14}`
and `{14}` respectively. -/
#eval
  let rows := (List.range 415).map (· + 6)
  let winFails := rows.filter (fun s =>
    let d := firstLate s
    let R := lateEntryRemainder s d
    !((List.range (s + 1 - (2 * (s - d) + 1))).any (fun k =>
        Nat.testBit R (2 * (s - d) + 1 + k))))
  (winFails,
   winFails.filter (fun s =>
     decide (lateCorrection s (firstLate s)
       ≤ lateEntryRemainder s (firstLate s) % 2 ^ (s + 1))))

/-! **Anti-vacuity of the two `def`s themselves.**  `bitCorrection` must not be
identically `0` (which would make `hpay` free) nor identically
`lateCorrection` (which would make §4 a relabelling).  Printed, at the first
late rank of rows `6 … 40`:
`(s, bitCorrection, lateCorrection, low block)`. -/
#eval ((List.range 35).map (· + 6)).map (fun s =>
  let d := firstLate s
  let R := lateEntryRemainder s d
  (s, bitCorrection s R d, lateCorrection s d, R % 2 ^ (s + 1)))

/-! ## 3. Independent re-derivation

`bitCorr'` and `lateCorr'` are written from the mathematical description in
`D4`'s prose ("`∑ 4 ^ (s - e)` over the late ranks `e ∈ [d, s)` whose bit
`2 * s - e` of `C` is set"), as `List.range` folds rather than well-founded
recursions.  `lateEntry'` re-derives the entering remainder from
`truncatedMersenneWeight` directly, bypassing `earlyWeights`/`seamWeights`.
If any of these disagreed with the corpus objects, the whole of §2 above would
be measuring the wrong thing. -/

def bitCorr' (s C d : ℕ) : ℕ :=
  ((List.range (s - d)).map (fun k =>
    if Nat.testBit C (2 * s - (d + k)) then 4 ^ (s - (d + k)) else 0)).sum

def lateCorr' (s d : ℕ) : ℕ :=
  ((List.range (s - d)).map (fun k => 4 ^ (s - (d + k)))).sum

def lateEntry' (s d : ℕ) : ℕ :=
  integerGreedyRemainder ((List.range (d - 2)).map (fun k =>
    truncatedMersenneWeight s (k + 2))) (seamSubsetTarget s)

def rho' (s : ℕ) : ℕ :=
  integerGreedyRemainder ((List.range (s - 2)).map (fun k =>
    truncatedMersenneWeight s (k + 2))) (seamSubsetTarget s)

/-! **Cross-check of the re-implementations against the corpus objects**, over
every `(s, d)` with `6 ≤ s ≤ 120`, `2 ≤ d ≤ s`.  Printed:
`(pairs tested, bitCorr' mismatches, lateCorr' mismatches, lateEntry'
mismatches, rho' mismatches)`.  All four failure sets must be empty. -/
#eval
  let pairs := ((List.range 115).map (· + 6)).flatMap (fun s =>
    ((List.range (s + 1)).filter (2 ≤ ·)).map (fun d => (s, d)))
  (pairs.length,
   pairs.filter (fun p =>
     bitCorr' p.1 (lateEntryRemainder p.1 p.2) p.2
       ≠ bitCorrection p.1 (lateEntryRemainder p.1 p.2) p.2),
   pairs.filter (fun p => lateCorr' p.1 p.2 ≠ lateCorrection p.1 p.2),
   pairs.filter (fun p => lateEntry' p.1 p.2 ≠ lateEntryRemainder p.1 p.2),
   ((List.range 115).map (· + 6)).filter (fun s =>
     rho' s ≠ seamIntegerGreedyRemainder s))

/-! **The header's measured claim: the exact identity.**  `D4` reports
`ρ s = R % 2 ^ (s+1) − bitCorrection s R d` over `s ∈ [6, 2200]` with empty
failure set.  Re-derived here from the independent definitions, rows `6 … 420`,
first late rank.  Printed: `(rows tested, failure set)`. -/
#eval
  let rows := (List.range 415).map (· + 6)
  (rows.length,
   rows.filter (fun s =>
     let d := firstLate s
     let R := lateEntry' s d
     rho' s ≠ R % 2 ^ (s + 1) - bitCorr' s R d))

/-! **The header's measured claim: `hhigh` never fails on `[6, 2200]`.**
Re-derived independently, rows `6 … 420`, first late rank. -/
#eval ((List.range 415).map (· + 6)).filter (fun s =>
  let d := firstLate s
  !decide (lateEntry' s d < 2 ^ (2 * s - d + 1)))

/-! **The header's measured claim: `hlow` fails at exactly `{7}`.**  Re-derived
independently, rows `6 … 420`, first late rank. -/
#eval ((List.range 415).map (· + 6)).filter (fun s =>
  let d := firstLate s
  !decide (lateCorr' s d ≤ lateEntry' s d % 2 ^ (s + 1)))

/-! **Beyond the header's range.**  `D4` scans `[6, 2200]`.  An independent
scan of the *same* definitions in Python (`4 ^ s / (2 ^ d - 1)`,
`2 ^ (2s-1) - 2 ^ s`, descending greedy) over `s ∈ [6, 3400]` at the first late
rank returns, MEASURED not proved:

* `hhigh` failure set: `∅`;
* `hlow` failure set: `{7}`;
* `hpay` failure set: `∅`;
* exact-identity failure set: `∅`;
* §2 window-condition failure set: `{7, 14}`;
* `ρ s ≥ 2 ^ (s + 1)` failure set: `∅` (so the *conclusion* `T4` wants is
  true, unproved, on every row scanned).

A second independent Python scan over **every** late rank of every row
`s ∈ [6, 700]` (not just the first) returns: `hhigh` never fails; `hlow` fails
at exactly the single pair `(7, 5)`; `hpay` never fails; and `T1`'s
`ResidualInvariant` fails at exactly the single pair `(13, 7)` — which is never
of the form `(s, d - 1)` for a late `d`, since the first late rank of row `13`
is `9`.  This is the whole content of `D4`'s `hhigh_thirteen_nine`, confirmed
at scale.  The Lean `#eval`s above reproduce all of it up to `s ≤ 420`. -/

/-! ## 4. Falsification probes -/

/-! ### 4.1 Is `hpay` a restatement of the conclusion?

If `bitCorrection s C d ≤ C % 2 ^ (s + 1)` were *equivalent* to
`integerGreedyRemainder (seamWeightsFrom s d) C < 2 ^ (s + 1)`, then
`seamRemainder_lt_two_pow_succ'` would be assuming what it proves.  It is not:
the implication is strict.  Printed, at `(s, d) = (7, 5)` over all
`C < 2 ^ (2 * s - d + 1) = 2 ^ 10`:
`(C with hpay and conclusion, C with hpay but not conclusion,
  C with conclusion but not hpay, C with neither)`.
The second component must be `0` (soundness of `D4`'s theorem) and the third
must be non-zero (the hypothesis is strictly stronger, hence not a restatement). -/
#eval
  let s := 7; let d := 5
  let cs := List.range (2 ^ (2 * s - d + 1))
  let hpay := fun C => decide (bitCorrection s C d ≤ C % 2 ^ (s + 1))
  let concl := fun C =>
    decide (integerGreedyRemainder (seamWeightsFrom s d) C < 2 ^ (s + 1))
  ((cs.filter (fun C => hpay C && concl C)).length,
   (cs.filter (fun C => hpay C && !concl C)).length,
   (cs.filter (fun C => !hpay C && concl C)).length,
   (cs.filter (fun C => !hpay C && !concl C)).length)

/-! The same at `(s, d) = (10, 7)`, `(13, 9)`. -/
#eval
  ([(10, 7), (13, 9)]).map (fun p =>
    let s := p.1; let d := p.2
    let cs := List.range (2 ^ (2 * s - d + 1))
    let hpay := fun C => decide (bitCorrection s C d ≤ C % 2 ^ (s + 1))
    let concl := fun C =>
      decide (integerGreedyRemainder (seamWeightsFrom s d) C < 2 ^ (s + 1))
    (p,
     (cs.filter (fun C => hpay C && !concl C)).length,
     (cs.filter (fun C => !hpay C && concl C)).length))

/-! ### 4.2 Is the additive slack of §3 real, and how tight?

`lateGreedy_lt_of_high` gives `< 2 ^ (s + 1) + 4 ^ (s - d)` from `hhigh` alone.
`D4` justifies the slack with the single witness `C = 527` at `(7, 5)`.
Exhaustively, over all `C < 2 ^ 10`: the maximum late-greedy remainder, the
bound `2 ^ 8 + 4 ^ 2 = 272`, and the full list of `C` overshooting `2 ^ 8`.
The maximum is `267`, so the bound holds and is *not* attained: `D4` claims only
that the slack cannot be removed, which is exactly what `267 ≥ 256` shows. -/
#eval
  let s := 7; let d := 5
  let cs := List.range (2 ^ (2 * s - d + 1))
  let g := fun C => integerGreedyRemainder (seamWeightsFrom s d) C
  ((cs.map g).foldl max 0, 2 ^ (s + 1) + 4 ^ (s - d), 2 ^ (s + 1),
   cs.filter (fun C => decide (2 ^ (s + 1) ≤ g C)))

/-! The same overshoot maximum at several `(s, d)`, against `4 ^ (s - d)`:
`(s, d, max (greedy − 2 ^ (s+1)), 4 ^ (s - d))`.  The slack is real everywhere
and is within a factor `< 2` of optimal — so `4 ^ (s - d)` is the right order,
though not the least constant. -/
#eval
  ([(6, 5), (7, 5), (8, 6), (9, 7), (10, 7), (11, 8)]).map (fun p =>
    let s := p.1; let d := p.2
    let cs := List.range (2 ^ (2 * s - d + 1))
    let g := fun C => integerGreedyRemainder (seamWeightsFrom s d) C
    (s, d, ((cs.map (fun C => g C - 2 ^ (s + 1))).foldl max 0), 4 ^ (s - d)))

/-! ### 4.2b The sharpness witness is NOT a genuine entering remainder

`D4`'s header draws a stronger conclusion from `sharpness_seven_five` than the
theorem supports:

> So `hhigh` alone provably cannot deliver `ρ s < 2 ^ (s + 1)`.

What `sharpness_seven_five` proves is that the late greedy run from an
*arbitrary* capacity satisfying `hhigh` can overshoot `2 ^ (s + 1)`.  The
capacity it uses is `527`, and `lateEntryRemainder 7 5 = 263 ≠ 527`.  Genuine
entering remainders are not arbitrary, so nothing here rules out the implication
"`hhigh` at the genuine remainder ⟹ `ρ s < 2 ^ (s + 1)`".  Indeed that
implication has no counterexample anywhere scanned.

The file's own adjacent sentence — "no strengthening of the *argument* of §3 can
remove the slack" — is the accurate version.  Printed:
`(527, lateEntryRemainder 7 5, ρ 7, 2 ^ 8, rows of [6,420] with ρ s ≥ 2 ^ (s+1))`. -/
#eval (527, lateEntryRemainder 7 5, seamIntegerGreedyRemainder 7, 2 ^ 8,
  ((List.range 415).map (· + 6)).filter (fun s =>
    decide (2 ^ (s + 1) ≤ seamIntegerGreedyRemainder s)))

/-! ### 4.3 Is the §1 counterexample real, and is it the only one?

`D4`'s headline is `not_hlow_seven_five`.  Recomputed from scratch:
`(seamWeights 7, seamSubsetTarget 7, lateEntryRemainder 7 5, its low block,
  lateCorrection 7 5, ρ 7)`.  Expected
`([5461, 2340, 1092, 528, 260], 8064, 263, 7, 20, 3)`. -/
#eval (seamWeights 7, seamSubsetTarget 7, lateEntryRemainder 7 5,
  lateEntryRemainder 7 5 % 2 ^ 8, lateCorrection 7 5, seamIntegerGreedyRemainder 7)

/-! And the rank-dependence claim: `hlow` at `(7, d)` for every late `d`.
Expected `[(5, false), (6, true), (7, true)]`. -/
#eval ((List.range 8).filter (fun d => 2 ≤ d && decide (2 * 7 < 3 * d))).map
  (fun d => (d, decide (lateCorrection 7 d ≤ lateEntryRemainder 7 d % 2 ^ 8)))

/-! ### 4.4 Row `5`, the excluded degenerate row

`D4` excludes `s = 5` throughout, on the stated ground that `hhigh` fails there.
Checked: `(ρ 5, 2 ^ 6, hhigh at (5,4), hhigh at (5,5), BitAdmissible 5 4,
BitAdmissible 5 5)`.  `ρ 5 = 71 > 64`, so this row genuinely falsifies the
*conclusion*; every hypothesis of `D4` must therefore exclude it, and does. -/
#eval (seamIntegerGreedyRemainder 5, 2 ^ 6,
  decide (lateEntryRemainder 5 4 < 2 ^ (2 * 5 - 4 + 1)),
  decide (lateEntryRemainder 5 5 < 2 ^ (2 * 5 - 5 + 1)),
  decide (BitAdmissible 5 4), decide (BitAdmissible 5 5))

/-! ## 5. `D4` §5: the verdict is true, but its citation is not

`D4`'s header concludes:

> `hhigh` is the obstruction: by §5 it *is* `RemC6`'s residual invariant at the
> single rank `d - 1`, which `T1.IntervalCeiling.two_pow_lt` shows no
> rank-indexed interval induction can produce.

The first half is proved in `D4` (`lateEntryRemainder_eq_seamResidualUpto`,
`hhigh_iff_seamResidualUpto`) and is correct.  The second half does **not**
follow from the theorem cited: `T1.IntervalCeiling.two_pow_lt` says
`2 ^ (s + 1) < K.bound (s - 1)`, a statement about the *terminal* rank `s - 1`
and the *terminal* target `2 ^ (s + 1)`.  `hhigh` lives at rank `d - 1 ≈ 2s/3`
with target `2 ^ (2 * s - d + 1) ≈ 2 ^ (4s/3)`, which is exponentially larger
than `2 ^ (s + 1)`; nothing about rank `s - 1` bears on it.  As stated, the
inference is a non-sequitur.

The conclusion is nevertheless true, and this section proves it.  `T1`'s chain
bound holds at every rank, not just the last, and it pins every interval
ceiling at the `4 ^ s` scale throughout — far above `2 ^ (2 * s - d + 1)` in the
late zone.  So no `IntervalCeiling` certifies `hhigh` either. -/

open Three.T1 in
/-- **`T1`'s no-go at every rank, not just `s - 1`.**  The proof of
`T1.IntervalCeiling.four_pow_le` specialises `IntervalCeiling.chain` to
`b = s - 1`; the chain holds at every `b`, and the tail sum is monotone, so the
`4 ^ s` floor is a floor on the *whole* ceiling function. -/
theorem IntervalCeiling.four_pow_le_at {s : ℕ} (hs : 6 ≤ s) (K : IntervalCeiling s)
    {b : ℕ} (hb : 3 ≤ b) (hbs : b < s) :
    4 ^ s ≤ 105 * K.bound b + 90 := by
  have hchain := K.chain b hb hbs
  have hw3 := K.weight_three_le hs
  have htail := fifteen_mul_weightSum_tail_le s
  have hsub : ∑ j ∈ Finset.Ico 4 (b + 1), truncatedMersenneWeight s j
      ≤ ∑ j ∈ Finset.Ico 4 s, truncatedMersenneWeight s j :=
    Finset.sum_le_sum_of_subset (Finset.Ico_subset_Ico le_rfl (by omega))
  have hw3' : truncatedMersenneWeight s 3 = 4 ^ s / 7 := by
    norm_num [truncatedMersenneWeight]
  have d7 := Nat.div_add_mod (4 ^ s) 7
  have d7' : 4 ^ s % 7 < 7 := Nat.mod_lt _ (by norm_num)
  omega

open Three.T1 in
/-- **No interval ceiling certifies `hhigh`.**  For `s ≥ 11` and any late rank
`d` of row `s`, every `IntervalCeiling s` has `2 ^ (2 * s - d + 1) ≤ bound (d-1)`.

The mechanism: writing `P = 2 ^ (2*s-d+1)` and `Q = 2 ^ (d-1)` we have
`P * Q = 4 ^ s`, while `4 ^ s ≤ 105 * bound (d-1) + 90`.  If the ceiling were
below `P` this would force `Q < 105`, i.e. `d ≤ 7`, i.e. `s ≤ 10`.

So `D4`'s verdict — "`hhigh` is the obstruction, and it is out of reach of the
induction `C6` attempted" — is correct.  Only its citation was wrong. -/
theorem no_intervalCeiling_certifies_hhigh {s d : ℕ} (hs : 11 ≤ s) (hds : d ≤ s)
    (hlate : 2 * s < 3 * d) (K : IntervalCeiling s) :
    2 ^ (2 * s - d + 1) ≤ K.bound (d - 1) := by
  by_contra hcontra
  have hcon : K.bound (d - 1) < 2 ^ (2 * s - d + 1) := Nat.not_le.mp hcontra
  have hd8 : 8 ≤ d := by omega
  have h4 : 4 ^ s ≤ 105 * K.bound (d - 1) + 90 :=
    IntervalCeiling.four_pow_le_at (by omega) K (by omega) (by omega)
  have hPQ : (2 : ℕ) ^ (2 * s - d + 1) * 2 ^ (d - 1) = 4 ^ s := by
    rw [← pow_add, show 2 * s - d + 1 + (d - 1) = 2 * s by omega,
      show (4 : ℕ) = 2 ^ 2 by norm_num, ← pow_mul, Nat.mul_comm 2 s]
  have hQ : (128 : ℕ) ≤ 2 ^ (d - 1) := by
    calc (128 : ℕ) = 2 ^ 7 := by norm_num
      _ ≤ 2 ^ (d - 1) := Nat.pow_le_pow_right (by norm_num) (by omega)
  have hPpos : 0 < (2 : ℕ) ^ (2 * s - d + 1) := Nat.two_pow_pos _
  have hmul : 2 ^ (2 * s - d + 1) * 128 ≤ 2 ^ (2 * s - d + 1) * 2 ^ (d - 1) :=
    Nat.mul_le_mul_left _ hQ
  rw [hPQ] at hmul
  omega

open Three.T1 in
/-- **Anti-vacuity.**  `IntervalCeiling s` is inhabited (`T1.trivialCeiling`), so
the previous theorem is a statement about a non-empty class; here it is at the
corpus's own certified row `(s, d) = (20, 14)`. -/
theorem no_intervalCeiling_certifies_hhigh_twenty :
    2 ^ (2 * 20 - 14 + 1) ≤ (trivialCeiling 20).bound (14 - 1) :=
  no_intervalCeiling_certifies_hhigh (by norm_num) (by norm_num) (by norm_num) _

open Three.T1 in
/-- The gap is not marginal: at row `20` the trivial ceiling at rank `13` is
`seamSubsetTarget 20 + 1`, against `hhigh`'s target `2 ^ 27`. -/
example : ((trivialCeiling 20).bound 13, 2 ^ (2 * 20 - 14 + 1)) =
    (seamSubsetTarget 20 + 1, 134217728) := by
  norm_num [trivialCeiling, seamSubsetTarget]

/-! **`hhigh` and `T1.ResidualInvariant` line up exactly.**  Confirming `D4`'s
`hhigh_iff_seamResidualUpto` numerically at the rows that matter, and confirming
that `T1`'s refuting rank `7` of row `13` is not a late rank's predecessor:
`(firstLate 13, firstLate 13 - 1, seamResidualUpto 13 7, 2 ^ 19,
  seamResidualUpto 13 8, 2 ^ 18)`. -/
#eval (firstLate 13, firstLate 13 - 1,
  Three.T1.seamResidualUpto 13 7, 2 ^ 19,
  Three.T1.seamResidualUpto 13 8, 2 ^ 18)

/-! Failure set of `T1.ResidualInvariant` over rows `6 … 160`, all ranks
`2 ≤ d < s`, and — separately — its failure set restricted to the ranks
`d = firstLate s - 1` that `hhigh` actually needs.  The first is `{(13, 7)}`;
the second must be empty, which is exactly why `T1.not_residualInvariant` does
not refute `hhigh`. -/
#eval
  let rows := (List.range 155).map (· + 6)
  (rows.flatMap (fun s =>
     ((List.range s).filter (2 ≤ ·)).filterMap (fun d =>
       if Three.T1.seamResidualUpto s d < 2 ^ (2 * s - d) then none else some (s, d))),
   rows.filterMap (fun s =>
     let d := firstLate s - 1
     if Three.T1.seamResidualUpto s d < 2 ^ (2 * s - d) then none else some (s, d)))

/-! ## 6. What is NOT established

1. **`ρ s < 2 ^ (s + 1)` is NOT unconditional after `D4`.**  Every bound in the
   file is conditional on `hhigh` at some late rank: `seamRemainder_lt_of_high`,
   `seamRemainder_lt_two_pow_succ_add`, `seamRemainder_lt_two_pow_succ'` all
   take it.  `D4` removes `hlow`, not `hhigh`, and §5 above shows `hhigh` is out
   of reach of the interval induction.  The unconditional statement is exactly
   as far away as it was before this file.

2. **Erdős #257 has not moved.**  `half_mem_of_bitAdmissible_halfPointBitClearCofinally`
   weakens the hypothesis of `T4`'s reduction from `LateEntryAdmissible` to
   `BitAdmissible`.  On the evidence of §2–§3 that weakening buys exactly one
   row (`s = 7`) in `[6, 3400]` at the first late rank, and exactly one pair
   `(7, 5)` over all late ranks of `[6, 700]`.  The cofinal hypothesis itself is
   untouched and uninstantiated, and by `D4`'s own header even
   `ρ s < 2 ^ (s + 1)` would not settle `#257`.

3. **The header's `[6, 2200]` measurements are confirmed, not proved.**  §3 above
   reproduces them independently in Lean to `s ≤ 420` and in Python to
   `s ≤ 3400`, with the exact failure sets `∅`, `{7}`, `∅`, `∅`, `{7, 14}`.  No
   theorem in `D4` or here asserts any of them for all `s`.

4. **`D4`'s §1 is a formalisation of something `T4`'s own verify file had already
   measured** (`ErdosProblems/Three/verify/T4.lean` reports the failure set of
   `LateEntryAdmissible s (firstLate s)` on `[6, 800]` as `[7]`).  `D4` upgrades
   that measurement to a theorem, which is a real gain, but it is not a new
   discovery about the corpus.

5. **Two prose overreaches, both repaired above, neither touching a Lean
   statement.**  (a) The §5 verdict's appeal to `T1.IntervalCeiling.two_pow_lt`
   does not support the claim made; the correct statement is
   `no_intervalCeiling_certifies_hhigh` above.  (b) "`hhigh` alone provably
   cannot deliver `ρ s < 2 ^ (s + 1)`" overstates `sharpness_seven_five`, whose
   witness `527` is not a genuine entering remainder (§4.2b); what is proved is
   that §3's *argument* cannot, which is what the header's next clause says.

Every `theorem` statement in `D4` was checked against its proof and against
data.  None was found to be false, vacuous, circular, or narrower than stated.
-/

end ErdosProblems.DeclD4.Verify
