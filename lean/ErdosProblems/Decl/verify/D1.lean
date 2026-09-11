/-
Copyright (c) 2026 Will Cook. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Will Cook
-/
import ErdosProblems.Decl.D1

/-!
# Adversarial verification of `ErdosProblems/Decl/D1.lean`

* §1  Axiom audit of every declaration of `D1`.
* §2  An independent transcription of the greedy, checked against `T1`.
* §3  **Satisfiability** of every non-trivial hypothesis, on real corpus data,
      over a wide range of rows.
* §4  Independent re-run of every measurement `D1` records, reporting the exact
      failure set rather than a summary statistic.
* §5  The two anti-vacuity gaps found, and the proofs that fill them.
* §6  What `D1` does not establish.

Everything below is either a `#eval` (a computation, reported as MEASURED) or a
proof (reported as PROVED).  Nothing is taken from `D1`'s prose.
-/

open Erdos249257 Erdos249257.HalfCylinderIntegerGreedy
open ErdosProblems.Three.T1
open ErdosProblems.Decl.D1

namespace ErdosProblems.Decl.VerifyD1

/-! ## 1. Axiom audit

Every declaration of `D1`, in file order.  Expected: `propext`,
`Classical.choice`, `Quot.sound` only.  Any `sorryAx` or bespoke axiom is a
failure. -/

#print axioms ErdosProblems.Decl.D1.weightTail
#print axioms ErdosProblems.Decl.D1.weight_eq_top_add_tail
#print axioms ErdosProblems.Decl.D1.weightTail_le
#print axioms ErdosProblems.Decl.D1.weight_succ_le_of_two_pow_le
#print axioms ErdosProblems.Decl.D1.residual_lt_two_pow_of_declined
#print axioms ErdosProblems.Decl.D1.BrokenAt
#print axioms ErdosProblems.Decl.D1.BrokenAt.taken
#print axioms ErdosProblems.Decl.D1.BrokenAt.not_declined_succ
#print axioms ErdosProblems.Decl.D1.BrokenAt.residual_succ
#print axioms ErdosProblems.Decl.D1.BrokenAt.excess_lt
#print axioms ErdosProblems.Decl.D1.BrokenAt.residual_succ_lt
#print axioms ErdosProblems.Decl.D1.BrokenAt.restored
#print axioms ErdosProblems.Decl.D1.BrokenAt.not_restored
#print axioms ErdosProblems.Decl.D1.brokenAt_thirteen_seven
#print axioms ErdosProblems.Decl.D1.seamResidualUpto_thirteen_eight
#print axioms ErdosProblems.Decl.D1.thirteen_break_repairs
#print axioms ErdosProblems.Decl.D1.weightTail_fails_halving
#print axioms ErdosProblems.Decl.D1.seamWeightsFrom_sum_exact
#print axioms ErdosProblems.Decl.D1.sum_exact_implies_C6_lower
#print axioms ErdosProblems.Decl.D1.remainder_lt_of_late_largest_skip_sharp
#print axioms ErdosProblems.Decl.D1.late_largest_skip_bound_sharp
#print axioms ErdosProblems.Decl.D1.remainder_lt_of_largest_skip_pred_pred
#print axioms ErdosProblems.Decl.D1.sharp_strictly_beats_C6
#print axioms ErdosProblems.Decl.D1.sharp_bound_sixteen
#print axioms ErdosProblems.Decl.D1.remainder_sixteen_lt_sharp
#print axioms ErdosProblems.Decl.D1.sharp_bound_fourteen
#print axioms ErdosProblems.Decl.D1.correction_ge
#print axioms ErdosProblems.Decl.D1.correction_ge_trivial
#print axioms ErdosProblems.Decl.D1.tailCorrected_not_intervalCeiling
#print axioms ErdosProblems.Decl.D1.PairCeiling
#print axioms ErdosProblems.Decl.D1.PairCeiling.sound
#print axioms ErdosProblems.Decl.D1.PairCeiling.SplitsAt
#print axioms ErdosProblems.Decl.D1.PairCeiling.lo_succ_eq_zero
#print axioms ErdosProblems.Decl.D1.PairCeiling.weight_le_hi_succ
#print axioms ErdosProblems.Decl.D1.PairCeiling.weight_pos
#print axioms ErdosProblems.Decl.D1.PairCeiling.zero_lo_step
#print axioms ErdosProblems.Decl.D1.PairCeiling.zero_lo_forever
#print axioms ErdosProblems.Decl.D1.PairCeiling.declined_obligation
#print axioms ErdosProblems.Decl.D1.PairCeiling.terminal_ge_of_splits
#print axioms ErdosProblems.Decl.D1.PairCeiling.not_splitsAt_of_terminal_lt
#print axioms ErdosProblems.Decl.D1.PairCeiling.branch_decided
#print axioms ErdosProblems.Decl.D1.PairCeiling.branches_decided_of_terminal_lt
#print axioms ErdosProblems.Decl.D1.PairCeiling.orbit
#print axioms ErdosProblems.Decl.D1.PairCeiling.orbit_never_splits
#print axioms ErdosProblems.Decl.D1.PairCeiling.loose
#print axioms ErdosProblems.Decl.D1.PairCeiling.loose_splitsAt_two
#print axioms ErdosProblems.Decl.D1.PairCeiling.loose_terminal_ge
#print axioms ErdosProblems.Decl.D1.take_succ_seamWeightsFrom
#print axioms ErdosProblems.Decl.D1.integerGreedyRemainder_seamWeights_take
#print axioms ErdosProblems.Decl.D1.lateEntryRemainder_eq
#print axioms ErdosProblems.Decl.D1.lateEntryRemainder_lt_two_pow_of_declined
#print axioms ErdosProblems.Decl.D1.lateEntryRemainder_twenty_fifteen
#print axioms ErdosProblems.Decl.D1.declined_twenty_fifteen
#print axioms ErdosProblems.Decl.D1.hhigh_twenty_fifteen

/-! ## 2. An independent transcription of the greedy

`rowScan` recomputes the descending seam greedy in one linear pass, straight
from the raw definitions `truncatedMersenneWeight s d = 4 ^ s / (2 ^ d - 1)` and
`seamSubsetTarget s = 2 ^ (2*s-1) - 2 ^ s`, without touching `T1.seamResidual`.
Every scan in §3 and §4 runs off it.  It is checked against `seamResidualUpto`
immediately below. -/

/-- One row: the list of `(d, R d, taken?)` for `d = 2 … s-1`, left to right. -/
def scanAux (s : ℕ) : ℕ → ℕ → ℕ → List (ℕ × ℕ × Bool)
  | 0, _, _ => []
  | n + 1, d, r =>
      let w := truncatedMersenneWeight s d
      let t := w ≤ r
      let r' := if t then r - w else r
      (d, r', decide t) :: scanAux s n (d + 1) r'

def rowScan (s : ℕ) : List (ℕ × ℕ × Bool) := scanAux s (s - 2) 2 (seamSubsetTarget s)

def weightTail' (s d : ℕ) : ℕ := truncatedMersenneWeight s d - 2 ^ (2 * s - d)

/-- Rows `6 … s+5`. -/
def rows (n : ℕ) : List ℕ := (List.range n).map (fun i => i + 6)

/-! ### CHECK: the transcription agrees with `T1.seamResidualUpto`

at every rank of every row `6 … 60`.  Expected `[]`. -/

#eval (rows 55).flatMap (fun s =>
  (rowScan s).filterMap (fun p =>
    if p.2.1 = seamResidualUpto s p.1 then none else some (s, p.1)))

/-! ## 3. Satisfiability of every non-trivial hypothesis

Each block prints the **exact** instance set (or the exact failure set), never a
summary statistic. -/

/-! ### SAT `BrokenAt s d`

the hypothesis of `BrokenAt.taken`, `.not_declined_succ`, `.residual_succ`,
`.excess_lt`, `.residual_succ_lt`, `.restored`, `.not_restored`.
Exact instance set over `s ∈ [6, 300]`, `d ∈ [2, s-2]`. -/

#eval (rows 295).flatMap (fun s =>
  (rowScan s).filterMap (fun p =>
    let d := p.1
    let r := p.2.1
    if d + 1 < s ∧ 2 ^ (2 * s - d) ≤ r ∧ r < truncatedMersenneWeight s d
    then some (s, d) else none))

/-! ### SAT the extra hypothesis `hsmall` of `BrokenAt.restored`

`R d < 2 ^ (2*s-d) + weightTail s (d+1)`, over `s ∈ [6, 300]`. -/

#eval (rows 295).flatMap (fun s =>
  (rowScan s).filterMap (fun p =>
    let d := p.1
    let r := p.2.1
    if d + 1 < s ∧ 2 ^ (2 * s - d) ≤ r ∧ r < truncatedMersenneWeight s d
        ∧ r < 2 ^ (2 * s - d) + weightTail' s (d + 1)
    then some (s, d) else none))

/-! ### SAT the extra hypothesis `hbig` of `BrokenAt.not_restored`

`2 ^ (2*s-d) + weightTail s (d+1) ≤ R d`, over `s ∈ [6, 300]`.
**If this prints `[]`, `BrokenAt.not_restored` has no instance on real corpus
data in the scanned range.** -/

#eval (rows 295).flatMap (fun s =>
  (rowScan s).filterMap (fun p =>
    let d := p.1
    let r := p.2.1
    if d + 1 < s ∧ 2 ^ (2 * s - d) ≤ r ∧ r < truncatedMersenneWeight s d
        ∧ 2 ^ (2 * s - d) + weightTail' s (d + 1) ≤ r
    then some (s, d) else none))

/-! ### SAT the hypothesis `2 ^ (2*s-d) ≤ R d`

of `weight_succ_le_of_two_pow_le` (equivalently, the negated conclusion of
`residual_lt_two_pow_of_declined`).  Exact instance set over `s ∈ [6, 300]`. -/

#eval (rows 295).flatMap (fun s =>
  (rowScan s).filterMap (fun p =>
    let d := p.1
    if d + 1 ≤ s ∧ 2 ^ (2 * s - d) ≤ p.2.1 then some (s, d) else none))

/-! ### SAT the hypothesis "rank `d+1` is declined"

of `residual_lt_two_pow_of_declined`.  Count and first ten over `s ∈ [6, 120]`. -/

#eval
  let hits := (rows 115).flatMap (fun s =>
    (rowScan s).filterMap (fun p =>
      let d := p.1
      if d + 1 < s ∧ p.2.1 < truncatedMersenneWeight s (d + 1) then some (s, d) else none))
  (hits.length, hits.take 10)

/-! ### SAT the hypotheses of §2

`RemC6.SeamSkipsLast s m` with `m` the largest declined rank and `2*s < 3*m`.
Reported as `(number of rows in [6,200] whose largest declined rank is late,
the exact list of rows where it is NOT late)`. -/

def lastDeclined (s : ℕ) : Option ℕ :=
  ((rowScan s).filterMap (fun p => if p.2.2 then none else some p.1)).getLast?

#eval
  let rs := rows 195
  let late := rs.filter (fun s => match lastDeclined s with
    | some m => decide (2 * s < 3 * m) | none => false)
  let notLate := rs.filterMap (fun s => match lastDeclined s with
    | some m => if 2 * s < 3 * m then none else some (s, m)
    | none => some (s, 0))
  (late.length, notLate)

/-! ### SAT `remainder_lt_of_largest_skip_pred_pred`

rows `s ≥ 7` whose largest declined rank is exactly `s - 2`.  Count over
`s ∈ [7, 200]` and the first twenty. -/

#eval
  let hits := (List.range 194).filterMap (fun i =>
    let s := i + 7
    match lastDeclined s with | some m => if m + 2 = s then some s else none | none => none)
  (hits.length, hits.take 20)

/-! ### SAT `correction_ge`

the hypothesis is `K.bound (s-1) ≤ 2 ^ (s+1) + c`; `D1` inhabits it with
`trivialCeiling` and `c = seamSubsetTarget s + 1`, so the conclusion
`2 ^ (2*s-7) ≤ c` must be a true numeral.  Failures over `s ∈ [12, 40]`;
expected `[]`. -/

#eval (List.range 29).filterMap (fun i =>
  let s := i + 12
  if (2 : ℕ) ^ (2 * s - 7) ≤ seamSubsetTarget s + 1 then none else some s)

/-! ### SAT `tailCorrected_not_intervalCeiling`

its proof needs `weightTail s (s-1) = 4` at every row.  Failures over
`s ∈ [12, 60]`; expected `[]`. -/

#eval (List.range 49).filterMap (fun i =>
  let s := i + 12
  if weightTail' s (s - 1) = 4 then none else some (s, weightTail' s (s - 1)))

/-! ### SAT `branches_decided_of_terminal_lt` / `not_splitsAt_of_terminal_lt`

the hypothesis is `K.hi (s-1) < 2 ^ (s+1) + 4`.  `D1` does **not** exhibit a
`PairCeiling` satisfying it.  For `D1`'s own `orbit s` it reads
`ρ s + 1 < 2 ^ (s+1) + 4`.  Rows in `[6, 300]` where that FAILS; expected `[]`
— but note this rests on the MEASURED fact `ρ s < 2 ^ (s+1)`, not a theorem, so
the class is inhabited only where that measurement has been run. -/

#eval (rows 295).filterMap (fun s =>
  match (rowScan s).getLast? with
  | some p => if p.2.1 + 1 < 2 ^ (s + 1) + 4 then none else some (s, p.2.1)
  | none => some (s, 0))

/-! ### SAT `terminal_ge_of_splits` via `loose_splitsAt_two`

needs `0 < w (s,3) < seamSubsetTarget s + 1`.  Failures over `s ∈ [6, 200]`;
expected `[]`. -/

#eval (rows 195).filterMap (fun s =>
  if 0 < truncatedMersenneWeight s 3 ∧ truncatedMersenneWeight s 3 < seamSubsetTarget s + 1
  then none else some s)

/-! ### SAT `lateEntryRemainder_lt_two_pow_of_declined`

its hypothesis is "rank `d` is declined".  The rank `Bit/Corr1` and `Three/T4`
actually use is `d₀ = ⌊2s/3⌋ + 1`, the first late rank.  Reported as
`(rows scanned, rows where d₀ is DECLINED, first ten such rows)` over
`s ∈ [6, 200]`.  Rows where `d₀` is TAKEN are outside the lemma's reach and
`hhigh` remains a hypothesis there. -/

#eval
  let rs := rows 195
  let usable := rs.filter (fun s =>
    let d := 2 * s / 3 + 1
    match (rowScan s).find? (fun p => p.1 = d) with
    | some p => !p.2.2
    | none => false)
  (rs.length, usable.length, usable.take 10)

/-! ### CHECK `lateEntryRemainder_eq` independently

`BitCorr.lateEntryRemainder s d` against `seamResidualUpto s (d-1)` at every
`2 ≤ d ≤ s`, for `s = 6 … 26`.  Expected `[]`. -/

#eval (rows 21).flatMap (fun s =>
  (List.range (s - 1)).filterMap (fun j =>
    let d := j + 2
    if BitCorr.lateEntryRemainder s d = seamResidualUpto s (d - 1) then none
    else some (s, d)))

/-! ## 4. Independent re-run of every measurement `D1` records -/

/-! ### MEASURED (re-run): the exact failure set of C6's ceiling

`R d < 2 ^ (2*s-d)` over `s ∈ [6, 300]`, every `d ∈ [2, s-1]`.  `D1`'s
measurement note claims the single pair `(13, 7)` over `[6, 1500]`. -/

#eval (rows 295).flatMap (fun s =>
  (rowScan s).filterMap (fun p =>
    if p.2.1 < 2 ^ (2 * s - p.1) then none
    else some (s, p.1, p.2.1, (2 : ℕ) ^ (2 * s - p.1))))

/-! ### MEASURED (re-run): violations of the forced-take law of §1

`2 ^ (2*s-d) ≤ R d` together with `w (d+1) > R d`, over `s ∈ [6, 300]`.  §1 is
PROVED, so this is a transcription check only.  Expected `[]`. -/

#eval (rows 295).flatMap (fun s =>
  (rowScan s).filterMap (fun p =>
    let d := p.1
    if d + 1 ≤ s ∧ 2 ^ (2 * s - d) ≤ p.2.1 ∧ p.2.1 < truncatedMersenneWeight s (d + 1)
    then some (s, d) else none))

/-! ### MEASURED (re-run): the exact suffix-sum identity of §2

at EVERY late `a`, for every `s ∈ [6, 90]` — not only at the first late `a`.
Expected `[]`. -/

#eval (rows 85).flatMap (fun s =>
  (List.range (s + 1)).filterMap (fun a =>
    if 2 * s < 3 * a ∧ a ≤ s then
      (if 3 * (seamWeightsFrom s a).sum + 3 * 2 ^ (s + 1) + 4
            = 3 * 2 ^ (2 * s - a + 1) + 4 ^ (s - a + 1) then none else some (s, a))
    else none))

/-! ### MEASURED (re-run): the sharpened bound of §2

at every row of `[6, 200]` whose largest declined rank `m` is late.
Expected `[]`. -/

#eval (rows 195).filterMap (fun s =>
  match lastDeclined s, (rowScan s).getLast? with
  | some m, some p =>
      if 2 ≤ m ∧ m < s ∧ 2 * s < 3 * m then
        (if 3 * p.2.1 < 3 * 2 ^ (s + 1) + 2 * 4 ^ (s - m) + 4 then none else some (s, m))
      else none
  | _, _ => none)

/-! ### MEASURED (re-run): the distribution of `s - m`

`m` the largest declined rank, over `s ∈ [6, 300]`.  `D1` reports the `[6,1500]`
distribution `1:718, 2:367, 3:191, 4:100, 5:53, 6:30, 7:16, 8:9, 9:5, 10:2,
11:2, 12:1, 13:1`; the shape here must match (geometric, ratio ≈ 1/2). -/

#eval
  let ds := (rows 295).filterMap (fun s =>
    match lastDeclined s with | some m => some (s - m) | none => none)
  (List.range 16).filterMap (fun k =>
    let c := (ds.filter (fun x => x = k)).length
    if c = 0 then none else some (k, c))

/-! ### MEASURED (re-run): `ρ s < 2 ^ (s+1)` and the weight ceiling `R d < w d`

over `s ∈ [6, 300]`.  Both expected `[]`.  Both remain **MEASURED, not proved**;
`D1` says so and this confirms it rather than upgrading it. -/

#eval
  let rhoFail := (rows 295).filterMap (fun s =>
    match (rowScan s).getLast? with
    | some p => if p.2.1 < 2 ^ (s + 1) then none else some (s, p.2.1)
    | none => none)
  let wFail := (rows 295).flatMap (fun s =>
    (rowScan s).filterMap (fun p =>
      if p.2.1 < truncatedMersenneWeight s p.1 then none else some (s, p.1)))
  (rhoFail, wFail)

/-! ### MEASURED: the degenerate row `5`, which `T1` and `D1` exclude

`ρ 5 = 71 > 64 = 2 ^ 6`. -/

#eval (seamIntegerGreedyRemainder 5, (2 : ℕ) ^ 6)

/-! ### The numerals `D1` asserts, re-derived independently

In order: `seamResidualUpto_thirteen_eight` and `thirteen_break_repairs`;
`weightTail_fails_halving`; `lateEntryRemainder_twenty_fifteen` and the §5
anti-vacuity remark about `(20,14)`; `remainder_sixteen_lt_sharp` against C6;
`ρ 14` and `ρ 13`. -/

#eval (seamResidualUpto 13 7, seamResidualUpto 13 8, (2 : ℕ) ^ 18,
       truncatedMersenneWeight 13 8)
#eval (weightTail 13 6, 2 * weightTail 13 7, weightTail 13 7)
#eval (BitCorr.lateEntryRemainder 20 15, truncatedMersenneWeight 20 15,
       BitCorr.lateEntryRemainder 20 14, truncatedMersenneWeight 20 14)
#eval (seamIntegerGreedyRemainder 16, (2 : ℕ) ^ 17 + 12, (2 : ℕ) ^ 17 + 16)
#eval (seamIntegerGreedyRemainder 14, seamIntegerGreedyRemainder 13)

/-! ## 5. The two anti-vacuity gaps, and what fills them

`D1`'s anti-vacuity for §4 exhibits `orbit` (a `PairCeiling` that never splits)
and `loose` (one that does).  It does **not** exhibit a `PairCeiling` satisfying
the hypothesis `hterm : K.hi (s-1) < 2 ^ (s+1) + 4` of
`not_splitsAt_of_terminal_lt` and `branches_decided_of_terminal_lt`.  Without
that, both theorems could be vacuous.  They are not; the witness is proved
here. -/

theorem orbit_thirteen_hi_terminal : (PairCeiling.orbit 13).hi 12 = 15148 := by
  show seamResidualUpto 13 12 + 1 = 15148
  norm_num [seamResidualUpto, seamResidual, truncatedMersenneWeight, seamSubsetTarget]

/-- **PROVED — fills gap 1.**  `orbit 13` is a `PairCeiling 13` whose terminal
upper bound `15148` beats `2 ^ 14 + 4 = 16388`.  So `hterm` is inhabited and
neither `not_splitsAt_of_terminal_lt` nor `branches_decided_of_terminal_lt` is
vacuous. -/
theorem orbit_thirteen_terminal_lt :
    (PairCeiling.orbit 13).hi (13 - 1) < 2 ^ (13 + 1) + 4 := by
  rw [show (13 : ℕ) - 1 = 12 from rfl, orbit_thirteen_hi_terminal]
  norm_num

/-- The conclusion of `branches_decided_of_terminal_lt`, fired on that witness.
For `orbit` it is trivially true — which is exactly `D1` §4's point: a two-sided
invariant that beats `2 ^ (s+1) + 4` has to carry the decline pattern in its
lower bound. -/
theorem branches_decided_thirteen :
    ∀ d, 2 ≤ d → d + 3 ≤ 13 →
      (truncatedMersenneWeight 13 (d + 1) ≤ seamResidualUpto 13 d
        ↔ truncatedMersenneWeight 13 (d + 1) ≤ (PairCeiling.orbit 13).lo d) :=
  PairCeiling.branches_decided_of_terminal_lt orbit_thirteen_terminal_lt

#print axioms orbit_thirteen_terminal_lt
#print axioms branches_decided_thirteen

/-- **PROVED — gap 2, stated as a negative.**  `BrokenAt.not_restored`'s
hypothesis `hbig` FAILS at `(13,7)`, the corpus's only broken state in
`[6, 3000]`: there `R 7 = 524419` while
`2 ^ 19 + weightTail 13 8 = 524288 + 1028 = 525316`.  So at the one place where
`BrokenAt` is inhabited, `not_restored` cannot fire.  `D1` exhibits only the
`restored` branch (`thirteen_break_repairs`) and does not record that
`not_restored` is unwitnessed. -/
theorem not_restored_hypothesis_fails_at_thirteen :
    seamResidualUpto 13 7 < 2 ^ (2 * 13 - 7) + weightTail 13 8 := by
  rw [seamResidualUpto_thirteen_seven]
  norm_num [weightTail, truncatedMersenneWeight]

#print axioms not_restored_hypothesis_fails_at_thirteen

/-- Companion: `BrokenAt.restored` DOES fire there.  So the pair
`restored` / `not_restored` is half-inhabited on corpus data, not inhabited. -/
theorem restored_hypothesis_holds_at_thirteen :
    seamResidualUpto 13 8 < 2 ^ (2 * 13 - (7 + 1)) :=
  brokenAt_thirteen_seven.restored (by norm_num) (by norm_num)
    not_restored_hypothesis_fails_at_thirteen

#print axioms restored_hypothesis_holds_at_thirteen

/-! ## 6. What `D1` does not establish

`ρ s < 2 ^ (s+1)` is not a theorem in `D1` or in anything it imports.  The
strongest unconditional statement `D1` reaches is
`remainder_lt_of_late_largest_skip_sharp`, which carries **both**
`RemC6.SeamSkipsLast s d` and `2 * s < 3 * d`; and `sharp_strictly_beats_C6`
shows it improves C6's constant, not C6's shape.
`T1.IntervalCeiling.two_pow_lt` still says no interval induction reaches
`2 ^ (s+1)`, and `D1` §3/§4 only widen that no-go.  The only unconditional
numeric consequences are at the rows where `RemC6` supplies a proved
`SeamSkipsLast` witness. -/

theorem sharp_at_sixteen : seamIntegerGreedyRemainder 16 < 2 ^ 17 + 12 :=
  remainder_sixteen_lt_sharp

#print axioms sharp_at_sixteen

/-! ## 7. §5 replaces a hypothesis by a strictly stronger one

`D1` presents `lateEntryRemainder_lt_two_pow_of_declined` as the *discharge* of
`hhigh`.  It is not a discharge: its hypothesis "rank `d` is declined",
`L < truncatedMersenneWeight s d`, **strictly implies** its conclusion
`L < 2 ^ (2*s-d+1)` by one line of arithmetic, because `RemC6` already proves
`truncatedMersenneWeight s d ≤ 2 ^ (2*s-d) + 2 ^ (2*s-2*d+1) ≤ 2 ^ (2*s-d+1)`
at every rank of every row.  The proof below uses **no** part of `D1`: not §1's
forced-take law, not `weight_succ_le_of_two_pow_le`, not
`residual_lt_two_pow_of_declined`, not `lateEntryRemainder_eq`.  It is `RemC6`
alone.  Since the implication is strict, §5 narrows the hypothesis rather than
removing it. -/

/-- **PROVED, from `RemC6` alone.**  Any quantity below the rank-`d` weight is
below `2 ^ (2*s-d+1)`.  No greedy, no residual, no §1. -/
theorem hhigh_is_weaker_than_declined {s d L : ℕ} (hd : 1 ≤ d) (hds : d ≤ s)
    (h : L < truncatedMersenneWeight s d) :
    L < 2 ^ (2 * s - d + 1) := by
  have hup := RemC6.truncatedMersenneWeight_le (s := s) (d := d) hd hds
  have hmono : (2 : ℕ) ^ (2 * s - 2 * d + 1) ≤ 2 ^ (2 * s - d) :=
    Nat.pow_le_pow_right (by norm_num) (by omega)
  have hsum : (2 : ℕ) ^ (2 * s - d) + 2 ^ (2 * s - d) = 2 ^ (2 * s - d + 1) := by
    rw [pow_succ]; ring
  omega

/-- Consequently `D1`'s headline §5 lemma is a one-line corollary of `RemC6`,
reproved here without touching `D1`. -/
theorem lateEntryRemainder_hhigh_of_declined' {s d : ℕ} (hd : 1 ≤ d) (hds : d ≤ s)
    (h : BitCorr.lateEntryRemainder s d < truncatedMersenneWeight s d) :
    BitCorr.lateEntryRemainder s d < 2 ^ (2 * s - d + 1) :=
  hhigh_is_weaker_than_declined hd hds h

/-- And `D1`'s §5 anti-vacuity certificate follows the same way. -/
theorem hhigh_twenty_fifteen' :
    BitCorr.lateEntryRemainder 20 15 < 2 ^ (2 * 20 - 15 + 1) :=
  lateEntryRemainder_hhigh_of_declined' (by norm_num) (by norm_num) declined_twenty_fifteen

#print axioms hhigh_is_weaker_than_declined
#print axioms lateEntryRemainder_hhigh_of_declined'
#print axioms hhigh_twenty_fifteen'

/-! ### MEASURED: how much §5 costs

At `Three/T4`'s own rank `d₀ = ⌊2s/3⌋ + 1`, reported as
`(rows in [6,200], rows where `hhigh` holds, rows where `d₀` is DECLINED)`.
`T4`'s measurement note says `hhigh` holds at all 795 rows of `[6,800]`.  If the
middle number is the row count and the last is strictly smaller, then `D1` §5
covers strictly fewer rows than the hypothesis it claims to discharge. -/

#eval
  let rs := rows 195
  let hhighOK := rs.filter (fun s =>
    let d := 2 * s / 3 + 1
    decide (d < s) && decide (BitCorr.lateEntryRemainder s d < 2 ^ (2 * s - d + 1)))
  let declined := rs.filter (fun s =>
    let d := 2 * s / 3 + 1
    match (rowScan s).find? (fun p => p.1 = d) with
    | some p => !p.2.2
    | none => false)
  (rs.length, hhighOK.length, declined.length)

/-! ### MEASURED: the same at `Bit/Corr1`'s and `Three/T4`'s certified rows

`(s, d, hhigh?, declined?)` at `(14,10)`, `(20,14)`, `(12,9)` — the three rows
carrying a proved `LateEntryAdmissible` — and at `(20,15)`, `D1`'s own witness.
Any row with `hhigh? = true, declined? = false` is a row where `T4` needs
`hhigh` and `D1` §5 cannot supply it. -/

#eval [(14, 10), (20, 14), (12, 9), (20, 15), (13, 8)].map (fun p =>
  let s := p.1
  let d := p.2
  (s, d,
   decide (BitCorr.lateEntryRemainder s d < 2 ^ (2 * s - d + 1)),
   decide (BitCorr.lateEntryRemainder s d < truncatedMersenneWeight s d)))

/-! ## 8. Two prose claims of `D1` that carry no Lean statement

**(a) §3's "a fortiori".**  `D1` writes that the *narrowed* family
`d ↦ 2 ^ (2*s-d) - weightTail s d` — which is the brief's actual candidate — is
"smaller still, hence excluded a fortiori", but states no theorem for it.  The
claim is TRUE; here is the missing three-line proof. -/

theorem narrowedTail_not_intervalCeiling {s : ℕ} (hs : 12 ≤ s) :
    ¬ ∃ K : IntervalCeiling s, K.bound = fun d => 2 ^ (2 * s - d) - weightTail s d := by
  rintro ⟨K, hK⟩
  have hb : K.bound (s - 1) ≤ 2 ^ (s + 1) + 0 := by
    have hval : K.bound (s - 1) = 2 ^ (2 * s - (s - 1)) - weightTail s (s - 1) := by rw [hK]
    rw [hval, show 2 * s - (s - 1) = s + 1 by omega]
    exact le_trans (Nat.sub_le _ _) (Nat.le_add_right _ 0)
  have h0 := correction_ge hs K 0 hb
  have hpos : 0 < (2 : ℕ) ^ (2 * s - 7) := pow_pos (by norm_num) _
  omega

#print axioms narrowedTail_not_intervalCeiling

/-! **(b) §4's rank range.**  `D1`'s §4 summary says a two-sided invariant with
`hi (s-1) < 2 ^ (s+1) + 4` has its branch decided "at every rank `d ≤ s-2`".
The theorem delivers `d + 3 ≤ s`, i.e. `d ≤ s - 3`.  The `#check` below is the
statement as it actually is. -/

#check @ErdosProblems.Decl.D1.PairCeiling.branches_decided_of_terminal_lt

end ErdosProblems.Decl.VerifyD1
