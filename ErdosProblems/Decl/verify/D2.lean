/-
Copyright (c) 2026 Will Cook. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Will Cook
-/
import ErdosProblems.Decl.D2

/-!
# Adversarial verification of `ErdosProblems/Decl/D2.lean`

* §1  Axiom audit of every declaration of D2 (`#print axioms`).
* §2  Independent re-derivation of every numeral D2 asserts.
* §3  **Satisfiability**: every non-trivial hypothesis of D2 is `#eval`'d on real
      corpus data over a wide range of rows, with exact counts and exact
      witness/failure sets — not summary statistics.
* §4  The exact identity `blockRun_worst_invariant` and the excess bound
      `blockRun_worst_excess` re-checked numerically, and the *sharpness* of the
      no-go probed: is the excess really positive at every `(s, d)`?
* §5  D2's §7 measurement note re-run inside Lean on an independent
      reimplementation of the greedy (cross-checked against the corpus
      definition rank by rank).
* §6  Adversarial probes: is any headline a trivially-true disjunct, is any
      hypothesis as hard as its conclusion, and does D2 give `ρ s < 2 ^ (s+1)`?
-/

open Erdos249257 Erdos249257.HalfCylinderIntegerGreedy
open ErdosProblems.Three.T1
open ErdosProblems.Decl.D2

namespace ErdosProblems.Decl.VerifyD2

/-! ## 1. Axiom audit — every declaration of D2 -/

#print axioms ErdosProblems.Decl.D2.declineBlock_self
#print axioms ErdosProblems.Decl.D2.takeBlock_self
#print axioms ErdosProblems.Decl.D2.residual_eq_of_declineBlock
#print axioms ErdosProblems.Decl.D2.residual_lt_weight_of_declineBlock
#print axioms ErdosProblems.Decl.D2.residual_lt_weight_first_of_declineBlock
#print axioms ErdosProblems.Decl.D2.declineBlock_gain
#print axioms ErdosProblems.Decl.D2.residual_lt_two_pow_add_of_declineBlock
#print axioms ErdosProblems.Decl.D2.residual_excess_le_of_takeBlock
#print axioms ErdosProblems.Decl.D2.residual_lt_of_lastDecline
#print axioms ErdosProblems.Decl.D2.seamRemainder_lt_of_lastDecline
#print axioms ErdosProblems.Decl.D2.seamRemainder_lt_two_pow_succ_add
#print axioms ErdosProblems.Decl.D2.two_pow_add_two_pow_le_weight
#print axioms ErdosProblems.Decl.D2.weight_eq_two_pow_add_weightTail
#print axioms ErdosProblems.Decl.D2.two_pow_le_weightTail
#print axioms ErdosProblems.Decl.D2.weightTail_le
#print axioms ErdosProblems.Decl.D2.three_mul_weightTail_sum_le
#print axioms ErdosProblems.Decl.D2.blockRun_zero
#print axioms ErdosProblems.Decl.D2.blockRun_succ
#print axioms ErdosProblems.Decl.D2.worstDeclined_lt
#print axioms ErdosProblems.Decl.D2.blockRun_worst_invariant
#print axioms ErdosProblems.Decl.D2.two_pow_le_blockRun_worst
#print axioms ErdosProblems.Decl.D2.blockRun_worst_takes
#print axioms ErdosProblems.Decl.D2.blockRun_worst_excess
#print axioms ErdosProblems.Decl.D2.no_blockMethod_closure
#print axioms ErdosProblems.Decl.D2.not_blockMethod_sound
#print axioms ErdosProblems.Decl.D2.blockMethod_excess_window
#print axioms ErdosProblems.Decl.D2.residual_excess_lt_weightTail
#print axioms ErdosProblems.Decl.D2.Concrete.declineBlock_twenty
#print axioms ErdosProblems.Decl.D2.Concrete.takeBlock_twenty_fourteen
#print axioms ErdosProblems.Decl.D2.Concrete.declineBlock_twenty_late
#print axioms ErdosProblems.Decl.D2.Concrete.seamResidualUpto_twenty_thirteen
#print axioms ErdosProblems.Decl.D2.Concrete.run_collapse_twenty
#print axioms ErdosProblems.Decl.D2.Concrete.invariant_holds_twenty
#print axioms ErdosProblems.Decl.D2.Concrete.seamRemainder_twenty_lt
#print axioms ErdosProblems.Decl.D2.Concrete.declineBlock_thirteen
#print axioms ErdosProblems.Decl.D2.Concrete.thirteen_run_length_one
#print axioms ErdosProblems.Decl.D2.Concrete.takeBlock_thirteen
#print axioms ErdosProblems.Decl.D2.Concrete.run_of_length_one_breaks_invariant
#print axioms ErdosProblems.Decl.D2.Concrete.seamRemainder_thirteen_lt
#print axioms ErdosProblems.Decl.D2.Concrete.worstDeclined_twenty_six
#print axioms ErdosProblems.Decl.D2.Concrete.blockRun_twenty_six
#print axioms ErdosProblems.Decl.D2.Concrete.blockRun_twenty_six_exceeds
#print axioms ErdosProblems.Decl.D2.Concrete.weightTail_twenty_six
#print axioms ErdosProblems.Decl.D2.Concrete.no_blockMethod_closure_twenty

/-! ## 2. Independent re-derivation of D2's numerals

Every numeral D2 asserts, recomputed from the corpus definitions by `#eval`
(which uses the compiler, not the tactic that proved them). -/

/-! D2 asserts `seamResidualUpto 20 13 = 67662313`. -/
#eval seamResidualUpto 20 13
/-! D2's docstring asserts `w 20 13 = 134234114` and `w 20 8 = 4311810305`. -/
#eval (truncatedMersenneWeight 20 13, truncatedMersenneWeight 20 8)
/-! D2 asserts `worstDeclined 20 6 = 17452565519`, `weightTail 20 6 = 272696336`. -/
#eval (worstDeclined 20 6, weightTail 20 6)
/-! D2 asserts `blockRun 20 6 (worstDeclined 20 6) 7 = 316837451`, ceiling `2^27`. -/
#eval (blockRun 20 6 (worstDeclined 20 6) 7, 2 ^ (2 * 20 - 13),
        decide (2 ^ (2 * 20 - 13) ≤ blockRun 20 6 (worstDeclined 20 6) 7))
/-! T1's `ρ 13 = 15147` and `seamResidualUpto 13 7 = 524419` (D2 leans on both). -/
#eval (seamIntegerGreedyRemainder 13, seamResidualUpto 13 7, 2 ^ (2 * 13 - 7))
/-! `run_collapse_twenty`'s second conjunct, in numbers. -/
#eval (2 ^ (13 - 7 - 1) * truncatedMersenneWeight 20 13, truncatedMersenneWeight 20 8)

/-! ## 3. SATISFIABILITY of every non-trivial hypothesis, on real data

An efficient Boolean replica of the descending seam greedy.  §5 cross-checks it
against the corpus `seamResidualUpto` rank by rank, so the scans below really are
about the corpus's own object. -/

/-- `rowResiduals s = [(d, seamResidualUpto s d, taken?) | d = 2 … s-1]`, computed
once per row instead of once per rank. -/
def rowScan (s : ℕ) : List (ℕ × ℕ × Bool) :=
  let rec go : ℕ → ℕ → ℕ → List (ℕ × ℕ × Bool)
    | 0, _, _ => []
    | fuel + 1, d, r =>
        if d < s then
          let w := truncatedMersenneWeight s d
          if w ≤ r then (d, r - w, true) :: go fuel (d + 1) (r - w)
          else (d, r, false) :: go fuel (d + 1) r
        else []
  go s 2 (seamSubsetTarget s)

/-- The decline/take word of a row, as a string (`.` = declined, `T` = taken). -/
def rowWord (s : ℕ) : String :=
  (rowScan s).foldl (fun acc p => acc ++ (if p.2.2 then "T" else ".")) ""

/-- The residual after rank `d`, from the fast scan. -/
def fastResidual (s d : ℕ) : ℕ :=
  if d ≤ 1 then seamSubsetTarget s
  else ((rowScan s).filter (fun p => p.1 == d)).foldl (fun _ p => p.2.1) 0

/-- Decidable replica of `DeclineBlock s a b`. -/
def declineBlockB (s a b : ℕ) : Bool :=
  (List.range b).all fun k => !(a ≤ k) || (fastResidual s k < truncatedMersenneWeight s (k + 1))

/-- Decidable replica of `TakeBlock s a b`. -/
def takeBlockB (s a b : ℕ) : Bool :=
  (List.range b).all fun k => !(a ≤ k) || (truncatedMersenneWeight s (k + 1) ≤ fastResidual s k)

/-! Sanity: the replicas agree with D2's own certificates. -/
#eval (declineBlockB 20 7 13, takeBlockB 20 13 14, declineBlockB 20 14 19,
        declineBlockB 13 6 7, takeBlockB 13 7 12)

/-! The decline/take words of the two certificate rows, for eyeball comparison
with D2's prose (ranks `2 … s-1`). -/
#eval (rowWord 13, rowWord 20)

/-- All maximal decline runs of a row, as `(first rank, length)`. -/
def runsOf (s : ℕ) : List (ℕ × ℕ) :=
  let step : (List (ℕ × ℕ) × Option (ℕ × ℕ)) → (ℕ × ℕ × Bool) → (List (ℕ × ℕ) × Option (ℕ × ℕ))
    | (acc, cur), (d, _, tk) =>
        if tk then
          match cur with
          | none => (acc, none)
          | some p => (acc ++ [p], none)
        else
          match cur with
          | none => (acc, some (d, 1))
          | some (a, n) => (acc, some (a, n + 1))
  let (acc, cur) := (rowScan s).foldl step ([], none)
  match cur with
  | none => acc
  | some p => acc ++ [p]

/-- Only the decline runs actually CLOSED by a taken rank — the convention D2 §7
uses for its "first closed run of each length" table.  (Runs that hit the end of
the row at rank `s - 1` are dropped.) -/
def closedRunsOf (s : ℕ) : List (ℕ × ℕ) :=
  (runsOf s).filter fun p => p.1 + p.2 < s

/-! **Satisfiability of `DeclineBlock` with `a < b` (the non-degenerate case).**
For every row of `[6, 300]` the list of maximal decline runs is nonempty, so the
hypothesis of `residual_lt_weight_of_declineBlock`,
`residual_lt_weight_first_of_declineBlock` and
`residual_lt_two_pow_add_of_declineBlock` is met at every row.  Printed: the
number of rows of `[6,300]` with NO decline run (`0` means never vacuous), and
the total number of runs. -/
#eval
  let rows := (List.range 295).map (· + 6)
  let runs := rows.map fun s => (runsOf s).length
  (runs.filter (· == 0) |>.length, runs.foldl (· + ·) 0)

/-- **Satisfiability of the master bound's full hypothesis set.**  For each row
`s` of `[6, 300]` we locate the LAST declined rank `b` and check, by the
decidable replicas, that `DeclineBlock s (b-1) b` and `TakeBlock s b (s-1)` both
hold — i.e. `residual_lt_of_lastDecline`, `seamRemainder_lt_of_lastDecline` and
`seamRemainder_lt_two_pow_succ_add` all fire.  Printed: the exact set of rows
where they do NOT (empty = the hypotheses are satisfiable at every row). -/
def lastDeclined (s : ℕ) : Option ℕ :=
  ((rowScan s).filter (fun p => !p.2.2)).foldl (fun _ p => some p.1) none

#eval
  let rows := (List.range 295).map (· + 6)
  rows.filter fun s =>
    match lastDeclined s with
    | none => true
    | some b => !(2 ≤ b && b ≤ s - 1 && declineBlockB s (b - 1) b && takeBlockB s b (s - 1))

/-! The last declined rank of a few rows, with the bound
`seamRemainder_lt_two_pow_succ_add` then delivers, against the truth.
Format: `(s, b, ρ s, 2^(s+1) + 2^(2s-2b+1))`. -/
#eval ([13, 20, 21, 40, 60, 80].map fun s =>
  match lastDeclined s with
  | none => (s, 0, 0, 0)
  | some b => (s, b, seamIntegerGreedyRemainder s,
      2 ^ (s + 1) + 2 ^ (2 * s - 2 * b + 1)))

/-! **Satisfiability of `TakeBlock` with `a < b`.**  `residual_excess_le_of_takeBlock`
and `residual_lt_of_lastDecline` need a NON-EMPTY take block, i.e. at least one
taken rank.  Printed: `(rows of [6,300] with no taken rank at all,
rows with no block of two consecutive taken ranks)`.  D2's own certificate
`takeBlock_twenty_fourteen` is a length-`1` block, so the first number is the
relevant one.  (`a` starts at `1`, the smallest value `residual_lt_of_lastDecline`
allows, so that the block of ranks `2,3` is not missed.) -/
#eval
  let rows := (List.range 295).map (· + 6)
  ((rows.filter fun s =>
      !((List.range (s - 2)).any fun i => takeBlockB s (i + 1) (i + 2))),
   (rows.filter fun s =>
      !((List.range (s - 2)).any fun i => takeBlockB s (i + 1) (i + 3))))

/-! **The no-go probed against reality at the one row where the invariant fails.**
Row `13`, ranks `7 … 12`: the worst-case model `blockRun 13 7 (w 13 7 - 1) n`,
the ceiling `2 ^ (2*13-(7+n))`, and the TRUE residual.  The model sits above the
ceiling at every rank while the true residual drops below it from rank `8` on —
and the two differ by under `1%`.  So the information the block method discards
is small, and discarding it is exactly what is fatal.  Format
`(rank, model, ceiling, true residual)`. -/
#eval (List.range 6).map fun n =>
  (7 + n, blockRun 13 7 (worstDeclined 13 7) n, 2 ^ (2 * 13 - (7 + n)),
    fastResidual 13 (7 + n))

/-! **Non-vacuity of `three_mul_weightTail_sum_le` as an inequality** — i.e. the
sum it bounds is not identically zero.  Printed: the number of `(s,d)` with
`1 ≤ d < s - 1`, `s ∈ [6,60]`, whose tail sum is `0` (should be `0`). -/
#eval
  let pairs := (List.range 55).flatMap fun i =>
    let s := i + 6
    (List.range (s - 2)).map fun j => (s, j + 1)
  (pairs.filter fun p =>
    (Finset.Ico (p.2 + 1) p.1).sum (fun j => weightTail p.1 j) == 0).length

/-! ## 4. The no-go re-checked numerically, and probed for sharpness -/

/-! `blockRun_worst_invariant` is an exact identity.  Re-checked over all
`s ∈ [6,40]`, `1 ≤ d < s`, `d + n < s`: printed is the exact set of failures. -/
#eval
  let triples := (List.range 35).flatMap fun i =>
    let s := i + 6
    (List.range (s - 1)).flatMap fun j =>
      let d := j + 1
      (List.range (s - d)).map fun n => (s, d, n)
  (triples.filter fun t =>
    let s := t.1; let d := t.2.1; let n := t.2.2
    !(blockRun s d (worstDeclined s d) n
        + (Finset.Ico (d + 1) (d + n + 1)).sum (fun j => weightTail s j) + 1
      == 2 ^ (2 * s - (d + n)) + weightTail s d)).take 20

/-! `two_pow_le_blockRun_worst` — the counter-model never gets under the ceiling.
Exact failure set over `s ∈ [6,40]`. -/
#eval
  let triples := (List.range 35).flatMap fun i =>
    let s := i + 6
    (List.range (s - 1)).flatMap fun j =>
      let d := j + 1
      (List.range (s - d)).map fun n => (s, d, n)
  (triples.filter fun t =>
    let s := t.1; let d := t.2.1; let n := t.2.2
    !(2 ^ (2 * s - (d + n)) ≤ blockRun s d (worstDeclined s d) n)).take 20

/-! **Sharpness probe.**  The no-go is only interesting if the excess is a real
obstruction, i.e. strictly positive.  Printed: the exact set of `(s,d,n)` in
`s ∈ [6,40]` where the excess `blockRun - 2^(2s-(d+n))` is `0`
(empty = the counter-model strictly exceeds the ceiling everywhere), and the
minimum excess/`weightTail s d` ratio numerator/denominator seen. -/
#eval
  let triples := (List.range 35).flatMap fun i =>
    let s := i + 6
    (List.range (s - 1)).flatMap fun j =>
      let d := j + 1
      (List.range (s - d)).map fun n => (s, d, n)
  (triples.filter fun t =>
    let s := t.1; let d := t.2.1; let n := t.2.2
    blockRun s d (worstDeclined s d) n - 2 ^ (2 * s - (d + n)) == 0).take 20

/-! **The repayment ratio, re-measured.**  D2 §7 claims the sharper
`3 * tail ≤ weightTail s d` holds with no violation over `s ∈ [6,120]`,
`d ∈ [2,s-2]`, and that the PROVED bound is `3 * tail ≤ 2 * weightTail s d`.
Printed here over the WIDER range `s ∈ [6,90]`, `d ∈ [1,s-1]`:
`(violations of 3*tail ≤ 2*wt, violations of 3*tail ≤ wt)`.  Both should be
empty; the second being empty confirms the measured claim on a wider `d` range
than D2 scanned. -/
#eval
  let pairs := (List.range 85).flatMap fun i =>
    let s := i + 6
    (List.range (s - 1)).map fun j => (s, j + 1)
  let tail := fun (p : ℕ × ℕ) => (Finset.Ico (p.2 + 1) p.1).sum (fun j => weightTail p.1 j)
  ((pairs.filter fun p => !(3 * tail p ≤ 2 * weightTail p.1 p.2)).take 10,
   (pairs.filter fun p => !(3 * tail p ≤ weightTail p.1 p.2)).take 10)

/-! ## 5. D2 §7 re-run inside Lean

First: the fast replica is the corpus greedy.  Cross-checked at every rank of
every row of `[6,60]`; printed is the exact disagreement set. -/

#eval
  let pairs := (List.range 55).flatMap fun i =>
    let s := i + 6
    (List.range (s - 2)).map fun j => (s, j + 2)
  (pairs.filter fun p => !(fastResidual p.1 p.2 == seamResidualUpto p.1 p.2)).take 20

/-! **C6's ceiling, re-scanned.**  Exact failure set of
`seamResidualUpto s d < 2 ^ (2*s-d)` over `s ∈ [6,300]`, `d ∈ [2,s-1]`.
D2 §7 claims exactly one failure, `(13,7)`. -/
#eval
  let rows := (List.range 295).map (· + 6)
  rows.flatMap fun s =>
    ((rowScan s).filter fun p => !(p.2.1 < 2 ^ (2 * s - p.1))).map fun p => (s, p.1)

/-! **T1's corrected ceiling, re-scanned.**  Exact failure set of
`seamResidualUpto s d < truncatedMersenneWeight s d` over the same range.
D2 §7 claims none. -/
#eval
  let rows := (List.range 295).map (· + 6)
  (rows.flatMap fun s =>
    ((rowScan s).filter fun p => !(p.2.1 < truncatedMersenneWeight s p.1)).map
      fun p => (s, p.1)).take 20

/-! **`ρ s < 2 ^ (s+1)`, re-scanned.**  Exact set of rows of `[6,300]` where it
fails.  D2 §7 claims none — but this is MEASURED, not proved, and D2 does not
claim to have proved it. -/
#eval
  let rows := (List.range 295).map (· + 6)
  rows.filter fun s => !(fastResidual s (s - 1) < 2 ^ (s + 1))

/-! **T4's `hhigh` at the first late rank, re-scanned.**  Exact failure set over
`[6,300]`. -/
#eval
  let rows := (List.range 295).map (· + 6)
  rows.filter fun s =>
    let d0 := 2 * s / 3 + 1
    !(fastResidual s (d0 - 1) < 2 ^ (2 * s - d0 + 1))

/-! **The decline-run histogram, re-measured.**  Over `s ∈ [6,300]`: the maximal
run length, and the full length histogram as `(length, count)` over ALL maximal
runs.  D2 §7 reports max `9` over `[6,800]`, first attained at `s = 513`. -/
#eval
  let rows := (List.range 295).map (· + 6)
  let all := rows.flatMap fun s => (runsOf s).map fun p => p.2
  let mx := all.foldl max 0
  (mx, (List.range mx).map fun i => (i + 1, (all.filter (· == i + 1)).length))

/-! Histogram restricted to CLOSED runs, D2 §7's other table. -/
#eval
  let rows := (List.range 295).map (· + 6)
  let all := rows.flatMap fun s => (closedRunsOf s).map fun p => p.2
  let mx := all.foldl max 0
  (mx, (List.range mx).map fun i => (i + 1, (all.filter (· == i + 1)).length))

/-! The first row carrying a CLOSED run of each length, and where the run starts.
D2 §7's table: `1:(9,7) 2:(7,4) 3:(74,67) 4:(27,22) 5:(21,15) 6:(20,8) 7:(16,8)
8:(123,114) 9:(513,503)`.  (Restricted to `[6,300]`, so length `9` is out of
range and must come back `none`.) -/
#eval
  let rows := (List.range 295).map (· + 6)
  (List.range 9).map fun i =>
    let L := i + 1
    let hits := rows.flatMap fun s =>
      ((closedRunsOf s).filter fun p => p.2 == L).map fun p => (s, p.1)
    (L, hits.head?)

/-! ## 6. Adversarial probes

**Probe A — is `no_blockMethod_closure` about reachable residuals?**  It is
not: the witness is `worstDeclined s d = w d - 1`, which is an ARBITRARY natural
satisfying the decline inequality, not a residual the greedy ever reaches.  This
is deliberate and D2 says so, but the probe records the gap in numbers: for each
row, the true residual entering rank `d` (when `d` is declined) versus the
witness `w d - 1`, at the last declined rank.  Format
`(s, b, seamResidualUpto s (b-1), worstDeclined s b)`. -/
#eval ([13, 20, 40, 60].map fun s =>
  match lastDeclined s with
  | none => (s, 0, 0, 0)
  | some b => (s, b, fastResidual s (b - 1), worstDeclined s b))

/-! **Probe B — does D2 deliver `ρ s < 2 ^ (s+1)`?**  Its strongest remainder
bound is `seamRemainder_lt_two_pow_succ_add`:
`ρ s < 2^(s+1) + 2^(2s-2b+1)`.  Printed: for `s ∈ [6,120]`, the number of rows
where that bound is `< 2^(s+1)` (must be `0` — the bound is strictly weaker than
the target by construction), and the number where the ADDED term already exceeds
`2^(s+1)` (i.e. the bound is worse than useless as a route to the target). -/
#eval
  let rows := (List.range 115).map (· + 6)
  let bnd := fun s => match lastDeclined s with
    | none => 0
    | some b => 2 ^ (2 * s - 2 * b + 1)
  ((rows.filter fun s => 2 ^ (s + 1) + bnd s < 2 ^ (s + 1)).length,
   (rows.filter fun s => 2 ^ (s + 1) ≤ bnd s).length)

/-- **Probe C — is `declineBlock_gain` doing any work?**  It is a pure exponent
identity with no reference to the greedy: it holds for every `a < b ≤ 2*s`,
including `s = 0`.  Recorded as a theorem so the claim is not merely asserted. -/
theorem declineBlock_gain_is_pure_arithmetic :
    ∀ a b : ℕ, a < b → b ≤ 2 * 0 →
      2 ^ (b - a - 1) * 2 ^ (2 * 0 - b) = 2 ^ (2 * 0 - a - 1) :=
  fun _ _ hab hb => declineBlock_gain hab hb

/-! **Probe D — the degenerate instantiations are genuinely degenerate.**
`seamRemainder_twenty_lt` is instantiated with `takeBlock_self 20 19`, i.e. the
EMPTY take block, and `declineBlock_twenty_late` with `b = s - 1 = 19`.  So the
row-20 headline bound is `ρ 20 < 2^21 + 2^3`.  Printed: that bound and the true
`ρ 20`. -/
#eval (2 ^ (20 + 1) + 2 ^ (2 * 20 - 2 * 19 + 1), seamIntegerGreedyRemainder 20)

/-! **Probe E — `run_of_length_one_breaks_invariant`'s second conjunct is exactly
`T1.not_residualInvariant`'s witness.**  Nothing new is proved about the
invariant; what is new is the run length.  Recorded: the row-13 run containing
rank `7` has length `1`. -/
#eval (runsOf 13, runsOf 20)

/-! **Probe F — could a bound on the run length have helped anyway?**  D2 claims
run length and invariant failure are anti-correlated.  Printed: over `s ∈
[6,300]`, the exact set of `(s, d)` where C6's ceiling fails, paired with the
length of the decline run containing `d` (or `0` if `d` is taken). -/
#eval
  let rows := (List.range 295).map (· + 6)
  rows.flatMap fun s =>
    ((rowScan s).filter fun p => !(p.2.1 < 2 ^ (2 * s - p.1))).map fun p =>
      (s, p.1, ((runsOf s).filter fun q => q.1 ≤ p.1 && p.1 < q.1 + q.2).map (·.2))

end ErdosProblems.Decl.VerifyD2
