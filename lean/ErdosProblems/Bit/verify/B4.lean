/-
Copyright (c) 2026 Will Cook. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Will Cook
-/
import ErdosProblems.Bit.R1

/-!
# B4: adversarial audit of `ErdosProblems/Bit/R1.lean`

This file *only* audits.  It states no new mathematics of its own beyond a
handful of concrete counter-witnesses; everything else is `#print axioms` and
`#eval`.  It is expected to produce output.  What must be checked is that the
output contains **no** `error`, **no** `warning`, and that every axiom line reads
exactly `[propext, Classical.choice, Quot.sound]`.

## What is audited

1. **Axioms.**  Every named theorem of `R1`, plus the two upstream results the
   whole reduction rests on (`AngleD2.half_mem_iff_unboundedLargestSkipLate`,
   `AngleD2.mem_of_late_of_not_largestSkipLateAt`).

2. **Satisfiability of every hypothesis**, by `#eval` on real rows.  The
   auditor's replicas `lfrOf` / `lateB` / `topMemB` are built *from the corpus's
   own* `SkipD3.gb` and `BitR1.remOf`, so they cannot drift from the definitions
   the theorems are about.

3. **Non-triviality of the certificate**: the correction
   `c s = 4 * R s - R (s+1) - 2 ^ (s+1)` is evaluated over a wide range, and its
   silent rows are exhibited.

## Findings recorded here (see the report for detail)

* `remainder_step_of_top_mem`     — hypothesis holds at 258 of the 497 rows
  `s ∈ [5, 501]`.  Richly non-vacuous.
* `remainder_step_of_not_largestSkipLateAt` — hypothesis holds at exactly three
  rows of `[5, 501]`, namely `s = 10, 11, 12`.  Non-vacuous, but only just.
* `largestSkipLateAt_succ_of_ascent / _descent / _of_window_miss` — hypothesis
  holds at 239 of 497 rows.  Richly non-vacuous, and *not* trivially true: at
  `s = 1498` the kernel refutes both halves (see `§5`).
* `exists_largestSkipLateAt_of_remainder_small` — hypothesis holds at 231 rows.
* `stepLaw_iterate` — hypothesis witnessed by `stepLaw_pow_add_two`.
* **`remainder_ge_of_no_late_window` — hypothesis holds at NO row of `[5, 240]`,
  and cannot hold anywhere `LargestSkipLateAt` is as dense as it is measured to
  be: its hypothesis needs `s + 2 ≥ 7` consecutive non-late rows and the longest
  such run over `[5, 501]` has length `3`.**  As a standalone implication it is
  empirically vacuous; it is sound and useful only through its contrapositive
  `exists_largestSkipLateAt_of_remainder_small`, whose hypothesis *is*
  satisfiable.  `§6` proves the hypothesis false at `s = 5` and `s = 13`
  outright.  `R1`'s docstring claim that this lemma is "witnessed above" is
  not borne out — no witness for it appears in `R1 §9`.
* `remainder_le_of_forcedRun_of_growth` / `remainder_band_of_forcedRun_of_growth`
  / `remainder_ge_of_forcedRun` / `forcedRun_defect_window` / `stepLaw_of_forcedRun`
  — all carry `ForcedRun N`, for which no witness exists or is claimed; `R1`'s
  own docstring flags them as possibly vacuous.  The growth side condition is
  separately measured: it fails only at `s = 5` over `[5, 501]`.
* The band `[2^s+2, 2^s+2s+1]` is met at exactly one row of `[6, 501]`, `s = 8`.
  This is *not* evidence against `ForcedRun`: the 231 rows that miss the band low
  are exactly the rows where `R s < 2 ^ s + 2`, and `LargestSkipLateAt` holds at
  all but four rows anyway, so `ForcedRun`'s hypothesis is false there to begin
  with.

## Reach, versus the pre-existing corpus machinery

`R1 §8` describes rows `1500`/`1501` as "far beyond anything the corpus has
certified by inspecting a greedy word".  Checked out of tree, the corpus's own
`SkipD3.largestSkipLateAt_of_rowChk` proves `LargestSkipLateAt` at `1500`, `1501`
**and** `3000` by `decide +kernel` in a few seconds each.  What `R1 §8` adds is a
*route* that needs no candidate rank supplied — not extra reach.  Likewise, the
docstring's "no greedy word is inspected at either row" is presentational:
`remOf s` is defined through `SkipD3.gb s`, so two greedy words are computed.
-/

namespace ErdosProblems
namespace VerifyB4

open Erdos249257
open Erdos249257.BitR1

/-! ## 1. Axiom audit of every named result of `R1` -/

section Axioms

-- § plumbing
#print axioms BitR1.wbs_append
#print axioms BitR1.four_mul_wbs_le_lift
#print axioms BitR1.wbs_lift_le
#print axioms BitR1.gapDominates_of_append_left
#print axioms BitR1.liftedRow_length
#print axioms BitR1.preBits_length
#print axioms BitR1.seamWeights_succ_split
#print axioms BitR1.greedy_succ_split
#print axioms BitR1.top_weight
#print axioms BitR1.top_mem_iff

-- § the row law
#print axioms BitR1.remainder_step_of_top_mem
#print axioms BitR1.remainder_step_of_not_largestSkipLateAt
#print axioms BitR1.top_mem_of_not_largestSkipLateAt

-- § the #257 endpoint
#print axioms BitR1.not_half_mem_iff_exists_forcedRun

-- § the certificate
#print axioms BitR1.largestSkipLateAt_succ_of_ascent
#print axioms BitR1.largestSkipLateAt_succ_of_descent
#print axioms BitR1.largestSkipLateAt_succ_of_window_miss

-- § the sharp negative
#print axioms BitR1.stepLaw_of_forcedRun
#print axioms BitR1.stepLaw_pow_add_two
#print axioms BitR1.exists_stepLaw
#print axioms BitR1.forcedRun_defect_window

-- § iteration
#print axioms BitR1.stepLaw_iterate
#print axioms BitR1.remainder_le_of_forcedRun_of_growth
#print axioms BitR1.remainder_ge_of_no_late_window
#print axioms BitR1.remainder_ge_of_forcedRun
#print axioms BitR1.exists_largestSkipLateAt_of_remainder_small
#print axioms BitR1.remainder_band_of_forcedRun_of_growth

-- § kernel certificates
#print axioms BitR1.remOf_eq
#print axioms BitR1.largestSkipLateAt_succ_of_remOf_ascent
#print axioms BitR1.largestSkipLateAt_succ_of_remOf_descent
#print axioms BitR1.lateAt_8
#print axioms BitR1.lateAt_14
#print axioms BitR1.lateAt_15
#print axioms BitR1.lateAt_20
#print axioms BitR1.lateAt_26
#print axioms BitR1.lateAt_32
#print axioms BitR1.lateAt_38
#print axioms BitR1.lateAt_102
#print axioms BitR1.lateAt_401
#print axioms BitR1.lateAt_1500
#print axioms BitR1.lateAt_1501

-- § non-vacuity block
#print axioms BitR1.top_mem_eleven
#print axioms BitR1.remainder_step_eleven
#print axioms BitR1.not_largestSkipLateAt_twelve
#print axioms BitR1.remainder_step_eleven'
#print axioms BitR1.remainder_small_seven
#print axioms BitR1.exists_late_in_window_seven
#print axioms BitR1.defect_window_eleven

-- § the two upstream results the whole reduction rests on
#print axioms AngleD2.half_mem_iff_unboundedLargestSkipLate
#print axioms AngleD2.mem_of_late_of_not_largestSkipLateAt

end Axioms

/-! ## 2. Computable replicas, built out of the corpus's own definitions

`SkipD3.gb s` *is* `integerGreedyBits (seamWeights s) (seamSubsetTarget s)`
(`SkipD3.gb_eq`), and `BitR1.remOf s` *is* `seamIntegerGreedyRemainder s`
(`BitR1.remOf_eq`).  So nothing below is a proxy predicate: it is the corpus's
own greedy word, read at rank `d` exactly as `SkipD3.mem_support_iff` reads it.
-/

/-- Rank `d` is selected in row `s`: the corpus's own indexing. -/
def bitAt (s d : ℕ) : Bool := (SkipD3.gb s).getD (d - 2) false

/-- The largest false rank of row `s`, if any.  The largest `d < s` whose bit is
off automatically has every larger rank on, so this *is* `IsLargestFalseRank`. -/
def lfrOf (s : ℕ) : Option ℕ :=
  ((List.range (s - 2)).map (fun k => s - 1 - k)).find? (fun d => !bitAt s d)

/-- Decidable replica of `LargestSkipLateAt s`. -/
def lateB (s : ℕ) : Bool :=
  match lfrOf s with
  | none => false
  | some d => decide (2 * s < 3 * d)

/-- Hypothesis of `remainder_step_of_top_mem`: `s ∈ support (seamGreedyWord (s+1))`. -/
def topMemB (s : ℕ) : Bool := bitAt (s + 1) s

/-- The row-law correction `c s = 4 * R s - R (s+1) - 2 ^ (s+1)`, as an integer
so that an out-of-window value is visible rather than truncated. -/
def corr (s : ℕ) : Int :=
  4 * (remOf s : Int) - (remOf (s + 1) : Int) - (2 : Int) ^ (s + 1)

/-- Hypothesis of `largestSkipLateAt_succ_of_ascent`. -/
def ascB (s : ℕ) : Bool := decide (remOf (s + 1) + 2 ^ (s + 1) + 2 * s < 4 * remOf s)

/-- Hypothesis of `largestSkipLateAt_succ_of_descent`. -/
def descB (s : ℕ) : Bool := decide (4 * remOf s < remOf (s + 1) + 2 ^ (s + 1) + 4)

/-- Hypothesis of `exists_largestSkipLateAt_of_remainder_small`. -/
def smallB (s : ℕ) : Bool := decide (remOf s ≤ 2 ^ s + 1)

/-- Hypothesis of `remainder_ge_of_no_late_window` at `s`: the whole window
`[s+1, 2*s+2]` is non-late. -/
def noLateWindowB (s : ℕ) : Bool :=
  ((List.range (s + 2)).map (fun j => s + 1 + j)).all (fun t => !lateB t)

/-- The growth side condition of `remainder_le_of_forcedRun_of_growth`. -/
def growthB (s : ℕ) : Bool := decide (remOf s ≤ 2 ^ (s + 1))

/-- The band of `remainder_band_of_forcedRun_of_growth`. -/
def bandB (s : ℕ) : Bool :=
  decide (2 ^ s + 2 ≤ remOf s ∧ remOf s ≤ 2 ^ s + 2 * s + 1)

/-- Rows `[lo, lo+n)`. -/
def rows (lo n : ℕ) : List ℕ := (List.range n).map (fun k => lo + k)

/-! ## 3. Cross-check of the replicas against the corpus's published numbers -/

/-! `Corr2` records `seamIntegerGreedyRemainder 14 = 392`. -/
#eval remOf 14
/-! …and `seamIntegerGreedyRemainder 15 = 34333`. -/
#eval remOf 15

/-! `Corr3` records `d₀ 1148 = 1135`, `d₀ 1500 = 1499`, `d₀ 3000 = 2996`. -/
#eval (lfrOf 1148, lfrOf 1500, lfrOf 3000)

/-! ## 4. SATISFIABILITY of every hypothesis, on real rows -/

/-! **`LargestSkipLateAt` failure set over `[5, 501]`.**  Expected `[5,11,12,13]`
— i.e. `remainder_step_of_not_largestSkipLateAt`'s hypothesis `¬ Late (s+1)`
holds at exactly `s = 10, 11, 12`. -/
#eval (rows 5 497).filter (fun s => !lateB s)

/-! **Hypothesis of `remainder_step_of_top_mem`.**  How many of `[5,501]`? -/
#eval ((rows 5 497).filter topMemB).length
/-! …and the first twenty of them. -/
#eval ((rows 5 497).filter topMemB).take 20

/-! **The row-law correction at the rows where `top_mem` genuinely holds**, and
whether it lands in the window `[4, 2*s]` the theorem asserts.  Every entry must
be `true`, otherwise `remainder_step_of_top_mem` is false. -/
#eval ((rows 5 200).filter topMemB).map
        (fun s => (s, corr s, decide (4 ≤ corr s ∧ corr s ≤ 2 * (s : Int))))

/-! The same check, silently, over the full range: `true` means the row law is
consistent with the data at every one of its 258 satisfying rows. -/
#eval ((rows 5 497).filter topMemB).all
        (fun s => decide (4 ≤ corr s ∧ corr s ≤ 2 * (s : Int)))

/-! **The three rows where the `#257`-vocabulary hypothesis genuinely holds.**
`R1`'s docstring claims corrections `7, 8, 5`. -/
#eval ((rows 5 497).filter (fun s => !lateB (s + 1))).map (fun s => (s, corr s))

/-! **The certificate's fire rate** over `s ∈ [5, 501]`: ascent, descent, union. -/
#eval (((rows 5 497).filter ascB).length,
       ((rows 5 497).filter descB).length,
       ((rows 5 497).filter (fun s => ascB s || descB s)).length)

/-! **Soundness spot-check of the certificate**: every row it fires at must
actually be late.  Must be `true`. -/
#eval (rows 5 497).all (fun s => !(ascB s || descB s) || lateB (s + 1))

/-! **Hypothesis of `exists_largestSkipLateAt_of_remainder_small`**: count over
`[5, 501]`, then the first twenty rows. -/
#eval ((rows 5 497).filter smallB).length
#eval ((rows 5 497).filter smallB).take 20

/-! **Hypothesis of `remainder_ge_of_no_late_window`**: rows of `[5, 240]` at
which the *whole* window `[s+1, 2s+2]` is non-late.  Expected `[]` — the
theorem is empirically vacuous as a standalone implication. -/
#eval (rows 5 236).filter noLateWindowB

/-! The longest run of consecutive non-late rows in `[5, 501]`; the hypothesis
above needs a run of length `s + 2 ≥ 7`.  Expected `3` (rows `11, 12, 13`). -/
#eval (rows 5 497).foldl
        (fun (p : ℕ × ℕ) s => if lateB s then (0, p.2) else (p.1 + 1, max (p.1 + 1) p.2))
        (0, 0) |>.2

/-! **The growth side condition** `R m ≤ 2 ^ (m+1)`: its violations in `[5,501]`. -/
#eval (rows 5 497).filter (fun s => !growthB s)

/-! **The band** `[2^s+2, 2^s+2s+1]`: which rows of `[6, 501]` lie in it. -/
#eval (rows 6 496).filter bandB

/-! Why the band is almost always violated: it is violated exactly where the
defect dips below `2 ^ s + 2`, which is the same 232 rows as `smallB`. -/
#eval ((rows 6 496).filter (fun s => decide (remOf s < 2 ^ s + 2))).length

/-! ## 5. The certificate is a real computation, not a trivially true condition

At `s = 1498` the correction is `11`, inside `[4, 2996]`, so neither half of the
certificate fires — and indeed the kernel *refuses* both
`largestSkipLateAt_succ_of_remOf_ascent (s := 1498)` and
`..._descent (s := 1498)` (checked out of tree; putting them here would make this
file fail to compile, which is the point).  The correction itself: -/
#eval corr 1498
/-! …versus the two rows `R1` does certify. -/
#eval (corr 1499, corr 1500)
/-! …and the rows `R1` certifies really are late, independently. -/
#eval (lateB 1500, lateB 1501, lfrOf 1500, lfrOf 1501)

/-! ## 6. `remainder_ge_of_no_late_window`'s hypothesis, refuted at a concrete row

`R1`'s docstring says the localised forms "are witnessed above".  For
`remainder_ge_of_no_late_window` no witness is given, and none exists in the
measured range: its hypothesis needs `s + 2` consecutive non-late rows, and the
longest such run in `[5, 501]` has length `3`.  Here is an outright refutation at
`s = 5`, using `R1`'s own `lateAt_8`. -/

theorem noLateWindow_fails_at_five :
    ¬ (∀ t : ℕ, 5 ≤ t → t ≤ 11 → ¬ LargestSkipLateAt (t + 1)) := by
  intro h
  exact h 7 (by norm_num) (by norm_num) BitR1.lateAt_8

/-- The same at `s = 13`: the window `[14, 28]` contains the late row `14`. -/
theorem noLateWindow_fails_at_thirteen :
    ¬ (∀ t : ℕ, 13 ≤ t → t ≤ 27 → ¬ LargestSkipLateAt (t + 1)) := by
  intro h
  exact h 13 (by norm_num) (by norm_num) BitR1.lateAt_14

/-! ## 7. Reach: does `R1 §8` go past the pre-existing corpus machinery?

`SkipD3.largestSkipLateAt_of_rowChk` already decides `LargestSkipLateAt s` at an
arbitrary row from a single `decide +kernel`, given the largest false rank.  It
reaches rows `1500`, `1501` **and** `3000` (checked out of tree, all kernel-clean
in a few seconds).  So `R1 §8`'s rows are not beyond the corpus's reach; what is
new is the *route* — a scalar criterion that needs no candidate rank supplied.
Recorded here as the largest false ranks the corpus checker would be handed: -/
#eval (lfrOf 1499, lfrOf 1500, lfrOf 1501, lfrOf 3000)

/-! ## 8. Quantifier sanity on the `#257` endpoint

`UnboundedLargestSkipLate := ∀ N, ∃ s, N ≤ s ∧ LargestSkipLateAt s`; its negation
is `∃ N, ∀ s, N ≤ s → ¬ LargestSkipLateAt s`, which is `∃ N, ForcedRun N`.  The
statement below type-checks only if `R1`'s `not_half_mem_iff_exists_forcedRun`
has the orientation it claims. -/

example : (1 / 2 : ℝ) ∉ mersenneAchievementSet ↔
    ∃ N : ℕ, ∀ s : ℕ, N ≤ s → ¬ LargestSkipLateAt s :=
  BitR1.not_half_mem_iff_exists_forcedRun

/-- And the certificate really does land in `#257` vocabulary: eleven rows are
*finitely* many, so they contribute nothing to `UnboundedLargestSkipLate`.  This
is a restatement of what is *needed*, for contrast — it is deliberately left
unproved and unused. -/
example : (1 / 2 : ℝ) ∈ mersenneAchievementSet ↔
    ∀ N : ℕ, ∃ s : ℕ, N ≤ s ∧ LargestSkipLateAt s :=
  AngleD2.half_mem_iff_unboundedLargestSkipLate

end VerifyB4
end ErdosProblems
