/-
Copyright (c) 2026 Will Cook. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Will Cook
-/
import ErdosProblems.Skip.D2
import ErdosProblems.Skip.D3
import ErdosProblems.Bit.Corr2
import Erdos249257.HalfCylinderResetDeficitEscape

/-!
# Bit R2: the half-point counting law for bad rows

`AngleD2.half_mem_iff_unboundedLargestSkipLate` reduces the `1/2` question of
Erdős `#257` to: does `LargestSkipLateAt s` hold at cofinally many rows?  Call a
row **bad** when it fails.  The negative branch of `#257` is exactly an infinite
tail of bad rows.

This file counts.  It does not track the entering remainder bit by bit
(`Bit/Corr1`–`Corr3` do that); instead it asks how *many* values of the one
deterministic quantity

    `rem s = seamIntegerGreedyRemainder s`

are compatible with a bad run of length `k`, and finds that the answer shrinks
geometrically — so that a bad run pins `rem` into a window whose width is
`O(s)` inside a range of size `2 ^ s`.

## The mechanism

A bad row is *not* a neutral event for the branch structure.  If the row-`s`
step took an upper or middle branch, then `seamGreedyWord_succ_isLargest`
`FalseRank_terminal_of_upperOrMiddle` makes the brand-new rank `s` the largest
false rank of row `s + 1`, and `2 * (s + 1) < 3 * s` for `s ≥ 3`, so row `s + 1`
is **good**.  Contrapositive (`not_upperOrMiddle_of_not_largestSkipLateAt_succ`):

    row `s + 1` bad  ⟹  the row-`s` step is a right branch.

On a right branch `HalfCylinderResetDeficitEscape.rightBranch_remainder_succ_eq`
gives the exact recurrence

    `rem (s+1) + 2 ^ (s+1) + pulse s + 4 = 4 * rem s`,   `pulse s ≤ 2 * (s - 2)`.

Measuring `rem s` against the **half point** `2 ^ s` turns this into a pair of
one-line expanding maps.  With `D s = 2 ^ s - rem s` (deficit) and
`σ s = rem s - 2 ^ s` (surplus):

    `D (s+1) = 4 * D s + pulse s + 4`      (`deficit_step`)
    `σ (s+1) = 4 * σ s - pulse s - 4`      (`surplus_step`)

The half point `2 ^ s` is the *repelling fixed point* of the row map.  A bad run
is therefore a run of right branches, and along it any displacement from the
half point is amplified — by `4` downward, by at least `3` upward once the
surplus clears the pulse budget `2 * s`.

## Main results

* `deficit_iter`, `deficit_shrinks_along_rightRun` — **the counting law.**  A
  run of `k` right branches confines the base deficit to
  `4 ^ k * D N + 4 ^ k ≤ 2 ^ (N + k) + 1`: the admissible set of deficits at the
  base of the run shrinks by a factor `4` per row, i.e. `D N ≲ 2 ^ (N - k)`.
* `exists_largestSkipLateAt_of_remainder_le_two_pow` — **Theorem A,
  unconditional.**  If `rem N ≤ 2 ^ N` for some `N ≥ 5`, then some row of
  `[N + 1, 2 * N + 1]` is good.  A bad run based at a sub-half-point row has
  length at most `N`.  Note the deficit map has the additive `+ 4`, so this
  needs no lower bound on `D N` at all: even `rem N = 2 ^ N` exactly is killed.
* `half_mem_of_remainderReachesHalfPointCofinally` — **the payoff, and it is
  unconditional:** `1/2 ∈ mersenneAchievementSet` follows from the single
  inequality `rem s ≤ 2 ^ s` holding at arbitrarily large `s`.  No bit
  correspondence, no side condition, no unproved numeric coincidence.
* `three_mul_remainder_lt_of_largestSkipLateAt` — **the ceiling.**  Every *good*
  row obeys `3 * rem s < 7 * 2 ^ s + 4`, i.e. `rem s < (7/3) * 2 ^ s`.  This is
  `three_mul_remainder_lt_exactLateGap` with the late margin `2 * s < 3 * d`
  used to collapse the correction `4 ^ (s - d)` below `2 ^ (s - 1)`.
* `surplus_iter`, `not_surplus_run`, `exists_largestSkipLateAt_of_surplus` —
  **Theorem B.**  A surplus `σ N ≥ 2 * N` triples per bad row, so after
  `2 * N + 2` bad rows the remainder has passed every value a good row can
  carry.  Hence a surplus row also produces a good row in `[N + 1, 3 * N + 2]`,
  *provided* the top row of that window still obeys the ceiling.
* `badRun_pins_remainder` — **the pin.**  If every row of `[N + 1, 3 * N + 2]`
  is bad and the top row obeys the ceiling, then

      `2 ^ N < rem N < 2 ^ N + 2 * N`.

  The base remainder is trapped in a window of width `2 * N` — relative width
  `O(N * 2 ^ (-N))`.  That is the counting/density conclusion, in exact form:
  it is not a measure heuristic but a two-sided expansion argument.
* `half_mem_of_remainderMissesHalfPointWindowCofinally` — consequently `1/2` is
  achieved as soon as `rem s` misses that width-`2 * s` window cofinally often
  (with the ceiling holding at the companion row `3 * s + 2`).

## What this does not close, and exactly why

The deficit half is unconditional.  The surplus half is not: it needs *some*
upper bound on `rem` at the **top** row of the run, and the only bound the
corpus proves unconditionally at an arbitrary row is `rem t ≤ seamSubsetTarget
t ≈ 4 ^ t / 2` — which scales exactly like the `4 ^ k` amplification and
therefore yields nothing.  The ceiling `3 * rem t < 7 * 2 ^ t + 4` is exactly
strong enough, and `three_mul_remainder_lt_of_largestSkipLateAt` proves it at
every good row; the missing input is a version valid at a bad row.  Chasing it
through `isLargestFalseRank_iff_exists_lowerPrefix_fullSuffix` shows what is
needed: for a largest false rank `d`, the exact adjacent gap is
`2 ^ (s+1) + Θ(4 ^ (s-d))`, which stays `O(2 ^ s)` precisely when `d ≥ s / 2`.
So the surplus half is unconditional as soon as the greedy take-run at a bad
row is at most half the row — a strictly weaker demand than the `s / 3` run
bound `Bit/Corr3` identifies as the live target of `#257` itself.

An arbitrary-precision replication of `seamWeights`, `seamSubsetTarget` and
`integerGreedyBits` finds the ceiling `3 * rem s < 7 * 2 ^ s + 4` satisfied at
**every** row of `[5, 299]` (worst ratio `0.856`, at `s = 43`), and finds the
half-point window `(2 ^ s, 2 ^ s + 2 * s)` occupied at exactly one row of that
range, `s = 8` (`rem 8 = 265`, window `(256, 272)`).  The bad rows of `[5, 3000]`
are exactly `5, 11, 12, 13`, reproducing `Bit/Corr3`.

## Non-vacuity

Certified in the kernel, in this file, for every hypothesis used:

* **bad rows exist**: `not_largestSkipLateAt_eleven / _twelve / _thirteen`, by
  `decide +kernel` on the decidable certificate `noLateSkip`;
* **right branches exist**: `not_upperOrMiddle_six`, `not_upperOrMiddle_nine`,
  each a single bit of the successor row;
* **`deficit_step` / `deficit_iter` / `deficit_shrinks_along_rightRun`**:
  witnessed at `N = 6`, where `rem 6 = 34` sits `30` below `2 ^ 6` and the step
  is a right branch (`deficit_step_witness`, `deficit_iter_witness`,
  `deficit_shrinks_witness`);
* **`surplus_step`**: witnessed at `s = 9` (`rem 9 = 541 = 2 ^ 9 + 29`,
  `29 ≥ 2 * 9`, right branch);
* **`surplus_iter` at `k = 3`**: witnessed at `N = 10` over the genuine
  three-row bad block `11, 12, 13` (`surplus_iter_witness`).  The theorem
  predicts `rem 13 ≥ 2 ^ 13 + 27 * 111 = 11189`; the true value is `15147`;
* **the ceiling**: `obeysRemainderCeiling_fourteen` (from the good row `14`),
  `obeysRemainderCeiling_seventeen` (direct);
* **Theorem A**: `theoremA_witness` — hypotheses hold at `N = 14`
  (`rem 14 = 392 ≤ 2 ^ 14`), conclusion produced: a good row in `[15, 29]`;
* **Theorem B**: `theoremB_witness` — hypotheses hold at `N = 5`
  (`rem 5 = 71 = 2 ^ 5 + 39`, `39 ≥ 10`, ceiling at row `17`), conclusion
  produced: a good row in `[6, 17]`.

The one statement whose hypotheses are **not** exhibited is
`badRun_pins_remainder`.  It requires at least `2 * N + 2 ≥ 12` consecutive bad
rows.  The exhaustive computation on `[5,3000]` finds bad rows only at
`5, 11, 12, 13`, so its longest consecutive bad run has length `3`; the
headline theorem applies to no row in that audited range and supplies no
observed instance.  Its two contrapositive halves —
`exists_largestSkipLateAt_of_remainder_le_two_pow` and
`exists_largestSkipLateAt_of_surplus` — are separately exhibited above and
are the non-vacuous content used later.

No `sorry`, no `native_decide`, no new axiom; `decide +kernel` only.  Every
theorem depends on `[propext, Classical.choice, Quot.sound]`.
-/

namespace ErdosProblems.BitR2

open Erdos249257
open Erdos249257.HalfCylinderIntegerGreedy

noncomputable section

noncomputable local instance
    {α : Type*} {F : PerturbedFamily α} {C : ℕ}
    (K : F.AdjacentCut C) : Decidable K.successorCarries :=
  Classical.propDecidable _

/-! ## 1. A bad row forces the previous step onto the right branch -/

/-- An upper-or-middle branch at `s` makes rank `s` a *late* largest false rank
of row `s + 1`, so row `s + 1` is good. -/
theorem largestSkipLateAt_succ_of_upperOrMiddle
    {s : ℕ} (hs : 5 ≤ s) (hUM : SeamGreedyUpperOrMiddleAt s hs) :
    LargestSkipLateAt (s + 1) :=
  ⟨s, seamGreedyWord_succ_isLargestFalseRank_terminal_of_upperOrMiddle s hs hUM,
    by omega⟩

/-- **The link.**  A bad row `s + 1` forces the row-`s` step to be a right
branch. -/
theorem not_upperOrMiddle_of_not_largestSkipLateAt_succ
    {s : ℕ} (hs : 5 ≤ s) (hbad : ¬ LargestSkipLateAt (s + 1)) :
    ¬ SeamGreedyUpperOrMiddleAt s hs :=
  fun hUM => hbad (largestSkipLateAt_succ_of_upperOrMiddle hs hUM)

/-! ## 2. A decidable certificate for badness -/

/-- `noLateSkip s`: every rank of the late zone of row `s` is selected by the
concrete greedy.  A `true` value certifies `¬ LargestSkipLateAt s`. -/
def noLateSkip (s : ℕ) : Bool :=
  (List.range s).all fun d =>
    decide (d < 2) || decide (3 * d ≤ 2 * s) || (SkipD3.gb s).getD (d - 2) false

theorem not_largestSkipLateAt_of_noLateSkip {s : ℕ} (h : noLateSkip s = true) :
    ¬ LargestSkipLateAt s := by
  rintro ⟨d, ⟨hd2, hds, hdnot, -⟩, hlate⟩
  rw [noLateSkip, List.all_eq_true] at h
  have hd := h d (List.mem_range.mpr hds)
  rw [Bool.or_eq_true, Bool.or_eq_true, decide_eq_true_eq, decide_eq_true_eq] at hd
  rcases hd with (h1 | h2) | h3
  · omega
  · omega
  · exact hdnot ((SkipD3.mem_support_iff hd2 hds).mpr h3)

/-! ### The four bad rows of `[5, 3000]`, certified

The measurement reported in `Bit/Corr3.lean` finds `¬ LargestSkipLateAt s`
at exactly `s = 5, 11, 12, 13` in the range `[5, 3000]`.  The three usable
ones (`s ≥ 6`, so that the bit reading of `Corr1` is not degenerate) are
certified here; they are the witnesses that make every "bad row" hypothesis
below non-vacuous. -/

theorem not_largestSkipLateAt_eleven : ¬ LargestSkipLateAt 11 :=
  not_largestSkipLateAt_of_noLateSkip (by decide +kernel)

theorem not_largestSkipLateAt_twelve : ¬ LargestSkipLateAt 12 :=
  not_largestSkipLateAt_of_noLateSkip (by decide +kernel)

theorem not_largestSkipLateAt_thirteen : ¬ LargestSkipLateAt 13 :=
  not_largestSkipLateAt_of_noLateSkip (by decide +kernel)

/-! ## 3. The deficit recurrence: below the half point, bad runs die -/

/-- **Deficit step.**  On a right branch the distance of the greedy remainder
*below* the half point `2 ^ s` is more than quadrupled. -/
theorem deficit_step {s D : ℕ} (hs : 5 ≤ s)
    (hR : ¬ SeamGreedyUpperOrMiddleAt s hs)
    (hD : seamIntegerGreedyRemainder s + D = 2 ^ s) :
    ∃ D' : ℕ, seamIntegerGreedyRemainder (s + 1) + D' = 2 ^ (s + 1) ∧
      4 * D + 4 ≤ D' := by
  have hrec := rightBranch_remainder_succ_eq hs hR
  have hp2 : (2 : ℕ) ^ (s + 1) = 2 * 2 ^ s := by rw [pow_succ]; ring
  exact ⟨4 * D + (seamAdjacentCut s hs).belowPulse + 4, by omega, by omega⟩

/-- **Deficit iteration.**  Along a run of right branches the deficit grows at
least like `4 ^ k`, with an extra additive `4 ^ k`. -/
theorem deficit_iter {N : ℕ} (hN : 5 ≤ N) {D : ℕ}
    (hD : seamIntegerGreedyRemainder N + D = 2 ^ N) :
    ∀ k : ℕ,
      (∀ j : ℕ, j < k → ¬ SeamGreedyUpperOrMiddleAt (N + j) (by omega)) →
      ∃ D' : ℕ, seamIntegerGreedyRemainder (N + k) + D' = 2 ^ (N + k) ∧
        4 ^ k * D + 4 ^ k ≤ D' + 1 := by
  intro k
  induction k with
  | zero => intro _; exact ⟨D, by simpa using hD, by simp⟩
  | succ k ih =>
      intro hblock
      obtain ⟨Dk, hDk, hgrow⟩ := ih fun j hj => hblock j (by omega)
      obtain ⟨D', hD', hstep⟩ :=
        deficit_step (s := N + k) (by omega) (hblock k (by omega)) hDk
      refine ⟨D', ?_, ?_⟩
      · rw [show N + (k + 1) = N + k + 1 by omega]; exact hD'
      · have h4 : (4 : ℕ) ^ (k + 1) = 4 * 4 ^ k := by rw [pow_succ]; ring
        nlinarith [hgrow, hstep]

/-- **Theorem A (unconditional).**  If the concrete seam greedy remainder of a
row `N ≥ 5` has not risen above the half point `2 ^ N`, then a *late* largest
false rank occurs at some row of the window `[N + 1, 2 * N + 1]`.

Equivalently: a run of bad rows starting at `N + 1` has length at most `N`
whenever `seamIntegerGreedyRemainder N ≤ 2 ^ N`. -/
theorem exists_largestSkipLateAt_of_remainder_le_two_pow
    {N : ℕ} (hN : 5 ≤ N) (hrem : seamIntegerGreedyRemainder N ≤ 2 ^ N) :
    ∃ t : ℕ, N + 1 ≤ t ∧ t ≤ 2 * N + 1 ∧ LargestSkipLateAt t := by
  by_contra hcon
  have hbadAll : ∀ t : ℕ, N + 1 ≤ t → t ≤ 2 * N + 1 → ¬ LargestSkipLateAt t :=
    fun t h1 h2 hl => hcon ⟨t, h1, h2, hl⟩
  have hblock : ∀ j : ℕ, j < N + 1 →
      ¬ SeamGreedyUpperOrMiddleAt (N + j) (by omega) := by
    intro j hj
    exact not_upperOrMiddle_of_not_largestSkipLateAt_succ (by omega)
      (hbadAll (N + j + 1) (by omega) (by omega))
  obtain ⟨D', hD', hgrow⟩ :=
    deficit_iter hN (D := 2 ^ N - seamIntegerGreedyRemainder N) (by omega)
      (N + 1) hblock
  have hpow : (4 : ℕ) ^ (N + 1) = 2 * 2 ^ (N + (N + 1)) := by
    have h1 : (4 : ℕ) ^ (N + 1) = 2 ^ (2 * (N + 1)) := by
      rw [show (4 : ℕ) = 2 ^ 2 by norm_num, ← pow_mul, Nat.mul_comm]
    rw [h1, show 2 * (N + 1) = (N + (N + 1)) + 1 by omega, pow_succ]
    ring
  have hbig : (2 : ℕ) ≤ 2 ^ (N + (N + 1)) := Nat.one_lt_two_pow (by omega)
  have hle : (4 : ℕ) ^ (N + 1) ≤ D' + 1 := by nlinarith [hgrow]
  omega

/-- **The counting law, explicitly.**  Along a run of `k` right branches the
*set of admissible base deficits* shrinks by a factor `4` per row: the deficit
`2 ^ N - rem(N)` is confined to `[0, 2 ^ (N - k)]` up to the additive `4 ^ k`
that the `+ 4` in the recurrence contributes.  For `k > N` the confinement is
empty, which is `exists_largestSkipLateAt_of_remainder_le_two_pow`. -/
theorem deficit_shrinks_along_rightRun {N k : ℕ} (hN : 5 ≤ N)
    (hle : seamIntegerGreedyRemainder N ≤ 2 ^ N)
    (hblock : ∀ j : ℕ, j < k → ¬ SeamGreedyUpperOrMiddleAt (N + j) (by omega)) :
    4 ^ k * (2 ^ N - seamIntegerGreedyRemainder N) + 4 ^ k ≤ 2 ^ (N + k) + 1 := by
  obtain ⟨D', hD', hgrow⟩ :=
    deficit_iter hN (D := 2 ^ N - seamIntegerGreedyRemainder N) (by omega) k hblock
  omega

/-! ## 4. A new unconditional sufficient condition for `1/2` -/

/-- The concrete seam greedy remainder returns to or below the half point
`2 ^ s` at arbitrarily large rows. -/
def RemainderReachesHalfPointCofinally : Prop :=
  ∀ N : ℕ, ∃ s : ℕ, N ≤ s ∧ 5 ≤ s ∧ seamIntegerGreedyRemainder s ≤ 2 ^ s

/-- **`1/2 ∈ mersenneAchievementSet` follows from one inequality, infinitely
often.**  No side condition, no unproved bit correspondence: it is enough that
the deterministic remainder `seamIntegerGreedyRemainder s` fails to exceed
`2 ^ s` at arbitrarily large `s`. -/
theorem half_mem_of_remainderReachesHalfPointCofinally
    (h : RemainderReachesHalfPointCofinally) :
    (1 / 2 : ℝ) ∈ mersenneAchievementSet := by
  rw [AngleD2.half_mem_iff_unboundedLargestSkipLate]
  intro N
  obtain ⟨s, hNs, hs5, hrem⟩ := h N
  obtain ⟨t, h1, _h2, hlate⟩ :=
    exists_largestSkipLateAt_of_remainder_le_two_pow hs5 hrem
  exact ⟨t, by omega, hlate⟩

/-! ## 5. The surplus recurrence: above the half point, bad runs explode -/

/-- **Surplus step.**  On a right branch a surplus of at least `2 * s` above the
half point at least triples. -/
theorem surplus_step {s σ : ℕ} (hs : 5 ≤ s)
    (hR : ¬ SeamGreedyUpperOrMiddleAt s hs)
    (hσ : seamIntegerGreedyRemainder s = 2 ^ s + σ) (hbig : 2 * s ≤ σ) :
    ∃ σ' : ℕ, seamIntegerGreedyRemainder (s + 1) = 2 ^ (s + 1) + σ' ∧
      3 * σ ≤ σ' ∧ 2 * (s + 1) ≤ σ' := by
  have hrec := rightBranch_remainder_succ_eq hs hR
  have hp2 : (2 : ℕ) ^ (s + 1) = 2 * 2 ^ s := by rw [pow_succ]; ring
  have hpulse := seamAdjacentCut_belowPulse_le hs
  exact ⟨4 * σ - ((seamAdjacentCut s hs).belowPulse + 4), by omega, by omega,
    by omega⟩

/-- **Surplus iteration.**  Along a run of right branches a surplus above the
half point grows at least like `3 ^ k`. -/
theorem surplus_iter {N : ℕ} (hN : 5 ≤ N) {σ : ℕ}
    (hσ : seamIntegerGreedyRemainder N = 2 ^ N + σ) (hbig : 2 * N ≤ σ) :
    ∀ k : ℕ,
      (∀ j : ℕ, j < k → ¬ SeamGreedyUpperOrMiddleAt (N + j) (by omega)) →
      ∃ σ' : ℕ, seamIntegerGreedyRemainder (N + k) = 2 ^ (N + k) + σ' ∧
        3 ^ k * σ ≤ σ' ∧ 2 * (N + k) ≤ σ' := by
  intro k
  induction k with
  | zero => intro _; exact ⟨σ, by simpa using hσ, by simp, by simpa using hbig⟩
  | succ k ih =>
      intro hblock
      obtain ⟨σk, hσk, hgrow, hbk⟩ := ih fun j hj => hblock j (by omega)
      obtain ⟨σ', hσ', hstep, hb'⟩ :=
        surplus_step (s := N + k) (by omega) (hblock k (by omega)) hσk hbk
      refine ⟨σ', ?_, ?_, ?_⟩
      · rw [show N + (k + 1) = N + k + 1 by omega]; exact hσ'
      · have h3 : (3 : ℕ) ^ (k + 1) = 3 * 3 ^ k := by rw [pow_succ]; ring
        nlinarith [hgrow, hstep]
      · rw [show N + (k + 1) = N + k + 1 by omega]; exact hb'

/-! ## 6. The ceiling that every good row obeys -/

/-- The remainder ceiling `3 * rem(s) < 7 * 2 ^ s + 4`, i.e. `rem(s)` below
`(7/3) * 2 ^ s`.  Every *good* row obeys it automatically
(`three_mul_remainder_lt_of_largestSkipLateAt`), and an arbitrary-precision
replication finds it satisfied at every row of `[5, 299]`, with the worst ratio
`0.856` at `s = 43`. -/
def ObeysRemainderCeiling (s : ℕ) : Prop :=
  3 * seamIntegerGreedyRemainder s < 7 * 2 ^ s + 4

/-- **Good rows obey the ceiling, unconditionally.**  This is the exact
adjacent-gap strip invariant `three_mul_remainder_lt_exactLateGap` with the
late-zone margin `2 * s < 3 * d` used to collapse the correction `4 ^ (s - d)`
into `2 ^ (s - 1)`. -/
theorem three_mul_remainder_lt_of_largestSkipLateAt
    {s : ℕ} (hs : 5 ≤ s) (hgood : LargestSkipLateAt s) :
    ObeysRemainderCeiling s := by
  obtain ⟨d, hd, hlate⟩ := hgood
  have hds : d < s := hd.2.1
  have hstrip := three_mul_remainder_lt_exactLateGap hs hd hlate
  have hfour : (4 : ℕ) ^ (s - d) = 2 ^ (2 * (s - d)) := by
    rw [show (4 : ℕ) = 2 ^ 2 by norm_num, ← pow_mul, Nat.mul_comm]
  have hmono : (2 : ℕ) ^ (2 * (s - d)) ≤ 2 ^ (s - 1) :=
    Nat.pow_le_pow_right (by norm_num) (by omega)
  have hhalf : (2 : ℕ) ^ s = 2 * 2 ^ (s - 1) := by
    conv_lhs => rw [show s = (s - 1) + 1 by omega]
    rw [pow_succ]; ring
  have hsucc : (2 : ℕ) ^ (s + 1) = 2 * 2 ^ s := by rw [pow_succ]; ring
  unfold ObeysRemainderCeiling
  omega

/-! ## 7. Theorem B: above the half point a long bad run breaks the ceiling -/

/-- **Theorem B.**  A surplus of at least `2 * N` above the half point at row
`N`, followed by `2 * N + 2` right branches, is impossible if the top row of
the run still obeys the remainder ceiling: the tripling drives the remainder
past every value a good row can carry. -/
theorem not_surplus_run {N σ : ℕ} (hN : 5 ≤ N)
    (hσ : seamIntegerGreedyRemainder N = 2 ^ N + σ) (hbig : 2 * N ≤ σ)
    (hblock : ∀ j : ℕ, j < 2 * N + 2 →
      ¬ SeamGreedyUpperOrMiddleAt (N + j) (by omega))
    (hceil : ObeysRemainderCeiling (3 * N + 2)) : False := by
  obtain ⟨σ', hσ', hgrow, _⟩ := surplus_iter hN hσ hbig (2 * N + 2) hblock
  rw [show N + (2 * N + 2) = 3 * N + 2 by omega] at hσ'
  have h9 : (3 : ℕ) ^ (2 * N + 2) = 9 * 9 ^ N := by
    rw [show 2 * N + 2 = 2 * (N + 1) by omega, pow_mul, pow_succ]
    norm_num
    ring
  have h8 : (8 : ℕ) ^ N ≤ 9 ^ N := Nat.pow_le_pow_left (by norm_num) N
  have h8pos : 1 ≤ (8 : ℕ) ^ N := Nat.one_le_pow _ _ (by norm_num)
  have h2 : (2 : ℕ) ^ (3 * N + 2) = 4 * 8 ^ N := by
    rw [show 3 * N + 2 = 2 + 3 * N by omega, pow_add, pow_mul]
    norm_num
  have hσ10 : 10 ≤ σ := by omega
  have hchain : (90 : ℕ) * 8 ^ N ≤ σ' := by
    calc (90 : ℕ) * 8 ^ N ≤ 90 * 9 ^ N := Nat.mul_le_mul_left _ h8
      _ = (9 * 9 ^ N) * 10 := by ring
      _ ≤ (9 * 9 ^ N) * σ := Nat.mul_le_mul_left _ hσ10
      _ = 3 ^ (2 * N + 2) * σ := by rw [h9]
      _ ≤ σ' := hgrow
  unfold ObeysRemainderCeiling at hceil
  omega

/-- **Theorem B, positive form.**  A row `N` carrying a surplus of at least
`2 * N` above the half point *produces* a late largest false rank inside
`[N + 1, 3 * N + 2]`, provided the top row of that window still obeys the
remainder ceiling. -/
theorem exists_largestSkipLateAt_of_surplus {N σ : ℕ} (hN : 5 ≤ N)
    (hσ : seamIntegerGreedyRemainder N = 2 ^ N + σ) (hbig : 2 * N ≤ σ)
    (hceil : ObeysRemainderCeiling (3 * N + 2)) :
    ∃ t : ℕ, N + 1 ≤ t ∧ t ≤ 3 * N + 2 ∧ LargestSkipLateAt t := by
  by_contra hcon
  have hbadAll : ∀ t : ℕ, N + 1 ≤ t → t ≤ 3 * N + 2 → ¬ LargestSkipLateAt t :=
    fun t h1 h2 hl => hcon ⟨t, h1, h2, hl⟩
  refine not_surplus_run hN hσ hbig (fun j hj => ?_) hceil
  exact not_upperOrMiddle_of_not_largestSkipLateAt_succ (by omega)
    (hbadAll (N + j + 1) (by omega) (by omega))

/-! ## 8. The two halves together: a long bad run pins the remainder -/

/-- **The pin.**  Suppose every row of `[N + 1, 3 * N + 2]` is bad and the top
row `3 * N + 2` of that block still obeys the remainder ceiling that every good
row obeys.  Then the remainder at the base row `N` is trapped in the window
`(2 ^ N, 2 ^ N + 2 * N)` — an interval of width `2 * N` inside a range of size
`2 ^ N`.

The two clauses come from opposite sides: below the half point the deficit
quadruples per bad row (`deficit_iter`), above it the surplus triples
(`surplus_iter`).  Only a window of relative width `O(N * 2 ^ (-N))` around the
half point `2 ^ N` survives both. -/
theorem badRun_pins_remainder {N : ℕ} (hN : 5 ≤ N)
    (hbad : ∀ t : ℕ, N + 1 ≤ t → t ≤ 3 * N + 2 → ¬ LargestSkipLateAt t)
    (hceil : ObeysRemainderCeiling (3 * N + 2)) :
    2 ^ N < seamIntegerGreedyRemainder N ∧
      seamIntegerGreedyRemainder N < 2 ^ N + 2 * N := by
  have hblock : ∀ j : ℕ, j < 2 * N + 2 →
      ¬ SeamGreedyUpperOrMiddleAt (N + j) (by omega) := by
    intro j hj
    exact not_upperOrMiddle_of_not_largestSkipLateAt_succ (by omega)
      (hbad (N + j + 1) (by omega) (by omega))
  constructor
  · by_contra hlow
    obtain ⟨t, h1, h2, hlate⟩ :=
      exists_largestSkipLateAt_of_remainder_le_two_pow hN (by omega)
    exact hbad t h1 (by omega) hlate
  · by_contra hhigh
    have hsplit : seamIntegerGreedyRemainder N =
        2 ^ N + (seamIntegerGreedyRemainder N - 2 ^ N) := by omega
    exact not_surplus_run hN hsplit (by omega) hblock hceil

/-! ## 9. The `#257` endpoint, from a window-avoidance condition -/

/-- Cofinally many rows `s` whose remainder avoids the width-`2 * s` window just
above the half point `2 ^ s`, and whose companion row `3 * s + 2` obeys the
remainder ceiling. -/
def RemainderMissesHalfPointWindowCofinally : Prop :=
  ∀ N : ℕ, ∃ s : ℕ, N ≤ s ∧ 5 ≤ s ∧ ObeysRemainderCeiling (3 * s + 2) ∧
    ¬ (2 ^ s < seamIntegerGreedyRemainder s ∧
        seamIntegerGreedyRemainder s < 2 ^ s + 2 * s)

/-- **The endpoint.**  `1/2 ∈ mersenneAchievementSet` as soon as the
deterministic seam greedy remainder misses the width-`2 * s` half-point window
at arbitrarily large `s`. -/
theorem half_mem_of_remainderMissesHalfPointWindowCofinally
    (h : RemainderMissesHalfPointWindowCofinally) :
    (1 / 2 : ℝ) ∈ mersenneAchievementSet := by
  rw [AngleD2.half_mem_iff_unboundedLargestSkipLate]
  intro N
  obtain ⟨s, hNs, hs5, hceil, hmiss⟩ := h N
  by_contra hcon
  refine hmiss (badRun_pins_remainder hs5 (fun t h1 h2 hl => hcon ⟨t, ?_, hl⟩) hceil)
  omega

/-! ## 7. Hypothesis status

The local right-branch hypotheses of `deficit_step`, `deficit_iter`,
`surplus_step`, and `surplus_iter` are realised by kernel-checked rows.
Individual bad rows also occur at `5, 11, 12, 13`.  This does **not** instantiate
`badRun_pins_remainder`, whose antecedent requires at least twelve consecutive
bad rows in its smallest relevant case; the measured maximum run has length
three.  That theorem remains a valid conditional implication with no observed
instance. -/

section Witnesses

/-! ### Explicit rows -/

private theorem seamWeights_six : seamWeights 6 = [1365, 585, 273, 132] := by
  unfold seamWeights
  rw [seamWeightsFrom_eq_cons (by norm_num : 2 < 6),
    seamWeightsFrom_eq_cons (by norm_num : 3 < 6),
    seamWeightsFrom_eq_cons (by norm_num : 4 < 6),
    seamWeightsFrom_eq_cons (by norm_num : 5 < 6),
    seamWeightsFrom_eq_nil (by norm_num : 6 ≤ 6)]
  norm_num [truncatedMersenneWeight]

theorem remainder_six : seamIntegerGreedyRemainder 6 = 34 := by
  unfold seamIntegerGreedyRemainder integerGreedyRemainder
  rw [seamWeights_six, show seamSubsetTarget 6 = 1984 by norm_num [seamSubsetTarget]]
  norm_num [integerGreedyBits, weightedBoolSum]

private theorem seamWeights_nine :
    seamWeights 9 = [87381, 37449, 17476, 8456, 4161, 2064, 1028] := by
  unfold seamWeights
  rw [seamWeightsFrom_eq_cons (by norm_num : 2 < 9),
    seamWeightsFrom_eq_cons (by norm_num : 3 < 9),
    seamWeightsFrom_eq_cons (by norm_num : 4 < 9),
    seamWeightsFrom_eq_cons (by norm_num : 5 < 9),
    seamWeightsFrom_eq_cons (by norm_num : 6 < 9),
    seamWeightsFrom_eq_cons (by norm_num : 7 < 9),
    seamWeightsFrom_eq_cons (by norm_num : 8 < 9),
    seamWeightsFrom_eq_nil (by norm_num : 9 ≤ 9)]
  norm_num [truncatedMersenneWeight]

theorem remainder_nine : seamIntegerGreedyRemainder 9 = 541 := by
  unfold seamIntegerGreedyRemainder integerGreedyRemainder
  rw [seamWeights_nine,
    show seamSubsetTarget 9 = 130560 by norm_num [seamSubsetTarget]]
  norm_num [integerGreedyBits, weightedBoolSum]

private theorem seamWeights_ten :
    seamWeights 10 = [349525, 149796, 69905, 33825, 16644, 8256, 4112, 2052] := by
  unfold seamWeights
  rw [seamWeightsFrom_eq_cons (by norm_num : 2 < 10),
    seamWeightsFrom_eq_cons (by norm_num : 3 < 10),
    seamWeightsFrom_eq_cons (by norm_num : 4 < 10),
    seamWeightsFrom_eq_cons (by norm_num : 5 < 10),
    seamWeightsFrom_eq_cons (by norm_num : 6 < 10),
    seamWeightsFrom_eq_cons (by norm_num : 7 < 10),
    seamWeightsFrom_eq_cons (by norm_num : 8 < 10),
    seamWeightsFrom_eq_cons (by norm_num : 9 < 10),
    seamWeightsFrom_eq_nil (by norm_num : 10 ≤ 10)]
  norm_num [truncatedMersenneWeight]

theorem remainder_ten : seamIntegerGreedyRemainder 10 = 1135 := by
  unfold seamIntegerGreedyRemainder integerGreedyRemainder
  rw [seamWeights_ten,
    show seamSubsetTarget 10 = 523264 by norm_num [seamSubsetTarget]]
  norm_num [integerGreedyBits, weightedBoolSum]

private theorem seamWeights_five : seamWeights 5 = [341, 146, 68] := by
  unfold seamWeights
  rw [seamWeightsFrom_eq_cons (by norm_num : 2 < 5),
    seamWeightsFrom_eq_cons (by norm_num : 3 < 5),
    seamWeightsFrom_eq_cons (by norm_num : 4 < 5),
    seamWeightsFrom_eq_nil (by norm_num : 5 ≤ 5)]
  norm_num [truncatedMersenneWeight]

theorem remainder_five : seamIntegerGreedyRemainder 5 = 71 := by
  unfold seamIntegerGreedyRemainder integerGreedyRemainder
  rw [seamWeights_five, show seamSubsetTarget 5 = 480 by norm_num [seamSubsetTarget]]
  norm_num [integerGreedyBits, weightedBoolSum]

private theorem seamWeights_seventeen :
    seamWeights 17 =
      [5726623061, 2454267026, 1145324612, 554189328, 272696336, 135274560,
        67372036, 33620096, 16793616, 8392706, 4195328, 2097408, 1048640,
        524304, 262148] := by
  unfold seamWeights
  rw [seamWeightsFrom_eq_cons (by norm_num : 2 < 17),
    seamWeightsFrom_eq_cons (by norm_num : 3 < 17),
    seamWeightsFrom_eq_cons (by norm_num : 4 < 17),
    seamWeightsFrom_eq_cons (by norm_num : 5 < 17),
    seamWeightsFrom_eq_cons (by norm_num : 6 < 17),
    seamWeightsFrom_eq_cons (by norm_num : 7 < 17),
    seamWeightsFrom_eq_cons (by norm_num : 8 < 17),
    seamWeightsFrom_eq_cons (by norm_num : 9 < 17),
    seamWeightsFrom_eq_cons (by norm_num : 10 < 17),
    seamWeightsFrom_eq_cons (by norm_num : 11 < 17),
    seamWeightsFrom_eq_cons (by norm_num : 12 < 17),
    seamWeightsFrom_eq_cons (by norm_num : 13 < 17),
    seamWeightsFrom_eq_cons (by norm_num : 14 < 17),
    seamWeightsFrom_eq_cons (by norm_num : 15 < 17),
    seamWeightsFrom_eq_cons (by norm_num : 16 < 17),
    seamWeightsFrom_eq_nil (by norm_num : 17 ≤ 17)]
  simp only [truncatedMersenneWeight]
  decide +kernel

theorem remainder_seventeen : seamIntegerGreedyRemainder 17 = 156085 := by
  unfold seamIntegerGreedyRemainder integerGreedyRemainder
  rw [seamWeights_seventeen,
    show seamSubsetTarget 17 = 8589803520 by norm_num [seamSubsetTarget]]
  decide +kernel

/-! ### Right branches -/

/-- A right branch is exactly the statement that the new terminal rank is
*taken*, so it is certified by a single bit of the successor row. -/
theorem not_upperOrMiddle_of_mem_succ {s : ℕ} (hs : 5 ≤ s)
    (hmem : s ∈ seamWordSupport (seamGreedyWord (s + 1))) :
    ¬ SeamGreedyUpperOrMiddleAt s hs := by
  intro hUM
  exact (seamGreedyWord_succ_isLargestFalseRank_terminal_of_upperOrMiddle
    s hs hUM).2.2.1 hmem

theorem not_upperOrMiddle_six : ¬ SeamGreedyUpperOrMiddleAt 6 (by norm_num) :=
  not_upperOrMiddle_of_mem_succ (by norm_num)
    ((SkipD3.mem_support_iff (by norm_num) (by norm_num)).mpr (by decide +kernel))

theorem not_upperOrMiddle_nine : ¬ SeamGreedyUpperOrMiddleAt 9 (by norm_num) :=
  not_upperOrMiddle_of_mem_succ (by norm_num)
    ((SkipD3.mem_support_iff (by norm_num) (by norm_num)).mpr (by decide +kernel))

/-! ### The step and iteration hypotheses really are satisfiable -/

/-- `deficit_step` at `s = 6`: the row-`6` remainder `34` sits `30` below the
half point `2 ^ 6 = 64`, the step is a right branch, and the conclusion is
realised with `D' = 125 ≥ 4 * 30 + 4`. -/
theorem deficit_step_witness :
    ∃ D' : ℕ, seamIntegerGreedyRemainder 7 + D' = 2 ^ 7 ∧ 4 * 30 + 4 ≤ D' :=
  deficit_step (s := 6) (D := 30) (by norm_num) not_upperOrMiddle_six
    (by rw [remainder_six]; norm_num)

/-- `deficit_iter` at `N = 6`, `k = 1`: a genuine one-row right run below the
half point. -/
theorem deficit_iter_witness :
    ∃ D' : ℕ, seamIntegerGreedyRemainder (6 + 1) + D' = 2 ^ (6 + 1) ∧
      4 ^ 1 * 30 + 4 ^ 1 ≤ D' + 1 :=
  deficit_iter (N := 6) (by norm_num) (D := 30)
    (by rw [remainder_six]; norm_num) 1
    (by
      intro j hj
      have hj0 : j = 0 := by omega
      subst hj0
      exact not_upperOrMiddle_six)

/-- The explicit counting law, instantiated at `N = 6`, `k = 1`:
`4 * (2 ^ 6 - 34) + 4 = 124 ≤ 2 ^ 7 + 1`. -/
theorem deficit_shrinks_witness :
    4 ^ 1 * (2 ^ 6 - seamIntegerGreedyRemainder 6) + 4 ^ 1 ≤ 2 ^ (6 + 1) + 1 :=
  deficit_shrinks_along_rightRun (N := 6) (k := 1) (by norm_num)
    (by rw [remainder_six]; norm_num)
    (by
      intro j hj
      have hj0 : j = 0 := by omega
      subst hj0
      exact not_upperOrMiddle_six)

/-- `surplus_step` at `s = 9`: the row-`9` remainder `541` sits `29` above the
half point `2 ^ 9 = 512`, `29 ≥ 2 * 9`, and the step is a right branch. -/
theorem surplus_step_witness :
    ∃ σ' : ℕ, seamIntegerGreedyRemainder (9 + 1) = 2 ^ (9 + 1) + σ' ∧
      3 * 29 ≤ σ' ∧ 2 * (9 + 1) ≤ σ' :=
  surplus_step (s := 9) (σ := 29) (by norm_num) not_upperOrMiddle_nine
    (by rw [remainder_nine]; norm_num) (by norm_num)

/-- The three bad rows `11, 12, 13` give a genuine **three-step** right run
above the half point, based at `N = 10` where the surplus is `111 ≥ 2 * 10`.
So `surplus_iter` is not vacuous even at `k = 3`: it predicts
`seamIntegerGreedyRemainder 13 ≥ 2 ^ 13 + 27 * 111 = 11189`, and the true
value is `15147`. -/
theorem surplus_iter_witness :
    ∃ σ' : ℕ, seamIntegerGreedyRemainder (10 + 3) = 2 ^ (10 + 3) + σ' ∧
      3 ^ 3 * 111 ≤ σ' ∧ 2 * (10 + 3) ≤ σ' := by
  refine surplus_iter (N := 10) (by norm_num) (σ := 111)
    (by rw [remainder_ten]; norm_num) (by norm_num) 3 ?_
  intro j hj
  interval_cases j
  · exact not_upperOrMiddle_of_not_largestSkipLateAt_succ (by norm_num)
      not_largestSkipLateAt_eleven
  · exact not_upperOrMiddle_of_not_largestSkipLateAt_succ (by norm_num)
      not_largestSkipLateAt_twelve
  · exact not_upperOrMiddle_of_not_largestSkipLateAt_succ (by norm_num)
      not_largestSkipLateAt_thirteen

/-! ### The remainder ceiling -/

/-- The good-row ceiling lemma, instantiated: row `14` is good
(`largestSkipLateAt_fourteen`), so it obeys the ceiling; its remainder is `392`
against a ceiling of `(7 * 2 ^ 14 + 4) / 3 = 38229`. -/
theorem obeysRemainderCeiling_fourteen : ObeysRemainderCeiling 14 :=
  three_mul_remainder_lt_of_largestSkipLateAt (by norm_num) largestSkipLateAt_fourteen

/-- The ceiling at the companion row `3 * 5 + 2 = 17`, checked directly. -/
theorem obeysRemainderCeiling_seventeen : ObeysRemainderCeiling 17 := by
  unfold ObeysRemainderCeiling
  rw [remainder_seventeen]
  norm_num

/-! ### Theorem B, instantiated -/

/-- The hypotheses of `exists_largestSkipLateAt_of_surplus` hold at `N = 5`:
`seamIntegerGreedyRemainder 5 = 71 = 2 ^ 5 + 39` with `39 ≥ 2 * 5`, and the
companion row `17` obeys the ceiling.  The theorem therefore *produces* a late
largest false rank somewhere in `[6, 17]`. -/
theorem theoremB_witness :
    ∃ t : ℕ, 6 ≤ t ∧ t ≤ 17 ∧ LargestSkipLateAt t :=
  exists_largestSkipLateAt_of_surplus (N := 5) (σ := 39) (by norm_num)
    (by rw [remainder_five]; norm_num) (by norm_num)
    obeysRemainderCeiling_seventeen

/-! ### Theorem A, instantiated -/

/-- The hypothesis of `Theorem A` holds at `N = 14`: `seamIntegerGreedyRemainder
14 = 392 ≤ 2 ^ 14`.  The theorem therefore *produces* a late largest false rank
somewhere in `[15, 29]`. -/
theorem theoremA_witness :
    ∃ t : ℕ, 15 ≤ t ∧ t ≤ 29 ∧ LargestSkipLateAt t :=
  exists_largestSkipLateAt_of_remainder_le_two_pow (N := 14) (by norm_num)
    (by rw [BitCorr2.seamIntegerGreedyRemainder_14]; norm_num)

end Witnesses

end

end ErdosProblems.BitR2
