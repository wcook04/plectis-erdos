/-
Copyright (c) 2026 Will Cook. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Will Cook
-/
import ErdosProblems.Three.T1

/-!
# D2 — counting consecutive declines cannot close the declined step

The brief for this file was:

> A decline at rank `k` means bit `2*s-k` of the entering capacity is `0`.
> Consecutive declines are therefore a run of zero bits.  Bound the number of
> CONSECUTIVE declines, then run the induction over blocks rather than single
> ranks: if at most `m` consecutive declines occur, the induction loses at most
> `m` lower terms per block and the taken step gains a full halving.  Measure
> the actual maximal run of consecutive declines over rows `6 … 800` first, then
> prove a bound on it if the data supports one.

The measurement was done (§7).  **The proposed block induction cannot obtain
the target from only a decline inequality and the subsequent take pattern, for
two independent reasons formalized here.**  This is a negative result about
that information set; the file contains no new
unconditional bound on `ρ s`, and in particular does *not* prove
`ρ s < 2 ^ (s+1)`.

**Reason 1 — a decline run of length `m` leaves one last-decline bound, not a
sum of `m` such bounds.**  The
greedy residual is frozen across a run of declines (`residual_eq_of_declineBlock`),
so the run's *last* decline supplies the bound and the earlier ones are
redundant: `residual_lt_weight_of_declineBlock` gives `R_b < w b`, which is
sharper than the first-decline bound `R_b < w (a+1)`
(`residual_lt_weight_first_of_declineBlock`).  The *leading powers* associated
with those two ranks differ by exactly the factor `2 ^ (m-1)`
(`declineBlock_gain`); that theorem is a pure exponent identity, not an exact
ratio between the full weights.  The run length has disappeared from
`residual_lt_two_pow_add_of_declineBlock`: the theorem retains only the last
declined rank.  Thus a count of the earlier declines does not sharpen that
particular bound.

**Reason 2 — one lower term defeats the proposed uniform implication.**
Write `weightTail s d = w d - 2 ^ (2*s-d)` for the lower binary terms of the
rank-`d` weight (`weightTail`).  Then

* the whole tail of taken ranks above `d` returns at most two thirds of a single
  `weightTail s d` (`three_mul_weightTail_sum_le`), so the deficit
  `weightTail s d / 3` is permanent; and
* that is not an artefact of a lossy estimate: starting from the largest residual
  the decline at rank `d` permits, the greedy genuinely takes every rank of
  `(d, D]` and still ends **at or above** the ceiling `2 ^ (2*s-D)`
  (`no_blockMethod_closure`, `blockRun_worst_excess`).

Hence *no* argument whose information about the residual entering the block is
the decline inequality `R < w d` plus the take pattern above `d` can establish
C6's invariant — whatever positive bound is placed on the run length, on the
block length, or on the number of declines within that formalization.
`not_blockMethod_sound` states this as the
falsity of the soundness statement.  Its witness is the artificial residual
`w d - 1`, not a residual proved reachable by the corpus greedy.  Compare
`T1.IntervalCeiling.two_pow_lt`,
which kills the same target for branch-*blind* rank-indexed ceilings; the present
no-go kills it for the branch-*aware* block method that knows exactly which ranks
were declined and which taken.

**Reason 2', empirically decisive.**  `run_of_length_one_breaks_invariant`:
row `13` carries a decline run of length **one** — the shortest there is, with
ranks `6` and `8` both taken (`thirteen_run_length_one`) — and C6's ceiling is
already destroyed at the end of it (`2 ^ 19 ≤ seamResidualUpto 13 7`, which is
`T1.not_residualInvariant`).  The loss that destroys the invariant is therefore
incurred at a run of length one, at the only `(s, d)` in the scanned range where
the invariant fails at all — so no positive upper bound on run length can
exclude this witness.  This does not establish a statistical correlation
between run length and failure.  It does show that longer runs need not fail:
row `20`, which carries runs of length `6` and `5`, satisfies the invariant at
the end of both
(`invariant_holds_twenty`), because a *later* decline resets the excess to the
much smaller `weightTail` of its own, later rank (§2, §3).

## What is proved

* §1 `DeclineBlock`, `TakeBlock`; `residual_eq_of_declineBlock`,
  `residual_lt_weight_of_declineBlock`, `residual_lt_weight_first_of_declineBlock`,
  `declineBlock_gain`, `residual_lt_two_pow_add_of_declineBlock`.
* §2 `residual_excess_le_of_takeBlock` — across a block of taken ranks the excess
  of the residual over C6's ceiling never increases.  (The taken step really does
  "gain a full halving", exactly as the brief says; that half is what §5 shows is
  not enough.)
* §3 `residual_lt_of_lastDecline` / `residual_excess_lt_weightTail` — the last
  declined rank `b` controls the whole tail: the residual at any later rank `D`
  exceeds `2 ^ (2*s-D)` by less than `weightTail s b`.  Corollaries
  `seamRemainder_lt_of_lastDecline` and `seamRemainder_lt_two_pow_succ_add`:
  `ρ s < 2 ^ (s+1) + 2 ^ (2*s-2*b+1)`.  This is *not new* — it is the rank-level
  form of `RemC6.seamIntegerGreedyRemainder_lt_of_largest_skip` — but it is
  derived here from the run structure alone, with no weight-word splitting and no
  lateness hypothesis.  Section 5 proves that the decline inequality plus the
  subsequent take pattern cannot uniformly remove the added term; it does not
  prove this displayed remainder bound numerically optimal for reachable corpus
  residuals.
* §4 `weightTail` and its enclosure `2 ^ (2*s-2*d) ≤ weightTail s d ≤
  2 ^ (2*s-2*d+1)`; the geometric repayment bound `three_mul_weightTail_sum_le`.
* §5 `blockRun` (the corpus step law `T1.greedyStep`, iterated),
  `blockRun_worst_invariant` (an exact identity), `blockRun_worst_takes`,
  `blockRun_worst_excess`, `no_blockMethod_closure`, `not_blockMethod_sound`,
  `blockMethod_excess_window`.
* §6 certificates, all on the corpus's own greedy.

## Where this leaves the located gap

`T4.seamRemainder_lt_two_pow_succ` needs
`hhigh : lateEntryRemainder s d₀ < 2 ^ (2*s-d₀+1)` at the first late rank `d₀`,
which is exactly C6's invariant at rank `d₀ - 1`, i.e. "the excess at rank
`d₀ - 1` is negative".  §3 bounds that excess above by `weightTail s b` for the
last declined rank `b ≤ d₀ - 1`, and §5 shows the block method admits residuals
whose excess is at least `weightTail s b / 3 - 1`
(`blockMethod_excess_window`).  Thus these local inequalities do not force a
negative excess: the artificial admissible witness has positive excess at every
permitted row and rank.  A successful proof must add information excluding that
witness, such as arithmetic information about the reachable residual; the local
take/decline pattern alone does not do so.

**Scope.**  The global invariant is false: this file imports
`T1.not_residualInvariant` and repackages its counterexample at `(13, 7)` in
`run_of_length_one_breaks_invariant`.  The independent scan in §7 found no
other failure in its stated range.  No new counterexample is proved here.
Nothing here shows that a method using the *entire* pattern from rank `2` fails — such a
method determines the residual exactly, since
`R_D = seamSubsetTarget s - ∑_{taken j ≤ D} w j`, and is therefore not an
induction carrying an inequality.  The no-go is about inequalities carried
across a block, which is what an induction has.

## Non-vacuity

Section 6 supplies concrete corpus witnesses for the principal decline-block and
take-block hypothesis shapes:
`declineBlock_twenty` (a length-`6` run),
`declineBlock_twenty_late` (a length-`5` run), `takeBlock_twenty_fourteen`,
`declineBlock_thirteen` (a length-`1` run), `takeBlock_thirteen` (a length-`5`
take block), and `takeBlock_self` for the degenerate case.  The remainder bound
is instantiated as `seamRemainder_twenty_lt` and
`seamRemainder_thirteen_lt`.  The counter-model is evaluated in numbers at
`s = 20, d = 6, D = 13` (`blockRun_twenty_six`, `blockRun_twenty_six_exceeds`),
and the run collapse is exhibited in numbers (`run_collapse_twenty`).  The
row-20 remainder instance uses the empty take block `takeBlock_self 20 19`;
the row-13 instance supplies a nonempty take block.
-/

namespace ErdosProblems.Decl.D2

open Erdos249257 Erdos249257.HalfCylinderIntegerGreedy
open ErdosProblems.Three.T1

/-! ## 1. Decline blocks and take blocks -/

/-- Every rank of the block `(a, b]` is **declined** by the descending seam
greedy of row `s`.  (Indexed by `k = rank - 1`, so that no `ℕ`-subtraction
appears: `k` ranges over `[a, b)` and the rank offered is `k + 1`.) -/
def DeclineBlock (s a b : ℕ) : Prop :=
  ∀ k : ℕ, a ≤ k → k < b → seamResidualUpto s k < truncatedMersenneWeight s (k + 1)

/-- Every rank of the block `(a, b]` is **taken** by the descending seam greedy
of row `s`. -/
def TakeBlock (s a b : ℕ) : Prop :=
  ∀ k : ℕ, a ≤ k → k < b → truncatedMersenneWeight s (k + 1) ≤ seamResidualUpto s k

theorem declineBlock_self (s a : ℕ) : DeclineBlock s a a := by
  intro k _ hk; omega

theorem takeBlock_self (s a : ℕ) : TakeBlock s a a := by
  intro k _ hk; omega

/-- **A decline run freezes the residual.** -/
theorem residual_eq_of_declineBlock {s a b : ℕ} (ha : 1 ≤ a) (hab : a ≤ b)
    (h : DeclineBlock s a b) :
    seamResidualUpto s b = seamResidualUpto s a := by
  induction b, hab using Nat.le_induction with
  | base => rfl
  | succ b hab ih =>
      have hdec := h b hab (by omega)
      rw [seamResidualUpto_succ (by omega : 1 ≤ b), if_neg (not_le.mpr hdec)]
      exact ih (fun k hk1 hk2 => h k hk1 (by omega))

/-- **Only the last decline of a run counts.**  After a run of declines covering
the ranks `a+1, …, b`, the residual is trapped below the rank-`b` weight — the
*smallest* weight of the run — no matter how long the run is. -/
theorem residual_lt_weight_of_declineBlock {s a b : ℕ} (ha : 1 ≤ a) (hab : a < b)
    (h : DeclineBlock s a b) :
    seamResidualUpto s b < truncatedMersenneWeight s b := by
  obtain ⟨c, rfl⟩ : ∃ c, b = c + 1 := ⟨b - 1, by omega⟩
  have hdec := h c (by omega) (by omega)
  rw [seamResidualUpto_succ (by omega : 1 ≤ c), if_neg (not_le.mpr hdec)]
  exact hdec

/-- The bound one gets from the *first* decline of the same run. -/
theorem residual_lt_weight_first_of_declineBlock {s a b : ℕ} (ha : 1 ≤ a) (hab : a < b)
    (h : DeclineBlock s a b) :
    seamResidualUpto s b < truncatedMersenneWeight s (a + 1) := by
  rw [residual_eq_of_declineBlock ha (by omega) h]
  exact h a le_rfl (by omega)

/-- **A pure exponent comparison.**  The leading power at rank `b` and the
leading power at rank `a+1` differ by exactly `2 ^ (b-a-1)`, i.e.
`2 ^ (m-1)` for `m = b-a`.  This theorem mentions neither `DeclineBlock` nor
the full weights, so it does not assert that their ratio is exactly this
factor. -/
theorem declineBlock_gain {s a b : ℕ} (hab : a < b) (hbs : b ≤ 2 * s) :
    2 ^ (b - a - 1) * 2 ^ (2 * s - b) = 2 ^ (2 * s - a - 1) := by
  rw [← pow_add]
  congr 1
  omega

/-- The quantitative form of the run collapse: the run length has disappeared
from the bound entirely. -/
theorem residual_lt_two_pow_add_of_declineBlock {s a b : ℕ} (ha : 1 ≤ a) (hab : a < b)
    (hbs : b ≤ s) (h : DeclineBlock s a b) :
    seamResidualUpto s b < 2 ^ (2 * s - b) + 2 ^ (2 * s - 2 * b + 1) := by
  have h1 := residual_lt_weight_of_declineBlock ha hab h
  have h2 := ErdosProblems.RemC6.truncatedMersenneWeight_le (s := s) (d := b)
    (by omega) hbs
  omega

/-! ## 2. A take block cannot increase the excess over the ceiling -/

/-- **Excess monotonicity.**  Write `E d := seamResidualUpto s d - 2 ^ (2*s-d)`
for the (signed) excess of the residual over C6's ceiling.  Across a block of
*taken* ranks the excess never increases: the ceiling halves and the accepted
weight pays for the halving.  Stated `ℕ`-safely by moving both subtractions to
the other side. -/
theorem residual_excess_le_of_takeBlock {s a b : ℕ} (ha : 1 ≤ a) (hab : a ≤ b)
    (hbs : b ≤ 2 * s) (h : TakeBlock s a b) :
    seamResidualUpto s b + 2 ^ (2 * s - a) ≤ seamResidualUpto s a + 2 ^ (2 * s - b) := by
  induction b, hab using Nat.le_induction with
  | base => omega
  | succ b hab ih =>
      have hIH := ih (by omega) (fun k hk1 hk2 => h k hk1 (by omega))
      have htake := h b hab (by omega)
      have hw := ErdosProblems.RemC6.two_pow_le_truncatedMersenneWeight
        (s := s) (d := b + 1) (by omega) (by omega)
      have hdbl : (2 : ℕ) ^ (2 * s - b) = 2 ^ (2 * s - (b + 1)) + 2 ^ (2 * s - (b + 1)) := by
        rw [show 2 * s - b = (2 * s - (b + 1)) + 1 by omega, pow_succ]; ring
      rw [seamResidualUpto_succ (by omega : 1 ≤ b), if_pos htake]
      omega

/-! ## 3. The master bound: the last declined rank controls the whole tail -/

/-- **The master bound.**  Let `b` be a declined rank of row `s` (the end of a
decline run starting after `a`), and suppose every rank of `(b, D]` is taken.
Then the residual at `D` exceeds C6's ceiling by less than the *lower binary
terms of the single weight* `w b`, whatever happened before `b` and however long
the run was. -/
theorem residual_lt_of_lastDecline {s a b D : ℕ} (ha : 1 ≤ a) (hab : a < b) (hbD : b ≤ D)
    (hDs : D ≤ 2 * s) (hdec : DeclineBlock s a b) (htake : TakeBlock s b D) :
    seamResidualUpto s D + 2 ^ (2 * s - b) <
      truncatedMersenneWeight s b + 2 ^ (2 * s - D) := by
  have h1 := residual_lt_weight_of_declineBlock ha hab hdec
  have h2 := residual_excess_le_of_takeBlock (s := s) (a := b) (b := D)
    (by omega) hbD hDs htake
  omega

/-- The same at the terminal rank: a bound on `ρ s` from its last declined
rank. -/
theorem seamRemainder_lt_of_lastDecline {s a b : ℕ} (hs : 4 ≤ s) (ha : 1 ≤ a) (hab : a < b)
    (hbs : b ≤ s - 1) (hdec : DeclineBlock s a b) (htake : TakeBlock s b (s - 1)) :
    seamIntegerGreedyRemainder s + 2 ^ (2 * s - b) <
      truncatedMersenneWeight s b + 2 ^ (s + 1) := by
  have h := residual_lt_of_lastDecline ha hab hbs (by omega) hdec htake
  rwa [seamResidualUpto_last (by omega), show 2 * s - (s - 1) = s + 1 by omega] at h

/-- Collapsed: `ρ s < 2 ^ (s+1) + 2 ^ (2*s-2*b+1)` where `b` is the last declined
rank.  (This is the rank-level analogue of `RemC6`'s
`seamIntegerGreedyRemainder_lt_of_largest_skip`, obtained here without splitting
the weight word and without any lateness hypothesis.) -/
theorem seamRemainder_lt_two_pow_succ_add {s a b : ℕ} (hs : 4 ≤ s) (ha : 1 ≤ a) (hab : a < b)
    (hbs : b ≤ s - 1) (hdec : DeclineBlock s a b) (htake : TakeBlock s b (s - 1)) :
    seamIntegerGreedyRemainder s < 2 ^ (s + 1) + 2 ^ (2 * s - 2 * b + 1) := by
  have h := seamRemainder_lt_of_lastDecline hs ha hab hbs hdec htake
  have hup := ErdosProblems.RemC6.truncatedMersenneWeight_le (s := s) (d := b)
    (by omega) (by omega)
  have hlow := ErdosProblems.RemC6.two_pow_le_truncatedMersenneWeight (s := s) (d := b)
    (by omega) (by omega)
  omega

/-! ## 4. The lower binary terms of a weight, and how little of them is repaid -/

/-- `weightTail s d = w d - 2 ^ (2*s-d)`: the "own lower binary terms" of the
rank-`d` weight, i.e. `2 ^ (2*s-2*d) + 2 ^ (2*s-3*d) + …`.  This is exactly the
quantity by which a declined rank overshoots C6's ceiling. -/
def weightTail (s d : ℕ) : ℕ := truncatedMersenneWeight s d - 2 ^ (2 * s - d)

theorem two_pow_add_two_pow_le_weight {s d : ℕ} (hd : 1 ≤ d) (hds : d ≤ s) :
    2 ^ (2 * s - d) + 2 ^ (2 * s - 2 * d) ≤ truncatedMersenneWeight s d := by
  have hP : (1 : ℕ) ≤ 2 ^ d := Nat.one_le_two_pow
  have hP2 : (2 : ℕ) ≤ 2 ^ d := by
    have : (2 : ℕ) ^ 1 ≤ 2 ^ d := Nat.pow_le_pow_right (by norm_num) hd
    simpa using this
  have hpos : 0 < 2 ^ d - 1 := by omega
  have hB : 0 < (2 : ℕ) ^ (2 * s - 2 * d) := Nat.two_pow_pos _
  have e1 : (2 : ℕ) ^ (2 * s - d) * 2 ^ d = 2 ^ (2 * s) := by
    rw [← pow_add]; congr 1; omega
  have e2 : (2 : ℕ) ^ (2 * s - 2 * d) * 2 ^ d = 2 ^ (2 * s - d) := by
    rw [← pow_add]; congr 1; omega
  have e3 : (2 ^ (2 * s - d) + 2 ^ (2 * s - 2 * d)) * 2 ^ d
      = 2 ^ (2 * s) + 2 ^ (2 * s - d) := by
    rw [add_mul, e1, e2]
  have e4 : (2 ^ (2 * s - d) + 2 ^ (2 * s - 2 * d)) * (2 ^ d - 1)
      + (2 ^ (2 * s - d) + 2 ^ (2 * s - 2 * d))
      = (2 ^ (2 * s - d) + 2 ^ (2 * s - 2 * d)) * 2 ^ d := by
    rw [← Nat.mul_succ, Nat.succ_eq_add_one, Nat.sub_add_cancel hP]
  have h4 : (4 : ℕ) ^ s = 2 ^ (2 * s) := by rw [pow_mul]; norm_num
  show (2 : ℕ) ^ (2 * s - d) + 2 ^ (2 * s - 2 * d) ≤ 4 ^ s / (2 ^ d - 1)
  rw [Nat.le_div_iff_mul_le hpos, h4]
  omega

theorem weight_eq_two_pow_add_weightTail {s d : ℕ} (hd : 1 ≤ d) (hds : d ≤ 2 * s) :
    truncatedMersenneWeight s d = 2 ^ (2 * s - d) + weightTail s d := by
  have h := ErdosProblems.RemC6.two_pow_le_truncatedMersenneWeight hd hds
  have hp : 0 < (2 : ℕ) ^ (2 * s - d) := Nat.two_pow_pos _
  show _ = _ + (truncatedMersenneWeight s d - 2 ^ (2 * s - d))
  omega

theorem two_pow_le_weightTail {s d : ℕ} (hd : 1 ≤ d) (hds : d ≤ s) :
    2 ^ (2 * s - 2 * d) ≤ weightTail s d := by
  have h := two_pow_add_two_pow_le_weight hd hds
  have hp : 0 < (2 : ℕ) ^ (2 * s - d) := Nat.two_pow_pos _
  have hq : 0 < (2 : ℕ) ^ (2 * s - 2 * d) := Nat.two_pow_pos _
  show _ ≤ truncatedMersenneWeight s d - 2 ^ (2 * s - d)
  omega

theorem weightTail_le {s d : ℕ} (hd : 1 ≤ d) (hds : d ≤ s) :
    weightTail s d ≤ 2 ^ (2 * s - 2 * d + 1) := by
  have h := ErdosProblems.RemC6.truncatedMersenneWeight_le hd hds
  have hp : 0 < (2 : ℕ) ^ (2 * s - d) := Nat.two_pow_pos _
  have hq : 0 < (2 : ℕ) ^ (2 * s - 2 * d + 1) := Nat.two_pow_pos _
  show truncatedMersenneWeight s d - 2 ^ (2 * s - d) ≤ _
  omega

/-- Geometric tail bound: `3 * ∑_{j ≥ a} 2 ^ (2*s-2*j+1) ≤ 4 * 2 ^ (2*s-2*a+1)`. -/
private theorem geomTail_aux (s : ℕ) :
    ∀ n a : ℕ, s ≤ a + n →
      3 * ∑ j ∈ Finset.Ico a s, 2 ^ (2 * s - 2 * j + 1) ≤ 4 * 2 ^ (2 * s - 2 * a + 1) := by
  intro n
  induction n with
  | zero =>
      intro a ha
      rw [Finset.Ico_eq_empty (by omega)]
      simp
  | succ n ih =>
      intro a ha
      rcases Nat.lt_or_ge a s with hlt | hge
      · rw [Finset.sum_eq_sum_Ico_succ_bot hlt]
        have hIH := ih (a + 1) (by omega)
        have he : (4 : ℕ) * 2 ^ (2 * s - 2 * (a + 1) + 1) = 2 ^ (2 * s - 2 * a + 1) := by
          rw [show (4 : ℕ) = 2 ^ 2 by norm_num, ← pow_add]
          congr 1
          omega
        omega
      · rw [Finset.Ico_eq_empty (by omega)]
        simp

/-- **The repayment lemma.**  The sum of the lower binary terms at all ranks
above `d` is at most two thirds of `weightTail s d`.  Interpreting that sum as
greedy repayment additionally assumes those ranks are taken.  Independently
MEASURED over `s ∈ [6,120]` and `d ∈ [2,s-2]`, the ratio was at most
`0.333333`; the sharper factor is not proved here. -/
theorem three_mul_weightTail_sum_le {s d : ℕ} (hd : 1 ≤ d) (hds : d < s) :
    3 * ∑ j ∈ Finset.Ico (d + 1) s, weightTail s j ≤ 2 * weightTail s d := by
  have hterm : ∀ j ∈ Finset.Ico (d + 1) s, weightTail s j ≤ 2 ^ (2 * s - 2 * j + 1) := by
    intro j hj
    rw [Finset.mem_Ico] at hj
    exact weightTail_le (by omega) (by omega)
  have hsum : ∑ j ∈ Finset.Ico (d + 1) s, weightTail s j
      ≤ ∑ j ∈ Finset.Ico (d + 1) s, 2 ^ (2 * s - 2 * j + 1) := Finset.sum_le_sum hterm
  have hgeom := geomTail_aux s s (d + 1) (by omega)
  have he : (2 : ℕ) ^ (2 * s - 2 * d) = 2 ^ (2 * s - 2 * (d + 1) + 1) * 2 := by
    rw [← pow_succ]; congr 1; omega
  have hlow := two_pow_le_weightTail (s := s) (d := d) hd (by omega)
  omega

private theorem sum_weightTail_block_le {s d n : ℕ} (hd : 1 ≤ d) (hds : d < s)
    (hn : d + n + 1 ≤ s) :
    3 * ∑ j ∈ Finset.Ico (d + 1) (d + n + 1), weightTail s j ≤ 2 * weightTail s d := by
  have hsub : (Finset.Ico (d + 1) (d + n + 1)) ⊆ Finset.Ico (d + 1) s :=
    Finset.Ico_subset_Ico le_rfl hn
  have h : ∑ j ∈ Finset.Ico (d + 1) (d + n + 1), weightTail s j
      ≤ ∑ j ∈ Finset.Ico (d + 1) s, weightTail s j :=
    Finset.sum_le_sum_of_subset hsub
  have h2 := three_mul_weightTail_sum_le (s := s) (d := d) hd hds
  omega

/-! ## 5. The block no-go: the decline inequality plus a full run of takes is
consistent with the invariant failing -/

/-- The descending greedy run over the ranks `d+1, d+2, …, d+n`, started at
residual `R`.  Written with `T1.greedyStep`, so this really is the corpus step
law and nothing else. -/
def blockRun (s d R : ℕ) : ℕ → ℕ
  | 0 => R
  | n + 1 => greedyStep s (d + n + 1) (blockRun s d R n)

theorem blockRun_zero (s d R : ℕ) : blockRun s d R 0 = R := rfl

theorem blockRun_succ (s d R n : ℕ) :
    blockRun s d R (n + 1) = greedyStep s (d + n + 1) (blockRun s d R n) := rfl

/-- The worst residual the decline at rank `d` permits. -/
def worstDeclined (s d : ℕ) : ℕ := truncatedMersenneWeight s d - 1

theorem worstDeclined_lt {s d : ℕ} (hd : 1 ≤ d) (hds : d ≤ 2 * s) :
    worstDeclined s d < truncatedMersenneWeight s d := by
  have h := ErdosProblems.RemC6.two_pow_le_truncatedMersenneWeight hd hds
  have : (1 : ℕ) ≤ 2 ^ (2 * s - d) := Nat.one_le_two_pow
  show truncatedMersenneWeight s d - 1 < _
  omega

private theorem blockRun_lower_of_invariant {s d n : ℕ} (hd : 1 ≤ d) (hds : d < s)
    (hn : d + n < s)
    (hinv : blockRun s d (worstDeclined s d) n
          + (∑ j ∈ Finset.Ico (d + 1) (d + n + 1), weightTail s j) + 1
        = 2 ^ (2 * s - (d + n)) + weightTail s d) :
    2 ^ (2 * s - (d + n)) ≤ blockRun s d (worstDeclined s d) n := by
  have hsum := sum_weightTail_block_le (s := s) (d := d) (n := n) hd hds (by omega)
  have hfour : (4 : ℕ) ≤ 2 ^ (2 * s - 2 * d) := by
    calc (4 : ℕ) = 2 ^ 2 := by norm_num
    _ ≤ 2 ^ (2 * s - 2 * d) := Nat.pow_le_pow_right (by norm_num) (by omega)
  have hlow := two_pow_le_weightTail (s := s) (d := d) hd (by omega)
  omega

/-- **The block invariant for the worst admissible residual.**  Started at the
largest value the decline at rank `d` allows, the greedy takes every rank of
`(d, d+n]` and the residual is *exactly* `2 ^ (2*s-(d+n)) + weightTail s d`
minus the lower terms it has spent, minus one. -/
theorem blockRun_worst_invariant {s d : ℕ} (hd : 1 ≤ d) (hds : d < s) :
    ∀ n : ℕ, d + n < s →
      blockRun s d (worstDeclined s d) n
          + (∑ j ∈ Finset.Ico (d + 1) (d + n + 1), weightTail s j) + 1
        = 2 ^ (2 * s - (d + n)) + weightTail s d := by
  intro n
  induction n with
  | zero =>
      intro _
      have hw := ErdosProblems.RemC6.two_pow_le_truncatedMersenneWeight
        (s := s) (d := d) hd (by omega)
      have hone : (1 : ℕ) ≤ 2 ^ (2 * s - d) := Nat.one_le_two_pow
      rw [blockRun_zero, Finset.Ico_self, Finset.sum_empty]
      show truncatedMersenneWeight s d - 1 + 0 + 1
        = 2 ^ (2 * s - (d + 0)) + (truncatedMersenneWeight s d - 2 ^ (2 * s - d))
      simp only [Nat.add_zero]
      omega
  | succ n ih =>
      intro hn
      have hIH := ih (by omega)
      have hfits : 2 ^ (2 * s - (d + n)) ≤ blockRun s d (worstDeclined s d) n :=
        blockRun_lower_of_invariant hd hds (by omega) hIH
      have hwup := ErdosProblems.RemC6.truncatedMersenneWeight_le
        (s := s) (d := d + n + 1) (by omega) (by omega)
      have hmono : (2 : ℕ) ^ (2 * s - 2 * (d + n + 1) + 1) ≤ 2 ^ (2 * s - (d + n + 1)) :=
        Nat.pow_le_pow_right (by norm_num) (by omega)
      have hdbl : (2 : ℕ) ^ (2 * s - (d + n)) = 2 ^ (2 * s - (d + n + 1)) + 2 ^ (2 * s - (d + n + 1)) := by
        rw [show 2 * s - (d + n) = (2 * s - (d + n + 1)) + 1 by omega, pow_succ]; ring
      have hwle : truncatedMersenneWeight s (d + n + 1) ≤ blockRun s d (worstDeclined s d) n := by
        omega
      have hstep : blockRun s d (worstDeclined s d) (n + 1)
          = blockRun s d (worstDeclined s d) n - truncatedMersenneWeight s (d + n + 1) := by
        rw [blockRun_succ, greedyStep, if_pos hwle]
      have hsplit := weight_eq_two_pow_add_weightTail
        (s := s) (d := d + n + 1) (by omega) (by omega)
      have hsumtop : ∑ j ∈ Finset.Ico (d + 1) (d + (n + 1) + 1), weightTail s j
          = (∑ j ∈ Finset.Ico (d + 1) (d + n + 1), weightTail s j)
            + weightTail s (d + n + 1) := by
        rw [show d + (n + 1) + 1 = (d + n + 1) + 1 by omega,
          Finset.sum_Ico_succ_top (by omega : d + 1 ≤ d + n + 1)]
      rw [hstep, hsumtop, show d + (n + 1) = (d + n + 1) by omega]
      omega

/-- The residual of the worst-case block run never falls below the ceiling it is
supposed to beat. -/
theorem two_pow_le_blockRun_worst {s d : ℕ} (hd : 1 ≤ d) (hds : d < s) (n : ℕ)
    (hn : d + n < s) :
    2 ^ (2 * s - (d + n)) ≤ blockRun s d (worstDeclined s d) n :=
  blockRun_lower_of_invariant hd hds hn (blockRun_worst_invariant hd hds n hn)

/-- Every rank of the block is genuinely taken by the worst-case run, so the run
really is "one decline followed by nothing but takes". -/
theorem blockRun_worst_takes {s d : ℕ} (hd : 1 ≤ d) (hds : d < s) (n : ℕ) (hn : d + n < s) :
    truncatedMersenneWeight s (d + n + 1) ≤ blockRun s d (worstDeclined s d) n := by
  have hfits := two_pow_le_blockRun_worst hd hds n hn
  have hwup := ErdosProblems.RemC6.truncatedMersenneWeight_le
    (s := s) (d := d + n + 1) (by omega) (by omega)
  have hmono : (2 : ℕ) ^ (2 * s - 2 * (d + n + 1) + 1) ≤ 2 ^ (2 * s - (d + n + 1)) :=
    Nat.pow_le_pow_right (by norm_num) (by omega)
  have hdbl : (2 : ℕ) ^ (2 * s - (d + n)) = 2 ^ (2 * s - (d + n + 1)) + 2 ^ (2 * s - (d + n + 1)) := by
    rw [show 2 * s - (d + n) = (2 * s - (d + n + 1)) + 1 by omega, pow_succ]; ring
  omega

/-- **The quantitative no-go.**  Started at the worst residual the decline at
rank `d` permits and run through a full block of takes, the greedy ends at least
`weightTail s d / 3` *above* the ceiling `2 ^ (2*s-(d+n))` it would have to be
below.  The excess does not shrink with the block length. -/
theorem blockRun_worst_excess {s d : ℕ} (hd : 1 ≤ d) (hds : d < s) (n : ℕ) (hn : d + n < s) :
    3 * 2 ^ (2 * s - (d + n)) + weightTail s d
      ≤ 3 * blockRun s d (worstDeclined s d) n + 3 := by
  have hinv := blockRun_worst_invariant hd hds n hn
  have hsum := sum_weightTail_block_le (s := s) (d := d) (n := n) hd hds (by omega)
  omega

/-- **The no-go for the proposed universal implication.**  For every permitted
row `s`, rank `d`, and block end `D`, there is an artificial residual `R` which
* satisfies the decline inequality at rank `d` (`R < w d`), and
* is taken at every single rank of `(d, D]`,

yet whose final value is **not** below C6's ceiling `2 ^ (2*s-D)`.  Hence no
argument that quantifies over every residual satisfying only the decline
inequality and the take equalities can establish the invariant.  This does not
exclude an argument that also characterizes which residuals are reachable from
the actual prefix.  Compare `T1.IntervalCeiling.two_pow_lt`, which kills the same target
for branch-*blind* ceilings; this kills it for the branch-*aware* block method. -/
theorem no_blockMethod_closure {s d D : ℕ} (hd : 1 ≤ d) (hdD : d ≤ D) (hDs : D < s) :
    ∃ R : ℕ, R < truncatedMersenneWeight s d ∧
      (∀ n : ℕ, n < D - d → truncatedMersenneWeight s (d + n + 1) ≤ blockRun s d R n) ∧
      2 ^ (2 * s - D) ≤ blockRun s d R (D - d) := by
  refine ⟨worstDeclined s d, worstDeclined_lt hd (by omega), ?_, ?_⟩
  · intro n hn
    exact blockRun_worst_takes hd (by omega) n (by omega)
  · have h := two_pow_le_blockRun_worst (s := s) (d := d) hd (by omega) (D - d) (by omega)
    rwa [show d + (D - d) = D by omega] at h

/-- The negated universal implication, spelled out: these local hypotheses are
not sufficient for the invariant. -/
theorem not_blockMethod_sound {s d D : ℕ} (hd : 1 ≤ d) (hdD : d ≤ D) (hDs : D < s) :
    ¬ (∀ R : ℕ, R < truncatedMersenneWeight s d →
        (∀ n : ℕ, n < D - d → truncatedMersenneWeight s (d + n + 1) ≤ blockRun s d R n) →
        blockRun s d R (D - d) < 2 ^ (2 * s - D)) := by
  intro hcon
  obtain ⟨R, hR1, hR2, hR3⟩ := no_blockMethod_closure hd hdD hDs
  exact absurd (hcon R hR1 hR2) (by omega)

/-- **The block method's excess window.**  Section 3 gives an upper bound below
`weightTail s d` for an actual residual satisfying its decline-block and
take-block hypotheses.  This theorem gives both bounds for the artificial worst
admissible residual `w d - 1`: its excess is at least
`weightTail s d / 3 - 1` and remains below `weightTail s d`.  Thus the proposed
uniform implication over every residual allowed by the decline inequality must
tolerate a positive-excess witness at every permitted row and rank. -/
theorem blockMethod_excess_window {s d : ℕ} (hd : 1 ≤ d) (hds : d < s) (n : ℕ)
    (hn : d + n < s) :
    weightTail s d ≤
        3 * (blockRun s d (worstDeclined s d) n - 2 ^ (2 * s - (d + n))) + 3 ∧
      blockRun s d (worstDeclined s d) n - 2 ^ (2 * s - (d + n)) < weightTail s d := by
  have hinv := blockRun_worst_invariant hd hds n hn
  have hfits := two_pow_le_blockRun_worst hd hds n hn
  have hsum := sum_weightTail_block_le (s := s) (d := d) (n := n) hd hds (by omega)
  have hpos : 0 < weightTail s d := by
    have h := two_pow_le_weightTail (s := s) (d := d) hd (by omega)
    have : 0 < (2 : ℕ) ^ (2 * s - 2 * d) := Nat.two_pow_pos _
    omega
  omega

/-- Excess form of the master bound of §3, for direct comparison with §5. -/
theorem residual_excess_lt_weightTail {s a b D : ℕ} (ha : 1 ≤ a) (hab : a < b) (hbD : b ≤ D)
    (hDs : D ≤ 2 * s) (hdec : DeclineBlock s a b) (htake : TakeBlock s b D) :
    seamResidualUpto s D < 2 ^ (2 * s - D) + weightTail s b := by
  have h := residual_lt_of_lastDecline ha hab hbD hDs hdec htake
  have hsplit := weight_eq_two_pow_add_weightTail (s := s) (d := b) (by omega) (by omega)
  omega

/-! ## 6. Certificates: the hypotheses are met, and run length is the wrong
currency -/

namespace Concrete

/-! ### Row 20: two long decline runs, and the run collapse in numbers -/

/-- Ranks `8, …, 13` of row `20` are all declined: a decline run of length `6`. -/
theorem declineBlock_twenty : DeclineBlock 20 7 13 := by
  intro k hk1 hk2
  interval_cases k <;>
    norm_num [seamResidualUpto, seamResidual, truncatedMersenneWeight, seamSubsetTarget]

/-- Rank `14` of row `20` is taken, so the run really ends at `13`. -/
theorem takeBlock_twenty_fourteen : TakeBlock 20 13 14 := by
  intro k hk1 hk2
  interval_cases k
  norm_num [seamResidualUpto, seamResidual, truncatedMersenneWeight, seamSubsetTarget]

/-- Ranks `15, …, 19` of row `20` are all declined: a second run, of length `5`,
ending at the terminal rank. -/
theorem declineBlock_twenty_late : DeclineBlock 20 14 19 := by
  intro k hk1 hk2
  interval_cases k <;>
    norm_num [seamResidualUpto, seamResidual, truncatedMersenneWeight, seamSubsetTarget]

theorem seamResidualUpto_twenty_thirteen : seamResidualUpto 20 13 = 67662313 := by
  norm_num [seamResidualUpto, seamResidual, truncatedMersenneWeight, seamSubsetTarget]

/-- **The run collapse in numbers.**  After the length-`6` run of row `20` the
residual is `67662313`.  The *last* decline of the run bounds it by
`w 13 = 134234114`; the *first* decline of the run bounds it only by
`w 8 = 4311810305`.  The theorem proves
`2 ^ 5 * w 13 ≤ w 8`; the full weights do not have exact ratio `2 ^ 5`. -/
theorem run_collapse_twenty :
    seamResidualUpto 20 13 < truncatedMersenneWeight 20 13 ∧
      2 ^ (13 - 7 - 1) * truncatedMersenneWeight 20 13 ≤ truncatedMersenneWeight 20 8 := by
  constructor
  · exact residual_lt_weight_of_declineBlock (by norm_num) (by norm_num) declineBlock_twenty
  · norm_num [truncatedMersenneWeight]

/-- Row `20` satisfies C6's ceiling at the end of *both* of its long runs. -/
theorem invariant_holds_twenty :
    seamResidualUpto 20 13 < 2 ^ (2 * 20 - 13) ∧ seamResidualUpto 20 19 < 2 ^ (2 * 20 - 19) := by
  constructor <;>
    norm_num [seamResidualUpto, seamResidual, truncatedMersenneWeight, seamSubsetTarget]

/-- The master bound of §3 fires at row `20` with last declined rank `19`. -/
theorem seamRemainder_twenty_lt : seamIntegerGreedyRemainder 20 < 2 ^ (20 + 1) + 2 ^ (2 * 20 - 2 * 19 + 1) :=
  seamRemainder_lt_two_pow_succ_add (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    declineBlock_twenty_late (takeBlock_self 20 19)

/-! ### Row 13: a decline run of length ONE already destroys the invariant -/

/-- Rank `7` of row `13` is declined. -/
theorem declineBlock_thirteen : DeclineBlock 13 6 7 := by
  intro k hk1 hk2
  interval_cases k
  norm_num [seamResidualUpto, seamResidual, truncatedMersenneWeight, seamSubsetTarget]

/-- Ranks `6` and `8` of row `13` are taken, so the decline at rank `7` is an
isolated run of length exactly one. -/
theorem thirteen_run_length_one :
    truncatedMersenneWeight 13 6 ≤ seamResidualUpto 13 5 ∧
      truncatedMersenneWeight 13 8 ≤ seamResidualUpto 13 7 := by
  constructor <;>
    norm_num [seamResidualUpto, seamResidual, truncatedMersenneWeight, seamSubsetTarget]

/-- Ranks `8, …, 12` of row `13` are all taken. -/
theorem takeBlock_thirteen : TakeBlock 13 7 12 := by
  intro k hk1 hk2
  interval_cases k <;>
    norm_num [seamResidualUpto, seamResidual, truncatedMersenneWeight, seamSubsetTarget]

/-- **The decisive certificate for this angle.**  Row `13` carries a decline run
of length `1` — the shortest possible — and C6's ceiling is *already* destroyed
at the end of it.  Bounding the number of consecutive declines therefore cannot
repair the induction: the bound `m ≤ 1` is met here and the step still fails.
(The failure itself is `T1.not_residualInvariant`; what is added here is that it
happens at a length-one run.) -/
theorem run_of_length_one_breaks_invariant :
    DeclineBlock 13 6 7 ∧ 2 ^ (2 * 13 - 7) ≤ seamResidualUpto 13 7 := by
  refine ⟨declineBlock_thirteen, ?_⟩
  rw [seamResidualUpto_thirteen_seven]
  norm_num

/-- The master bound of §3 at row `13`: from the single declined rank `7` and
the taken block above it, `ρ 13 < 2 ^ 14 + 2 ^ 13`.  (True value `15147`.) -/
theorem seamRemainder_thirteen_lt :
    seamIntegerGreedyRemainder 13 < 2 ^ (13 + 1) + 2 ^ (2 * 13 - 2 * 7 + 1) :=
  seamRemainder_lt_two_pow_succ_add (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    declineBlock_thirteen takeBlock_thirteen

/-! ### The counter-model, in numbers -/

/-- The worst residual the decline at rank `6` of row `20` permits. -/
theorem worstDeclined_twenty_six : worstDeclined 20 6 = 17452565519 := by
  norm_num [worstDeclined, truncatedMersenneWeight]

/-- **The counter-model evaluated.**  Started at `w 6 - 1`, the greedy takes
every one of the ranks `7, …, 13` and finishes at `316837451`, which is more than
twice the ceiling `2 ^ (2*20-13) = 134217728` it would have to be under.  The
whole excess is the single lower term `weightTail 20 6 = 272696336` that the
decline at rank `6` was allowed to carry, of which only about a third has been
repaid. -/
theorem blockRun_twenty_six :
    blockRun 20 6 (worstDeclined 20 6) 7 = 316837451 := by
  norm_num [blockRun, greedyStep, worstDeclined, truncatedMersenneWeight]

theorem blockRun_twenty_six_exceeds :
    2 ^ (2 * 20 - 13) ≤ blockRun 20 6 (worstDeclined 20 6) 7 := by
  rw [blockRun_twenty_six]; norm_num

theorem weightTail_twenty_six : weightTail 20 6 = 272696336 := by
  norm_num [weightTail, truncatedMersenneWeight]

/-- The general no-go instantiated at `s = 20`, `d = 6`, `D = 13`. -/
theorem no_blockMethod_closure_twenty :
    ∃ R : ℕ, R < truncatedMersenneWeight 20 6 ∧
      (∀ n : ℕ, n < 13 - 6 → truncatedMersenneWeight 20 (6 + n + 1) ≤ blockRun 20 6 R n) ∧
      2 ^ (2 * 20 - 13) ≤ blockRun 20 6 R (13 - 6) :=
  no_blockMethod_closure (by norm_num) (by norm_num) (by norm_num)

end Concrete

/-!
## 7. Measurement note (MEASURED, not theorems — recorded for the record)

All figures below come from an **independent** reimplementation of the corpus
definitions (`truncatedMersenneWeight s d = 4 ^ s / (2 ^ d - 1)`,
`seamSubsetTarget s = 2 ^ (2*s-1) - 2 ^ s`, the descending greedy over ranks
`2, …, s-1`), not from any Lean evaluation.  Counts and ranges are stated
explicitly; displayed decimal densities and ratios are summaries of those
finite computations.

### The maximal run of consecutive declines

Over rows `s ∈ [6, 800]` — `795` rows, `318795` ranks in total — the take/decline
pattern has `169884` declines, a density of `0.53289`.

The **global maximum run of consecutive declines is `9`**.  Counting every run
(a run may be terminated by a taken rank, or by the end of the row at rank
`s - 1`), the length histogram over all `795` rows is

    1: 32085   2: 17841   3: 12695   4: 5292   5: 2599
    6:  2587   7:   902   8:   679   9:  289

and restricted to runs actually closed by a taken rank

    1: 31897   2: 17748   3: 12641   4: 5268   5: 2588
    6:  2581   7:   894   8:   678   9:  288.

The first closed run of each length occurs at `(s, first rank)` equal to
`1:(9,7)`, `2:(7,4)`, `3:(74,67)`, `4:(27,22)`, `5:(21,15)`, `6:(20,8)`,
`7:(16,8)`, `8:(123,114)`, `9:(513,503)`.

**Finite long-row measurements.**  In the tested rows, the runs recur at fixed
ranks: the
length-`8` run begins at rank `114` and the length-`9` run at rank `503` at every
row long enough to contain them (checked: no row of `[122, 800]` lacks a run of
length `≥ 8`, and no row of `[512, 800]` lacks one of length `≥ 9`).  Running the
greedy of a single long row further, the maximum closed run is `9` (rank `503`)
at `s = 3000` and `12` (rank `5373`) at both `s = 6000` and `s = 12000`.
These observations show an increase from `9` to `12`; they prove neither
unboundedness nor a logarithmic asymptotic, and they provide no measured
constant bound valid beyond the tested rows.  Restricting to the late zone
`2*s < 3*d`, where the brief's
bit reading applies, the maximum over `[6, 800]` is again `9`, at `s = 512`,
ranks `503 … 511`; but at `s = 800` and `s = 3000` the longest runs (`9` at rank
`503`, `8` at rank `114`) lie *below* the first late rank, so the bit criterion
does not even apply to them.

### Finite prefix comparison

The take/decline word of row `800` agrees with that of row `3000` at every rank
`2 … 798`, differing only at the terminal rank `799`.  Over `s ∈ [6, 800]` there
are `454` interior disagreements with the row-`3000` word in total, and every one
of them is near the terminal rank.  These are exact finite MEASUREMENTS.  They
motivate comparison with the greedy expansion of `1/2` as a sum of distinct
`1/(2^d - 1)`, but this file proves neither stabilization to a universal word
nor an asymptotic explanation of run lengths.

### The invariant, re-scanned independently

Over `s ∈ [6, 800]`, `d ∈ [2, s-1]`:

* C6's ceiling `seamResidualUpto s d < 2 ^ (2*s-d)` fails at **exactly one**
  pair, `(13, 7)` — confirming `T1.not_residualInvariant` on an independent
  implementation.  There is no other failure in the range.
* T1's corrected ceiling `seamResidualUpto s d < truncatedMersenneWeight s d`
  has **no** failure in the range.
* `ρ s < 2 ^ (s+1)` at **every** row of `[6, 800]`; no exceedance.
* `T4`'s `hhigh` at the first late rank `d₀ = ⌊2*s/3⌋ + 1`, i.e.
  `seamResidualUpto s (d₀-1) < 2 ^ (2*s-d₀+1)`, holds at **every** row of
  `[6, 800]`; no failure.

### The repayment ratio

For `∑_{j=d+1}^{s-1} weightTail s j` against `weightTail s d`, over
`s ∈ [6, 120]` and every `d ∈ [2, s-2]`, the ratio never exceeds `0.333333`
(maximum attained at `(s, d) = (81, 53)`); the inequality
`3 * tail ≤ weightTail s d` holds with **no** violation in that range.  The
theorem `three_mul_weightTail_sum_le` proved above is the weaker
`3 * tail ≤ 2 * weightTail s d`, which is all the no-go needs — it already leaves
a permanent deficit of `weightTail s d / 3`.  The sharper `1/3` is MEASURED, not
proved.

Checked with `lake env lean ErdosProblems/Decl/D2.lean` (exit `0`, empty output).
-/

end ErdosProblems.Decl.D2
