/-
Copyright (c) 2026 Will Cook. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Will Cook
-/
import ErdosProblems.Bit.Corr1
import ErdosProblems.Bit.Corr2
import ErdosProblems.Skip.D2
import ErdosProblems.Skip.D3

/-!
# Bit R4: the contrapositive of `#257`, read off one number per row

`AngleD2.half_mem_iff_unboundedLargestSkipLate` turns the `1/2` question of
Erdős `#257` into `LargestSkipLateAt s` at cofinally many rows.  This file
attacks the *negative* branch: assume `LargestSkipLateAt` fails from some row
`S` on, and see what that forces.

The answer is a size law on a single, already-named scalar — the
concrete seam greedy defect

    `seamIntegerGreedyRemainder s = integerGreedyRemainder (seamWeights s) (seamSubsetTarget s)`.

## The mechanism

Row `s + 1` carries one rank that row `s` does not: the top rank `s`, whose
weight is exactly `truncatedMersenneWeight (s+1) s = 2 ^ (s+2) + 4`
(`topWeight_eq`).  That rank is *late* at row `s + 1` (`2*(s+1) < 3*s` for
`s ≥ 3`), and it is the last weight the descending greedy meets.  So whether
the greedy takes it is decided by one comparison, against the remainder
`topEntry s` entering that last step.

`Corr2.seamWeightsFrom_succ_row` writes the row-`s+1` weight word as
`liftedPrefix s ++ [truncatedMersenneWeight (s+1) s]`, where
`liftedPrefix s = liftWeights (seamWeights s) (rowCarriesFrom s 2)` quadruples
every row-`s` weight and adds its carry.  Feeding the row-`s` greedy word into
that prefix is admissible, so `integerGreedyBits_maximal` gives the whole
engine of this file in one line (`topEntry_le`):

    `topEntry s ≤ 4 * seamIntegerGreedyRemainder s + 2 ^ (s + 1)`.

## Main results

The implications listed here are kernel-proved.  Their conclusions must still
be read with their displayed hypotheses: the cofinal-dip hypotheses and the
eventual failure of `LargestSkipLateAt` are not proved in this file.

* `largestSkipLateAt_succ_of_remainder_le` — **the criterion.**  For `s ≥ 3`,

      `seamIntegerGreedyRemainder s ≤ 2 ^ (s - 1)  →  LargestSkipLateAt (s + 1)`.

  A pure *size* condition on row `s` produces the `#257` predicate at row
  `s + 1`, with no computation at row `s + 1` at all.  The threshold
  `2 ^ (s - 1)` is not half of the new top weight `2 ^ (s + 2) + 4`.
  Rather, after the factor-four lift and the target increment in `topEntry_le`,
  it makes the entering remainder too small to afford that top weight.  The
  top rank is therefore skipped, and a skipped late rank is a late largest
  false rank (`SkipD3.largestSkipLateAt_of_late_skip`).

* `remainder_succ_add_le_of_not_largestSkipLateAt` — **the descent.**  For
  `s ≥ 3`, if `LargestSkipLateAt (s+1)` fails then

      `seamIntegerGreedyRemainder (s+1) + 2 ^ (s+1) + 4 ≤ 4 * seamIntegerGreedyRemainder s`.

  The top rank *was* taken, so the row step loses its whole weight
  `2 ^ (s+2) + 4` against the target increment `2 ^ (s+1)`.  The displayed
  inequality is within one at the kernel-checked witness `s = 12`: its two
  sides are `23343` and `23344`.  This witness does not assert a global
  optimality result for the inequality.

* `remainder_ge_of_half_not_mem` — **the contrapositive law.**  If
  `1/2 ∉ mersenneAchievementSet` then there is `S` with

      `∀ s ≥ S,  2 ^ s + 2 ≤ seamIntegerGreedyRemainder s`.

  For the translated quantity
  `seamIntegerGreedyRemainder s - 2 ^ s`, the associated equality recurrence
  has rational fixed point `4/3`.  The largest integer offset below that point
  is `1`, which gives the proved cutoff `2 ^ s + 1`.  Under the hypothesis that
  `LargestSkipLateAt` keeps failing, a dip to that cutoff leads to an arithmetic
  contradiction after `s + 2` further descent steps.

* `half_mem_of_remainder_dips` / `half_mem_of_remainder_dips_strong` — the two
  positive criteria.  If `seamIntegerGreedyRemainder s ≤ 2 ^ (s-1)` at
  cofinally many `s` — or merely `≤ 2 ^ s + 1` at cofinally many `s` — then
  `(1/2 : ℝ) ∈ mersenneAchievementSet`.

## Where this leaves `#257`

The negative branch now says: **from some row on,
`2 ^ s + 2 ≤ seamIntegerGreedyRemainder s`.**  This follows conditionally from
`(1/2 : ℝ) ∉ mersenneAchievementSet`; that open hypothesis is not established
here.

The following are **MEASURED, not proved**.  An external arbitrary-precision
replication of `seamWeights`, `seamSubsetTarget` and `integerGreedyBits` was
reported over exactly `s ∈ [5, 800]`:

* `seamIntegerGreedyRemainder s ≤ 2 ^ (s-1)` at `193` of the `796` rows —
  `s = 7, 14, 21, 27, 35, 39, 42, 51, 53, 60, …, 786, 789, 793, 795, 797, 799`;
* `seamIntegerGreedyRemainder s ≤ 2 ^ s + 1` at `388` of the `796` rows.

These are finite counts only.  They neither prove equidistribution nor imply
that either kind of dip occurs cofinally.  The displayed sample includes dips
at `s = 797` and `s = 799`, near the top of the measured range.  The negative
branch would require the stronger dips
`seamIntegerGreedyRemainder s ≤ 2 ^ s + 1` to stop eventually.

## Which hypotheses are witnessed

Section 8 gives kernel-checked witnesses for the two local hypotheses:
`seamIntegerGreedyRemainder 7 = 3 ≤ 2 ^ 6` and
`seamIntegerGreedyRemainder 14 = 392 ≤ 2 ^ 13` feed the one-row criterion,
while `not_largestSkipLateAt_thirteen` feeds the one-row descent at `s = 12`.

It does **not** witness the eventual-failure hypothesis of
`remainder_ge_of_no_largestSkipLate`, either cofinal-dip hypothesis of
`half_mem_of_remainder_dips` or `half_mem_of_remainder_dips_strong`, or
`(1/2 : ℝ) ∉ mersenneAchievementSet` in `remainder_ge_of_half_not_mem`.
The finite theorem `Witness.dip_witness` covers only `N ≤ 14`; it is not a
cofinality result.  Thus the endpoint results remain proved implications whose
global hypotheses are open.
-/

namespace Erdos249257

namespace BitR4

open HalfCylinderIntegerGreedy
open ErdosProblems.BitCorr2

/-! ## 1. Boolean-sum plumbing -/

/-- A weighted subset sum splits along a concatenation, provided the bit word
is split at the matching place. -/
theorem weightedBoolSum_append (vs : List ℕ) (cs : List Bool) :
    ∀ (ws : List ℕ) (bs : List Bool), bs.length = ws.length →
      weightedBoolSum (ws ++ vs) (bs ++ cs) =
        weightedBoolSum ws bs + weightedBoolSum vs cs := by
  intro ws
  induction ws with
  | nil =>
      intro bs hb
      have hbnil : bs = [] := List.eq_nil_of_length_eq_zero (by simpa using hb)
      subst hbnil
      simp [weightedBoolSum]
  | cons w ws ih =>
      intro bs hb
      cases bs with
      | nil => simp at hb
      | cons b bs =>
          simp only [List.length_cons, Nat.succ.injEq] at hb
          cases b
          · simp only [List.cons_append, weightedBoolSum]
            exact ih bs hb
          · simp only [List.cons_append, weightedBoolSum]
            rw [ih bs hb, Nat.add_assoc]

/-- A prefix of a gap-dominating word is gap-dominating. -/
theorem gapDominates_of_append {gap : ℕ} (l₁ l₂ : List ℕ) :
    GapDominates gap (l₁ ++ l₂) → GapDominates gap l₁ := by
  induction l₁ with
  | nil => intro _; trivial
  | cons w ws ih =>
      intro h
      rw [List.cons_append, GapDominates] at h
      rw [GapDominates]
      have hs : ws.sum ≤ (ws ++ l₂).sum := by rw [List.sum_append]; omega
      exact ⟨by omega, ih h.2⟩

/-- The lift keeps the alignment length. -/
theorem liftWeights_length :
    ∀ (ws cs : List ℕ), cs.length = ws.length → (liftWeights ws cs).length = ws.length := by
  intro ws
  induction ws with
  | nil => intro cs _; simp [liftWeights]
  | cons w ws ih =>
      intro cs hc
      cases cs with
      | nil => simp at hc
      | cons c cs =>
          simp only [List.length_cons, Nat.succ.injEq] at hc
          have hlift : liftWeights (w :: ws) (c :: cs) = (4 * w + c) :: liftWeights ws cs := by
            simp [liftWeights]
          rw [hlift, List.length_cons, ih cs hc, List.length_cons]

/-- Selecting a bit word inside the lifted weights achieves at least four
times what it achieves inside the base weights. -/
theorem four_mul_weightedBoolSum_le_lift :
    ∀ (ws cs : List ℕ) (bs : List Bool), cs.length = ws.length →
      4 * weightedBoolSum ws bs ≤ weightedBoolSum (liftWeights ws cs) bs := by
  intro ws
  induction ws with
  | nil => intro cs bs _; simp [liftWeights, weightedBoolSum]
  | cons w ws ih =>
      intro cs bs hc
      cases cs with
      | nil => simp at hc
      | cons c cs =>
          simp only [List.length_cons, Nat.succ.injEq] at hc
          have hlift : liftWeights (w :: ws) (c :: cs) = (4 * w + c) :: liftWeights ws cs := by
            simp [liftWeights]
          cases bs with
          | nil => simp [hlift, weightedBoolSum]
          | cons b bs =>
              cases b
              · rw [hlift]
                simp only [weightedBoolSum]
                exact ih cs bs hc
              · rw [hlift]
                simp only [weightedBoolSum]
                have := ih cs bs hc
                omega

/-- …and at most four times that plus the whole carry budget. -/
theorem weightedBoolSum_lift_le :
    ∀ (ws cs : List ℕ) (bs : List Bool), cs.length = ws.length →
      weightedBoolSum (liftWeights ws cs) bs ≤ 4 * weightedBoolSum ws bs + cs.sum := by
  intro ws
  induction ws with
  | nil => intro cs bs _; simp [liftWeights, weightedBoolSum]
  | cons w ws ih =>
      intro cs bs hc
      cases cs with
      | nil => simp at hc
      | cons c cs =>
          simp only [List.length_cons, Nat.succ.injEq] at hc
          have hlift : liftWeights (w :: ws) (c :: cs) = (4 * w + c) :: liftWeights ws cs := by
            simp [liftWeights]
          cases bs with
          | nil => simp [hlift, weightedBoolSum]
          | cons b bs =>
              cases b
              · rw [hlift]
                simp only [weightedBoolSum, List.sum_cons]
                have := ih cs bs hc
                omega
              · rw [hlift]
                simp only [weightedBoolSum, List.sum_cons]
                have := ih cs bs hc
                omega

/-! ## 2. The top rank of row `s + 1` -/

/-- The brand-new top rank `s` of row `s + 1` carries weight `2 ^ (s+2) + 4`. -/
theorem topWeight_eq {s : ℕ} (hs : 3 ≤ s) :
    truncatedMersenneWeight (s + 1) s = 2 ^ (s + 2) + 4 := by
  have h := truncatedMersenneWeight_eq_twoPower_add_fourPower_of_lateRank
    (s := s + 1) (d := s) (by omega) (by omega) (by omega)
  rw [h, show 2 * (s + 1) - s = s + 2 by omega, show s + 1 - s = 1 by omega]
  norm_num

/-- The row-`s+1` weight word with its top rank removed: every row-`s` weight
quadrupled and given its carry. -/
def liftedPrefix (s : ℕ) : List ℕ := liftWeights (seamWeights s) (rowCarriesFrom s 2)

/-- The row-`s+1` greedy remainder on entering its top rank `s` — the single
number the last take/skip decision of row `s + 1` compares against. -/
def topEntry (s : ℕ) : ℕ :=
  integerGreedyRemainder (liftedPrefix s) (seamSubsetTarget (s + 1))

theorem seamWeights_succ_split {s : ℕ} (hs : 2 ≤ s) :
    seamWeights (s + 1) = liftedPrefix s ++ [truncatedMersenneWeight (s + 1) s] :=
  seamWeightsFrom_succ_row (le_refl 2) hs

theorem liftedPrefix_length (s : ℕ) : (liftedPrefix s).length = s - 2 := by
  have hc : (rowCarriesFrom s 2).length = (seamWeights s).length := by
    rw [rowCarriesFrom_length, seamWeights, seamWeightsFrom_length]
  rw [liftedPrefix, liftWeights_length _ _ hc, seamWeights, seamWeightsFrom_length]

/-! ## 3. The engine: the entering remainder is controlled by row `s` -/

/-- **The one inequality everything rests on.**  The remainder with which row
`s + 1` reaches its top rank is at most four times the row-`s` greedy defect
plus the exact target increment.  Proof: feeding the row-`s` greedy word into
the lifted prefix is admissible, and the greedy is maximal. -/
theorem topEntry_le {s : ℕ} (hs : 3 ≤ s) :
    topEntry s ≤ 4 * seamIntegerGreedyRemainder s + 2 ^ (s + 1) := by
  set Ws := seamWeights s with hWs
  set Ts := seamSubsetTarget s with hTs
  set bs := integerGreedyBits Ws Ts with hbs
  set Gs := weightedBoolSum Ws bs with hGs
  have hGle : Gs ≤ Ts := integerGreedyBits_admissible _ _
  have hrho : seamIntegerGreedyRemainder s = Ts - Gs := rfl
  have hlenWs : Ws.length = s - 2 := by rw [hWs, seamWeights, seamWeightsFrom_length]
  have hlenc : (rowCarriesFrom s 2).length = Ws.length := by
    rw [rowCarriesFrom_length, hlenWs]
  have hlenb : bs.length = Ws.length := integerGreedyBits_length _ _
  have hlenP : (liftedPrefix s).length = s - 2 := liftedPrefix_length s
  have hT' : seamSubsetTarget (s + 1) = 4 * Ts + 2 ^ (s + 1) :=
    HalfCylinderIntegerGreedy.seamSubsetTarget_succ (by omega)
  have hdomAll : GapDominates (2 ^ (s + 1 + 1)) (seamWeights (s + 1)) :=
    seamWeights_gapDominates (by omega)
  rw [seamWeights_succ_split (by omega)] at hdomAll
  have hdom : GapDominates (2 ^ (s + 1 + 1)) (liftedPrefix s) :=
    gapDominates_of_append _ _ hdomAll
  have hge : 4 * Gs ≤ weightedBoolSum (liftedPrefix s) bs :=
    four_mul_weightedBoolSum_le_lift _ _ _ hlenc
  have hub : weightedBoolSum (liftedPrefix s) bs ≤ 4 * Gs + (rowCarriesFrom s 2).sum :=
    weightedBoolSum_lift_le _ _ _ hlenc
  have hcarr : (rowCarriesFrom s 2).sum ≤ 2 * (s - 2) := rowCarriesFrom_sum_le s 2 (le_refl 2)
  have hlin : 2 * s + 4 < 2 ^ (s + 1) := two_mul_add_four_lt_two_pow_succ (by omega)
  have hadm : weightedBoolSum (liftedPrefix s) bs ≤ seamSubsetTarget (s + 1) := by
    have h := hT'
    omega
  have hlenbP : bs.length = (liftedPrefix s).length := by rw [hlenb, hlenWs, hlenP]
  have hmax := integerGreedyBits_maximal (gap := 2 ^ (s + 1 + 1))
    (by positivity) hdom hlenbP hadm
  have hGLle : weightedBoolSum (liftedPrefix s)
      (integerGreedyBits (liftedPrefix s) (seamSubsetTarget (s + 1))) ≤
        seamSubsetTarget (s + 1) := integerGreedyBits_admissible _ _
  have htop : topEntry s = seamSubsetTarget (s + 1) -
      weightedBoolSum (liftedPrefix s)
        (integerGreedyBits (liftedPrefix s) (seamSubsetTarget (s + 1))) := rfl
  rw [htop]
  omega

/-! ## 4. The last take/skip decision of row `s + 1` -/

theorem seamGreedyBits_succ_split {s : ℕ} (hs : 3 ≤ s) :
    integerGreedyBits (seamWeights (s + 1)) (seamSubsetTarget (s + 1)) =
      integerGreedyBits (liftedPrefix s) (seamSubsetTarget (s + 1)) ++
        integerGreedyBits [truncatedMersenneWeight (s + 1) s] (topEntry s) := by
  rw [seamWeights_succ_split (by omega), integerGreedyBits_append]
  rfl

/-- The top rank of row `s + 1` is selected exactly when the entering
remainder can pay for it. -/
theorem top_mem_iff {s : ℕ} (hs : 3 ≤ s) :
    s ∈ seamWordSupport (seamGreedyWord (s + 1)) ↔
      truncatedMersenneWeight (s + 1) s ≤ topEntry s := by
  have hlen : (integerGreedyBits (liftedPrefix s) (seamSubsetTarget (s + 1))).length = s - 2 := by
    rw [integerGreedyBits_length, liftedPrefix_length s]
  rw [BitCorr.mem_seamGreedySupport_iff_getElem (s := s + 1) (e := s) (by omega) (by omega),
    seamGreedyBits_succ_split hs,
    List.getElem?_append_right (le_of_eq hlen), hlen,
    show s - 2 - (s - 2) = 0 by omega]
  by_cases h : truncatedMersenneWeight (s + 1) s ≤ topEntry s
  · simp [integerGreedyBits, h]
  · simp [integerGreedyBits, h]

/-! ## 5. The two laws -/

/-- **The criterion.**  If the row-`s` greedy defect is at most
`2 ^ (s - 1)`, then the factor-four lift and target increment still leave row
`s + 1` unable to afford its top rank.  That rank — which is late — is skipped,
and `LargestSkipLateAt (s + 1)` holds.

No information about row `s + 1` is used beyond this one size comparison. -/
theorem largestSkipLateAt_succ_of_remainder_le {s : ℕ} (hs : 3 ≤ s)
    (h : seamIntegerGreedyRemainder s ≤ 2 ^ (s - 1)) :
    LargestSkipLateAt (s + 1) := by
  have hpow : 4 * 2 ^ (s - 1) = 2 ^ (s + 1) := by
    rw [show s + 1 = (s - 1) + 2 by omega, pow_add]; ring
  have hsplit : (2 : ℕ) ^ (s + 2) = 2 * 2 ^ (s + 1) := by
    rw [show s + 2 = (s + 1) + 1 by omega, pow_succ]; ring
  have hE := topEntry_le hs
  have hW := topWeight_eq hs
  refine SkipD3.largestSkipLateAt_of_late_skip (m := s) (by omega) (by omega) (by omega) ?_
  intro hmem
  have := (top_mem_iff hs).mp hmem
  rw [hW] at this
  omega

/-- Contrapositive shape: a row whose successor has no late largest false rank
must already carry a defect strictly above `2 ^ (s - 1)`. -/
theorem remainder_gt_of_not_largestSkipLateAt {s : ℕ} (hs : 3 ≤ s)
    (h : ¬ LargestSkipLateAt (s + 1)) :
    2 ^ (s - 1) < seamIntegerGreedyRemainder s := by
  by_contra hcon
  exact h (largestSkipLateAt_succ_of_remainder_le hs (by omega))

/-- **The descent.**  If row `s + 1` has no late largest false rank then it
took its top rank, and the row step therefore loses that rank's whole weight
`2 ^ (s+2) + 4` against the target increment `2 ^ (s+1)`. -/
theorem remainder_succ_add_le_of_not_largestSkipLateAt {s : ℕ} (hs : 3 ≤ s)
    (h : ¬ LargestSkipLateAt (s + 1)) :
    seamIntegerGreedyRemainder (s + 1) + 2 ^ (s + 1) + 4 ≤
      4 * seamIntegerGreedyRemainder s := by
  have hmem : s ∈ seamWordSupport (seamGreedyWord (s + 1)) :=
    AngleD2.mem_of_late_of_not_largestSkipLateAt h (by omega) (by omega) (by omega)
  have htake : truncatedMersenneWeight (s + 1) s ≤ topEntry s := (top_mem_iff hs).mp hmem
  have hword : integerGreedyBits [truncatedMersenneWeight (s + 1) s] (topEntry s) = [true] := by
    simp [integerGreedyBits, htake]
  have hlenP : (integerGreedyBits (liftedPrefix s) (seamSubsetTarget (s + 1))).length =
      (liftedPrefix s).length := integerGreedyBits_length _ _
  have hsum : weightedBoolSum (seamWeights (s + 1))
      (integerGreedyBits (seamWeights (s + 1)) (seamSubsetTarget (s + 1))) =
        weightedBoolSum (liftedPrefix s)
          (integerGreedyBits (liftedPrefix s) (seamSubsetTarget (s + 1))) +
          truncatedMersenneWeight (s + 1) s := by
    rw [seamGreedyBits_succ_split hs, seamWeights_succ_split (by omega), hword,
      weightedBoolSum_append _ _ _ _ hlenP]
    simp [weightedBoolSum]
  have hGLle : weightedBoolSum (liftedPrefix s)
      (integerGreedyBits (liftedPrefix s) (seamSubsetTarget (s + 1))) ≤
        seamSubsetTarget (s + 1) := integerGreedyBits_admissible _ _
  have htop : topEntry s = seamSubsetTarget (s + 1) -
      weightedBoolSum (liftedPrefix s)
        (integerGreedyBits (liftedPrefix s) (seamSubsetTarget (s + 1))) := rfl
  have hrem : seamIntegerGreedyRemainder (s + 1) = seamSubsetTarget (s + 1) -
      weightedBoolSum (seamWeights (s + 1))
        (integerGreedyBits (seamWeights (s + 1)) (seamSubsetTarget (s + 1))) := rfl
  have hE := topEntry_le hs
  have hW := topWeight_eq hs
  have hsplit : (2 : ℕ) ^ (s + 2) = 2 * 2 ^ (s + 1) := by
    rw [show s + 2 = (s + 1) + 1 by omega, pow_succ]; ring
  rw [hsum] at hrem
  omega

/-! ## 6. Iterating the descent: the contrapositive law -/

/-- The accumulated loss after `j` further descent steps: `cLoss j = (4^(j+1) - 4)/3`. -/
def cLoss : ℕ → ℕ
  | 0 => 0
  | j + 1 => 4 * cLoss j + 4

theorem three_mul_cLoss_add_four (j : ℕ) : 3 * cLoss j + 4 = 4 ^ (j + 1) := by
  induction j with
  | zero => norm_num [cLoss]
  | succ j ih =>
      have hp : (4 : ℕ) ^ (j + 1 + 1) = 4 * 4 ^ (j + 1) := by rw [pow_succ]; ring
      simp only [cLoss]
      omega

/-- Once the defect dips to `2 ^ s + 1` while `LargestSkipLateAt` is failing
everywhere above, the descent drives it down by a factor four per row against
a reference that only doubles. -/
theorem descent_iterate {S : ℕ} (hS : 3 ≤ S)
    (hno : ∀ t : ℕ, S ≤ t → ¬ LargestSkipLateAt t)
    {s : ℕ} (hs : S ≤ s) (hsmall : seamIntegerGreedyRemainder s ≤ 2 ^ s + 1) :
    ∀ j : ℕ, seamIntegerGreedyRemainder (s + 1 + j) + cLoss j ≤ 2 ^ (s + 1 + j) := by
  intro j
  induction j with
  | zero =>
      have hstep := remainder_succ_add_le_of_not_largestSkipLateAt
        (s := s) (by omega) (hno (s + 1) (by omega))
      have hp : (2 : ℕ) ^ (s + 1) = 2 * 2 ^ s := by rw [pow_succ]; ring
      simp only [cLoss, Nat.add_zero]
      omega
  | succ j ih =>
      have hstep := remainder_succ_add_le_of_not_largestSkipLateAt
        (s := s + 1 + j) (by omega) (hno (s + 1 + j + 1) (by omega))
      have hp : (2 : ℕ) ^ (s + 1 + j + 1) = 2 * 2 ^ (s + 1 + j) := by rw [pow_succ]; ring
      have hidx : s + 1 + (j + 1) = s + 1 + j + 1 := by omega
      rw [hidx]
      simp only [cLoss]
      omega

/-- **The contrapositive law.**  If `LargestSkipLateAt` fails from `S` on, then
from `S` on the greedy defect never drops below `2 ^ s + 2`. -/
theorem remainder_ge_of_no_largestSkipLate {S : ℕ} (hS : 3 ≤ S)
    (hno : ∀ t : ℕ, S ≤ t → ¬ LargestSkipLateAt t)
    {s : ℕ} (hs : S ≤ s) : 2 ^ s + 2 ≤ seamIntegerGreedyRemainder s := by
  by_contra hcon
  have hsmall : seamIntegerGreedyRemainder s ≤ 2 ^ s + 1 := by omega
  have hd := descent_iterate hS hno hs hsmall (s + 2)
  have hc := three_mul_cLoss_add_four (s + 2)
  have h4 : (4 : ℕ) ^ (s + 3) = 2 ^ (2 * s + 6) := by
    rw [show (4 : ℕ) = 2 ^ 2 by norm_num, ← pow_mul, show 2 * (s + 3) = 2 * s + 6 by omega]
  have hidx : s + 1 + (s + 2) = 2 * s + 3 := by omega
  have hsplit : (2 : ℕ) ^ (2 * s + 6) = 8 * 2 ^ (2 * s + 3) := by
    rw [show 2 * s + 6 = (2 * s + 3) + 3 by omega, pow_add]
    ring
  have hbig : (8 : ℕ) ≤ 2 ^ (2 * s + 3) := by
    calc (8 : ℕ) = 2 ^ 3 := by norm_num
    _ ≤ 2 ^ (2 * s + 3) := Nat.pow_le_pow_right (by norm_num) (by omega)
  rw [hidx] at hd
  rw [show s + 2 + 1 = s + 3 by omega] at hc
  omega

/-! ## 7. The `#257` criteria -/

/-- **Criterion, plain form.**  If the concrete seam greedy defect is at most
`2 ^ (s - 1)` at cofinally many rows, then `1/2` is achieved. -/
theorem half_mem_of_remainder_dips
    (h : ∀ N : ℕ, ∃ s : ℕ, N ≤ s ∧ seamIntegerGreedyRemainder s ≤ 2 ^ (s - 1)) :
    (1 / 2 : ℝ) ∈ mersenneAchievementSet := by
  rw [AngleD2.half_mem_iff_unboundedLargestSkipLate]
  intro N
  obtain ⟨s, hs, hsmall⟩ := h (max N 3)
  have hN : N ≤ s := le_trans (le_max_left _ _) hs
  have h3 : 3 ≤ s := le_trans (le_max_right _ _) hs
  exact ⟨s + 1, by omega, largestSkipLateAt_succ_of_remainder_le h3 hsmall⟩

/-- **Criterion, sharpened by the descent.**  The threshold can be raised from
`2 ^ (s-1)` to `2 ^ s + 1`, the integer cutoff below the descent recurrence's
rational fixed-point offset `4/3`. -/
theorem half_mem_of_remainder_dips_strong
    (h : ∀ N : ℕ, ∃ s : ℕ, N ≤ s ∧ seamIntegerGreedyRemainder s ≤ 2 ^ s + 1) :
    (1 / 2 : ℝ) ∈ mersenneAchievementSet := by
  by_contra hcon
  have hnu : ¬ AngleD2.UnboundedLargestSkipLate := fun hu =>
    hcon (AngleD2.half_mem_of_unboundedLargestSkipLate hu)
  unfold AngleD2.UnboundedLargestSkipLate at hnu
  push Not at hnu
  obtain ⟨N, hN⟩ := hnu
  have hno : ∀ t : ℕ, max N 3 ≤ t → ¬ LargestSkipLateAt t := fun t ht =>
    hN t (le_trans (le_max_left _ _) ht)
  obtain ⟨s, hs, hsmall⟩ := h (max N 3)
  have := remainder_ge_of_no_largestSkipLate (S := max N 3) (le_max_right _ _) hno hs
  omega

/-- **The contrapositive law, in `#257` vocabulary.**  Failure of half
membership forces the greedy defect above `2 ^ s` from some row on. -/
theorem remainder_ge_of_half_not_mem (h : (1 / 2 : ℝ) ∉ mersenneAchievementSet) :
    ∃ S : ℕ, ∀ s : ℕ, S ≤ s → 2 ^ s + 2 ≤ seamIntegerGreedyRemainder s := by
  have hnu : ¬ AngleD2.UnboundedLargestSkipLate := fun hu =>
    h (AngleD2.half_mem_of_unboundedLargestSkipLate hu)
  unfold AngleD2.UnboundedLargestSkipLate at hnu
  push Not at hnu
  obtain ⟨N, hN⟩ := hnu
  refine ⟨max N 3, fun s hs => ?_⟩
  exact remainder_ge_of_no_largestSkipLate (S := max N 3) (le_max_right _ _)
    (fun t ht => hN t (le_trans (le_max_left _ _) ht)) hs

/-! ## 8. Kernel-checked finite witnesses for the local hypotheses -/

namespace Witness

/-- The greedy defect through `SkipD3`'s kernel-computable row word. -/
theorem seamIntegerGreedyRemainder_eq_wgt (s : ℕ) :
    seamIntegerGreedyRemainder s =
      seamSubsetTarget s - weightedBoolSum (SkipD3.wgt s 2 (s - 2)) (SkipD3.gb s) := by
  rw [seamIntegerGreedyRemainder, integerGreedyRemainder, SkipD3.seamWeights_eq_wgt, SkipD3.gb]

set_option maxRecDepth 100000 in
theorem seamIntegerGreedyRemainder_seven : seamIntegerGreedyRemainder 7 = 3 := by
  rw [seamIntegerGreedyRemainder_eq_wgt]
  decide +kernel

set_option maxRecDepth 100000 in
theorem seamIntegerGreedyRemainder_twelve : seamIntegerGreedyRemainder 12 = 5836 := by
  rw [seamIntegerGreedyRemainder_eq_wgt]
  decide +kernel

set_option maxRecDepth 100000 in
theorem seamIntegerGreedyRemainder_thirteen : seamIntegerGreedyRemainder 13 = 15147 := by
  rw [seamIntegerGreedyRemainder_eq_wgt]
  decide +kernel

/-- **The criterion's hypothesis is satisfied**, at `s = 7`: `3 ≤ 2 ^ 6`. -/
theorem criterion_hypothesis_seven : seamIntegerGreedyRemainder 7 ≤ 2 ^ (7 - 1) := by
  rw [seamIntegerGreedyRemainder_seven]; norm_num

/-- …and the criterion then delivers the `#257` predicate at row `8`, from the
size of row `7`'s defect alone. -/
theorem largestSkipLateAt_eight : LargestSkipLateAt 8 :=
  largestSkipLateAt_succ_of_remainder_le (s := 7) (by norm_num) criterion_hypothesis_seven

/-- **The criterion's hypothesis at `Corr2`'s own row.**  `Corr2` computes
`seamIntegerGreedyRemainder 14 = 392`, and `392 ≤ 2 ^ 13`. -/
theorem criterion_hypothesis_fourteen : seamIntegerGreedyRemainder 14 ≤ 2 ^ (14 - 1) := by
  rw [ErdosProblems.BitCorr2.seamIntegerGreedyRemainder_14]; norm_num

theorem largestSkipLateAt_fifteen : LargestSkipLateAt 15 :=
  largestSkipLateAt_succ_of_remainder_le (s := 14) (by norm_num) criterion_hypothesis_fourteen

/-- The criterion is a genuine condition, not automatic: at `s = 15` the
defect `34333` exceeds `2 ^ 14 = 16384`, so the criterion is silent there. -/
theorem criterion_fails_fifteen : ¬ (seamIntegerGreedyRemainder 15 ≤ 2 ^ (15 - 1)) := by
  rw [ErdosProblems.BitCorr2.seamIntegerGreedyRemainder_15]; norm_num

set_option maxRecDepth 100000 in
/-- **The descent's hypothesis is satisfied**, at row `12`: every late rank of
row `12` (that is, `9, 10, 11`) is selected, so row `12` has no late largest
false rank. -/
theorem not_largestSkipLateAt_twelve : ¬ LargestSkipLateAt 12 := by
  rintro ⟨d, ⟨hd2, hds, hdnot, -⟩, hlate⟩
  have h9 : 9 ≤ d := by omega
  refine hdnot ?_
  rw [SkipD3.mem_support_iff hd2 hds]
  interval_cases d <;> decide +kernel

set_option maxRecDepth 100000 in
/-- The same at row `13`: the late ranks `9, 10, 11, 12` are all selected. -/
theorem not_largestSkipLateAt_thirteen : ¬ LargestSkipLateAt 13 := by
  rintro ⟨d, ⟨hd2, hds, hdnot, -⟩, hlate⟩
  have h9 : 9 ≤ d := by omega
  refine hdnot ?_
  rw [SkipD3.mem_support_iff hd2 hds]
  interval_cases d <;> decide +kernel

/-- The descent instantiated at `s = 12`. -/
theorem descent_twelve :
    seamIntegerGreedyRemainder 13 + 2 ^ 13 + 4 ≤ 4 * seamIntegerGreedyRemainder 12 :=
  remainder_succ_add_le_of_not_largestSkipLateAt (s := 12) (by norm_num)
    not_largestSkipLateAt_thirteen

/-- At `s = 12` the descent inequality is within one: its two sides are
`23343` and `23344`.  This is a concrete tightness witness, not a theorem that
the constants are globally optimal. -/
theorem descent_twelve_defect :
    4 * seamIntegerGreedyRemainder 12 - (seamIntegerGreedyRemainder 13 + 2 ^ 13 + 4) = 1 := by
  rw [seamIntegerGreedyRemainder_twelve, seamIntegerGreedyRemainder_thirteen]
  norm_num

/-- The contrapositive of the criterion instantiated at `s = 12`: row `13`'s
failure forces row `12`'s defect above `2 ^ 11`.  The kernel-checked values are
`5836 > 2048`. -/
theorem remainder_gt_twelve : 2 ^ (12 - 1) < seamIntegerGreedyRemainder 12 :=
  remainder_gt_of_not_largestSkipLateAt (s := 12) (by norm_num) not_largestSkipLateAt_thirteen

/-- The body of `half_mem_of_remainder_dips` is satisfied at every `N ≤ 14`.
This is a finite near-end witness only; it does not establish the theorem's
cofinality hypothesis. -/
theorem dip_witness {N : ℕ} (hN : N ≤ 14) :
    ∃ s : ℕ, N ≤ s ∧ seamIntegerGreedyRemainder s ≤ 2 ^ (s - 1) :=
  ⟨14, hN, criterion_hypothesis_fourteen⟩

end Witness

/-
## Axiom audit

Every theorem above was checked with `#print axioms`; each depends only on
`[propext, Classical.choice, Quot.sound]`.  The `#print` lines are left
commented so that `lake env lean ErdosProblems/Bit/R4.lean` produces exit `0`
with empty output; uncomment to reproduce the audit.

-- #print axioms topEntry_le
-- #print axioms top_mem_iff
-- #print axioms largestSkipLateAt_succ_of_remainder_le
-- #print axioms remainder_succ_add_le_of_not_largestSkipLateAt
-- #print axioms remainder_ge_of_no_largestSkipLate
-- #print axioms half_mem_of_remainder_dips
-- #print axioms half_mem_of_remainder_dips_strong
-- #print axioms remainder_ge_of_half_not_mem
-- #print axioms Witness.largestSkipLateAt_eight
-- #print axioms Witness.largestSkipLateAt_fifteen
-- #print axioms Witness.not_largestSkipLateAt_twelve
-- #print axioms Witness.descent_twelve
-/

end BitR4

end Erdos249257
