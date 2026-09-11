/-
Copyright (c) 2026 Will Cook. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Will Cook
-/
import ErdosProblems.Bit.Corr2
import ErdosProblems.Skip.D2
import ErdosProblems.Skip.D3

/-!
# Bit R3: conditional remainder criteria for a late skip

`AngleD2.half_mem_iff_unboundedLargestSkipLate` reduces Erdős `#257`'s `1/2`
question to `LargestSkipLateAt s` at cofinally many rows, and
`SkipD3.largestSkipLateAt_of_late_skip` says a *single* skipped late rank at row
`s` suffices.  This file proves sufficient remainder conditions for such rows,
an escape theorem that locates one such row in a finite interval, and explicit
finite witnesses.  It does not prove that either condition holds cofinally.

## The mechanism

Rank `s` is brand new at row `s + 1`: it is the last entry of
`seamWeights (s+1)`, it is worth exactly `2 ^ (s+2) + 4`
(`truncatedMersenneWeight_succ_top`), and it is *late* there
(`2 * (s+1) < 3 * s` for `s ≥ 3`).  So if the row-`s+1` greedy declines it, the
row is done.

`BitCorr2.seamWeightsFrom_succ_row` writes row `s+1`'s weight word as the lift
`w ↦ 4 * w + rowCarry s d` of row `s`'s, with rank `s` appended.  Feeding the
row-`s` greedy support into that lift is admissible, and the lifted prefix
greedy is *maximal* (`integerGreedyBits_maximal`, via
`seamWeights_gapDominates`), so the capacity that survives to reach rank `s`
obeys

    `topRemainder_le` :  topRemainder s + carryTaken s
                            ≤ 4 * seamIntegerGreedyRemainder s + 2 ^ (s+1).

Since the new rank costs `2 ^ (s+2) + 4 = 2 * 2 ^ (s+1) + 4`, the proof splits
on one inequality; both cases use the same carry term `carryTaken s`:

* `topRank_notMem_support` / `largestSkipLateAt_succ_of_small_remainder` —
  if `4 * r s < 2 ^ (s+1) + 4 + carryTaken s` the new rank is skipped, so
  `LargestSkipLateAt (s+1)`.  In particular
  **`4 * seamIntegerGreedyRemainder s ≤ 2 ^ (s+1)` implies
  `LargestSkipLateAt (s+1)`** — unconditional, every `s ≥ 3`.
* `remainder_succ_le_of_large` — otherwise the row-`s` support *extended by the
  new rank* is admissible at row `s+1`, and maximality forces
  `r (s+1) + 2 ^ (s+1) + 4 + carryTaken s ≤ 4 * r s`.

`dichotomy` packages these two implications.  Its conclusions are not
exclusive: `LargestSkipLateAt (s+1)` can hold because a lower late rank is
skipped even when the brand-new top rank is selected.  Thus the dichotomy is
not an equivalence or a classification of all rows satisfying
`LargestSkipLateAt`.

## The escape window

Write `e s = 2 ^ s - r s` for the deficit.  The second branch says
`e (s+1) ≥ 4 * e s + 4`: **the deficit quadruples at every row that fails to buy
a skip**, while `r ≥ 0` caps it at `2 ^ s`.  A positive deficit therefore cannot
survive many rows:

* `exists_largestSkipLateAt_of_deficit` — if `r s + 2 ^ j ≤ 2 ^ s` (`j ≤ s`)
  then `LargestSkipLateAt t` for some `t` in `[s+1, 2s-j+1]`;
* `exists_largestSkipLateAt_of_remainder_lt` — the case `j = 0`: `r s < 2 ^ s`
  forces a late skip inside `[s+1, 2s+1]`;
* `half_mem_of_remainder_lt_cofinally` — **hence
  `(1/2 : ℝ) ∈ mersenneAchievementSet` follows from the single inequality
  `seamIntegerGreedyRemainder s < 2 ^ s` holding infinitely often**;
* `remainder_ge_of_half_notMem` — contrapositive: if `1/2` is missed then from
  some row on `2 ^ s ≤ seamIntegerGreedyRemainder s`, forever.

These are one-sided sufficient conditions on the already-defined remainder.
A successful deficit estimate at row `s` proves the existence of at least one
late skip in the stated finite window; it does not certify every row in that
window.  Later, `RemC1.rowLaw_blind_at_16` proves that the top-rank row
recurrence used here can miss a row whose skipped late rank is lower than the
top rank.

## Non-vacuity

**PROVED:** `rem` is a kernel-computable form of
`seamIntegerGreedyRemainder`
(`rem_eq`), through `SkipD3.wgt` / `SkipD3.gb`.  The criterion is exhibited
firing, by `decide +kernel`, at

    s = 14, 21, 35, 100, 1200, 3001, 8000, 12002

giving `LargestSkipLateAt` at rows `15, 22, 36, 101, 1201, 3002, 8001, 12003`.
Row `1201` is the first row past `BitCorr3`'s certified block `[501, 1200]`, and
row `12003` is another finite witness.  `escape_witness_20` exhibits the escape
theorem doing work beyond the immediate criterion: at `s = 20` the criterion
does *not* fire (`4 * r 20 = 2197412 > 2 ^ 21`) yet the deficit
`2 ^ 20 - 549353` exceeds `2 ^ 18`, so a skip is forced in `[21, 23]`.
`remainder_lt_witness` proves the required existential statement for every
finite bound `N ≤ 12002`, using the witness row `12002`.

**Cofinality is exactly what is not proved.**  Outside the kernel, an
arbitrary-precision replication of `seamWeights` / `seamSubsetTarget` /
`integerGreedyBits` (faithful: it reproduces `H4`'s `d₀(81) = 75` and `H3`'s
"`LargestSkipLateAt` at every `s ∈ [5,400]` except `5, 11, 12, 13`") finds
`r s < 2 ^ s` at **86** of the 195 rows `s ∈ [5, 199]` and the stronger criterion
`4 * r s ≤ 2 ^ (s+1)` at **42** of them.
These counts are **MEASURED, NOT PROVED**.  The individually named rows above
are kernel-checked; no infinite family is established here.

## Calibration counterexamples

* `criterion_not_necessary` — at `s = 19` the transfer bound is far too weak
  (`4 * r 19 = 3697820` against `2 ^ 20 = 1048576`) and yet rank `19` really is
  skipped at row `20`.  This proves that the stated sufficient criterion is not
  necessary; it does not identify all possible strengthenings of the bound.
* `lateSkip_does_not_give_escape` — row `19` *has* a late largest false rank
  (`d = 14`, `2 * 19 = 38 < 42 = 3 * 14`) while `r 19 = 924455 ≥ 2 ^ 19`.  So a
  late skip at row `s` does **not** feed the escape hypothesis at row `s`, and
  the two conditions cannot be chained into an induction.

  `gap_is_two_pow_succ` records the available
  `GapDominates (2 ^ (s+1)) (seamWeights s)` estimate.  It does not assert that
  this parameter is optimal or rule out every stronger auxiliary invariant.
-/

namespace ErdosProblems

namespace BitR3

open Erdos249257
open Erdos249257.HalfCylinderIntegerGreedy
open ErdosProblems.BitCorr2

/-! ## 1. Elementary `weightedBoolSum` and `GapDominates` plumbing -/

/-- Appending one weight and one bit adds exactly that weight when the bit is
set.  The length hypothesis keeps the two lists aligned. -/
theorem weightedBoolSum_append_singleton :
    ∀ (l : List ℕ) (bs : List Bool), bs.length = l.length → ∀ (x : ℕ) (b : Bool),
      weightedBoolSum (l ++ [x]) (bs ++ [b]) =
        weightedBoolSum l bs + (if b then x else 0) := by
  intro l
  induction l with
  | nil =>
      intro bs hlen x b
      have : bs = [] := List.eq_nil_of_length_eq_zero (by simpa using hlen)
      subst this
      cases b <;> simp [weightedBoolSum]
  | cons w ws ih =>
      intro bs hlen x b
      cases bs with
      | nil => simp at hlen
      | cons c cs =>
          simp only [List.length_cons, Nat.succ.injEq] at hlen
          have hrec := ih cs hlen x b
          cases c
          · simpa only [List.cons_append, weightedBoolSum] using hrec
          · simp only [List.cons_append, weightedBoolSum]
            omega

/-- A prefix of a gap-dominating word is gap-dominating. -/
theorem gapDominates_of_append {gap : ℕ} :
    ∀ (l₁ l₂ : List ℕ), GapDominates gap (l₁ ++ l₂) → GapDominates gap l₁ := by
  intro l₁
  induction l₁ with
  | nil => intro l₂ _; trivial
  | cons w ws ih =>
      intro l₂ h
      rw [List.cons_append, GapDominates] at h
      refine ⟨?_, ih l₂ h.2⟩
      have : ws.sum ≤ (ws ++ l₂).sum := by
        rw [List.sum_append]; omega
      omega

/-- The descending greedy on a one-element word. -/
theorem integerGreedyBits_singleton (x C : ℕ) :
    integerGreedyBits [x] C = [decide (x ≤ C)] := by
  rw [integerGreedyBits]
  by_cases h : x ≤ C <;> simp [h, integerGreedyBits]

/-! ## 2. The exact row-step subset sum -/

/-- **The lifted subset sum, exactly.**  Selecting the same ranks at row `s + 1`
as at row `s`, and choosing `b` at the brand-new rank `s`, multiplies the row-`s`
subset sum by four and adds the carries actually collected — no slack. -/
theorem weightedBoolSum_succ_row (s : ℕ) :
    ∀ (d : ℕ), 2 ≤ d → d ≤ s → ∀ (bs : List Bool), bs.length = s - d → ∀ (b : Bool),
      weightedBoolSum (seamWeightsFrom (s + 1) d) (bs ++ [b]) =
        4 * weightedBoolSum (seamWeightsFrom s d) bs
          + weightedBoolSum (rowCarriesFrom s d) bs
          + (if b then truncatedMersenneWeight (s + 1) s else 0) := by
  intro d hd hds bs hlen b
  by_cases h : d < s
  · rw [seamWeightsFrom_eq_cons (show d < s + 1 by omega),
      seamWeightsFrom_eq_cons h, rowCarriesFrom_eq_cons h]
    cases bs with
    | nil => simp only [List.length_nil] at hlen; omega
    | cons c cs =>
        simp only [List.length_cons] at hlen
        have hrec := weightedBoolSum_succ_row s (d + 1) (by omega) (by omega) cs
          (by omega) b
        have hw := truncatedMersenneWeight_succ_row (s := s) (d := d) hd
        cases c
        · simpa only [List.cons_append, weightedBoolSum] using hrec
        · simp only [List.cons_append, weightedBoolSum]
          rw [hw, hrec]
          ring
  · have hde : d = s := by omega
    subst hde
    have hbs : bs = [] := List.eq_nil_of_length_eq_zero (by simpa using hlen)
    subst hbs
    rw [seamWeightsFrom_eq_nil (le_refl d), rowCarriesFrom_eq_nil (le_refl d),
      seamWeightsFrom_eq_cons (show d < d + 1 by omega),
      seamWeightsFrom_eq_nil (le_refl (d + 1))]
    cases b <;> simp [weightedBoolSum]
termination_by d => s - d
decreasing_by omega

theorem weightedBoolSum_succ_row_true {s : ℕ} (hs : 2 ≤ s) (bs : List Bool)
    (hlen : bs.length = s - 2) :
    weightedBoolSum (seamWeights (s + 1)) (bs ++ [true]) =
      4 * weightedBoolSum (seamWeights s) bs
        + weightedBoolSum (rowCarriesFrom s 2) bs
        + truncatedMersenneWeight (s + 1) s := by
  rw [show seamWeights (s + 1) = seamWeightsFrom (s + 1) 2 from rfl,
    show seamWeights s = seamWeightsFrom s 2 from rfl]
  simpa using weightedBoolSum_succ_row s 2 (le_refl 2) hs bs hlen true

theorem weightedBoolSum_succ_row_false {s : ℕ} (hs : 2 ≤ s) (bs : List Bool)
    (hlen : bs.length = s - 2) :
    weightedBoolSum (seamWeights (s + 1)) (bs ++ [false]) =
      4 * weightedBoolSum (seamWeights s) bs
        + weightedBoolSum (rowCarriesFrom s 2) bs := by
  rw [show seamWeights (s + 1) = seamWeightsFrom (s + 1) 2 from rfl,
    show seamWeights s = seamWeightsFrom s 2 from rfl]
  simpa using weightedBoolSum_succ_row s 2 (le_refl 2) hs bs hlen false

/-! ## 3. The brand-new rank, and the row-`s` data -/

/-- **The brand-new rank is worth exactly `2 ^ (s+2) + 4`.**  Rank `s` appears
for the first time at row `s + 1`, where `⌊2 * (s+1) / s⌋ = 2`. -/
theorem truncatedMersenneWeight_succ_top {s : ℕ} (hs : 3 ≤ s) :
    truncatedMersenneWeight (s + 1) s = 2 ^ (s + 2) + 4 := by
  have hq : (2 * (s + 1)) / s = 2 :=
    Nat.div_eq_of_lt_le (by omega) (by omega)
  rw [truncatedMersenneWeight_eq_descendingMultiples (by omega), hq,
    Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_zero,
    show 2 * (s + 1) - s * (0 + 1) = s + 2 by omega,
    show 2 * (s + 1) - s * (1 + 1) = 2 by omega]
  norm_num

/-- The concrete row-`s` greedy take/skip word. -/
def greedyWord (s : ℕ) : List Bool :=
  integerGreedyBits (seamWeights s) (seamSubsetTarget s)

/-- The subset sum the row-`s` greedy actually achieves. -/
def greedySum (s : ℕ) : ℕ := weightedBoolSum (seamWeights s) (greedyWord s)

/-- The carry the row-`s` greedy support actually collects on the step
`s ↦ s + 1`.  Every summand is `rowCarry s d ≤ 2`, and only ranks dividing
`2*s+1` or `2*s+2` contribute at all. -/
def carryTaken (s : ℕ) : ℕ := weightedBoolSum (rowCarriesFrom s 2) (greedyWord s)

theorem greedyWord_length (s : ℕ) : (greedyWord s).length = s - 2 := by
  rw [greedyWord, integerGreedyBits_length, seamWeights_length_eq]

theorem greedySum_add_remainder (s : ℕ) :
    greedySum s + seamIntegerGreedyRemainder s = seamSubsetTarget s := by
  have h := integerGreedyBits_admissible (seamWeights s) (seamSubsetTarget s)
  simp only [greedySum, greedyWord, seamIntegerGreedyRemainder,
    integerGreedyRemainder]
  omega

theorem carryTaken_le (s : ℕ) : carryTaken s ≤ 2 * (s - 2) :=
  le_trans (weightedBoolSum_le_sum _ _) (rowCarriesFrom_sum_le s 2 (le_refl 2))

/-- The row-`s+1` weight word without its brand-new last rank. -/
def liftedPrefix (s : ℕ) : List ℕ :=
  liftWeights (seamWeightsFrom s 2) (rowCarriesFrom s 2)

theorem liftedPrefix_length (s : ℕ) : (liftedPrefix s).length = s - 2 := by
  simp [liftedPrefix, liftWeights, seamWeightsFrom_length, rowCarriesFrom_length]

theorem seamWeights_succ_split {s : ℕ} (hs : 2 ≤ s) :
    seamWeights (s + 1) = liftedPrefix s ++ [truncatedMersenneWeight (s + 1) s] := by
  show seamWeightsFrom (s + 1) 2 = _
  rw [seamWeightsFrom_succ_row (le_refl 2) hs]
  rfl

/-- The row-`s` greedy support, read inside row `s + 1` with the new rank
declined, has subset sum exactly `4 * greedySum s + carryTaken s`. -/
theorem weightedBoolSum_liftedPrefix (s : ℕ) (hs : 2 ≤ s) :
    weightedBoolSum (liftedPrefix s) (greedyWord s) =
      4 * greedySum s + carryTaken s := by
  have hlen : (greedyWord s).length = (liftedPrefix s).length := by
    rw [greedyWord_length, liftedPrefix_length]
  have h1 := weightedBoolSum_append_singleton (liftedPrefix s) (greedyWord s) hlen
    (truncatedMersenneWeight (s + 1) s) false
  have h2 := weightedBoolSum_succ_row_false hs (greedyWord s) (greedyWord_length s)
  rw [← seamWeights_succ_split hs] at h1
  simp only [if_neg (by decide : ¬ (false = true))] at h1
  simp only [greedySum, carryTaken]
  omega

/-! ## 4. The one bound that does all the work

`liftedPrefix s` is a prefix of the row-`s+1` weight word, so the descending
greedy on it is *maximal* (`integerGreedyBits_maximal`).  Feeding it the row-`s`
greedy support — an admissible word — bounds the remainder that reaches the
brand-new rank `s`. -/

/-- The row-`s+1` greedy achieves at least the lift of the row-`s` greedy. -/
theorem prefixSum_lower_bound {s : ℕ} (hs : 3 ≤ s) :
    4 * greedySum s + carryTaken s ≤
      weightedBoolSum (liftedPrefix s)
        (integerGreedyBits (liftedPrefix s) (seamSubsetTarget (s + 1))) := by
  have hT : seamSubsetTarget (s + 1) = 4 * seamSubsetTarget s + 2 ^ (s + 1) :=
    ErdosProblems.BitCorr2.seamSubsetTarget_succ (by omega)
  have hlin : 2 * s + 4 < 2 ^ (s + 1) := two_mul_add_four_lt_two_pow_succ (by omega)
  have hGR := greedySum_add_remainder s
  have hC := carryTaken_le s
  have hdom : GapDominates (2 ^ (s + 1 + 1)) (liftedPrefix s) := by
    refine gapDominates_of_append _ [truncatedMersenneWeight (s + 1) s] ?_
    rw [← seamWeights_succ_split (by omega)]
    exact seamWeights_gapDominates (by omega)
  have hlen : (greedyWord s).length = (liftedPrefix s).length := by
    rw [greedyWord_length, liftedPrefix_length]
  have hval := weightedBoolSum_liftedPrefix s (by omega)
  have hadm : weightedBoolSum (liftedPrefix s) (greedyWord s) ≤
      seamSubsetTarget (s + 1) := by rw [hval]; omega
  have := integerGreedyBits_maximal (gap := 2 ^ (s + 1 + 1)) (by positivity)
    hdom hlen hadm
  omega

/-- The capacity that actually reaches the brand-new rank `s` at row `s + 1`. -/
def topRemainder (s : ℕ) : ℕ :=
  seamSubsetTarget (s + 1) -
    weightedBoolSum (liftedPrefix s)
      (integerGreedyBits (liftedPrefix s) (seamSubsetTarget (s + 1)))

/-- **The transfer bound.**  What reaches the brand-new rank is at most four
times the row-`s` remainder plus the target increment, less the carries. -/
theorem topRemainder_le {s : ℕ} (hs : 3 ≤ s) :
    topRemainder s + carryTaken s ≤
      4 * seamIntegerGreedyRemainder s + 2 ^ (s + 1) := by
  have hT : seamSubsetTarget (s + 1) = 4 * seamSubsetTarget s + 2 ^ (s + 1) :=
    ErdosProblems.BitCorr2.seamSubsetTarget_succ (by omega)
  have hGR := greedySum_add_remainder s
  have hlow := prefixSum_lower_bound hs
  have hC := carryTaken_le s
  have hlin : 2 * s + 4 < 2 ^ (s + 1) := two_mul_add_four_lt_two_pow_succ (by omega)
  simp only [topRemainder]
  omega

/-- Row `s+1`'s greedy word, split at the brand-new rank. -/
theorem greedyWord_succ_split {s : ℕ} (hs : 2 ≤ s) :
    greedyWord (s + 1) =
      integerGreedyBits (liftedPrefix s) (seamSubsetTarget (s + 1)) ++
        [decide (truncatedMersenneWeight (s + 1) s ≤ topRemainder s)] := by
  rw [greedyWord, seamWeights_succ_split hs,
    ErdosProblems.BitCorr2.integerGreedyBits_append, integerGreedyBits_singleton]
  rfl

theorem getD_append_singleton (p : List Bool) (b : Bool) :
    (p ++ [b]).getD p.length false = b := by
  induction p with
  | nil => simp
  | cons a as _ => simp

/-! ## 5. The criterion: a small remainder forces the top rank to be skipped -/

/-- **The criterion.**  If the row-`s` greedy remainder is small, the brand-new
rank `s` is skipped at row `s + 1`. -/
theorem topRank_notMem_support {s : ℕ} (hs : 3 ≤ s)
    (h : 4 * seamIntegerGreedyRemainder s < 2 ^ (s + 1) + 4 + carryTaken s) :
    s ∉ seamWordSupport (seamGreedyWord (s + 1)) := by
  have hpow : (2 : ℕ) ^ (s + 2) = 2 * 2 ^ (s + 1) := by rw [pow_succ]; ring
  have hlt : topRemainder s < truncatedMersenneWeight (s + 1) s := by
    rw [truncatedMersenneWeight_succ_top hs]
    have := topRemainder_le hs
    omega
  have hbit : (SkipD3.gb (s + 1)).getD (s - 2) false = false := by
    have hgb : SkipD3.gb (s + 1) = greedyWord (s + 1) := SkipD3.gb_eq (s + 1)
    rw [hgb, greedyWord_succ_split (by omega), decide_eq_false (by omega : ¬ _),
      show s - 2 =
        (integerGreedyBits (liftedPrefix s) (seamSubsetTarget (s + 1))).length by
        rw [integerGreedyBits_length, liftedPrefix_length]]
    exact getD_append_singleton _ _
  exact SkipD3.notMem_support_of_gb_false (by omega) (by omega) hbit

/-- **A small remainder buys a late skip.**  `LargestSkipLateAt (s+1)` follows
from `4 * seamIntegerGreedyRemainder s ≤ 2 ^ (s+1)` alone. -/
theorem largestSkipLateAt_succ_of_small_remainder {s : ℕ} (hs : 3 ≤ s)
    (h : 4 * seamIntegerGreedyRemainder s ≤ 2 ^ (s + 1)) :
    LargestSkipLateAt (s + 1) :=
  SkipD3.largestSkipLateAt_of_late_skip (m := s) (by omega) (by omega) (by omega)
    (topRank_notMem_support hs (by omega))

/-! ## 6. The escape step -/

/-- **The escape step.**  When the criterion does *not* fire at `s`, the row-`s`
greedy support extended by the brand-new rank is admissible at row `s + 1`, and
the remainder drops by a full `2 ^ (s+1)`. -/
theorem remainder_succ_le_of_large {s : ℕ} (hs : 3 ≤ s)
    (h : 2 ^ (s + 1) + 4 + carryTaken s ≤ 4 * seamIntegerGreedyRemainder s) :
    seamIntegerGreedyRemainder (s + 1) + 2 ^ (s + 1) + 4 + carryTaken s ≤
      4 * seamIntegerGreedyRemainder s := by
  have hpow : (2 : ℕ) ^ (s + 2) = 2 * 2 ^ (s + 1) := by rw [pow_succ]; ring
  have hT : seamSubsetTarget (s + 1) = 4 * seamSubsetTarget s + 2 ^ (s + 1) :=
    ErdosProblems.BitCorr2.seamSubsetTarget_succ (by omega)
  have hGR := greedySum_add_remainder s
  have hGR' := greedySum_add_remainder (s + 1)
  have hsum := weightedBoolSum_succ_row_true (s := s) (by omega) (greedyWord s)
    (greedyWord_length s)
  rw [truncatedMersenneWeight_succ_top hs] at hsum
  have hlen : (greedyWord s ++ [true]).length = (seamWeights (s + 1)).length := by
    rw [List.length_append, greedyWord_length, seamWeights_length_eq,
      List.length_singleton]
    omega
  have hadm : weightedBoolSum (seamWeights (s + 1)) (greedyWord s ++ [true]) ≤
      seamSubsetTarget (s + 1) := by
    rw [hsum]
    simp only [greedySum, carryTaken] at hGR h
    omega
  have hmax := integerGreedyBits_maximal (gap := 2 ^ (s + 1 + 1)) (by positivity)
    (seamWeights_gapDominates (s := s + 1) (by omega)) hlen hadm
  rw [hsum] at hmax
  simp only [greedySum, carryTaken, greedyWord] at hGR hGR' h hmax ⊢
  omega

/-- Carry-free form of the escape step: `carryTaken s ≤ 2 * (s - 2)` always, so
`2 ^ (s+1) + 2 * s + 4 ≤ 4 * r s` is enough to trigger it. -/
theorem remainder_succ_le_of_large' {s : ℕ} (hs : 3 ≤ s)
    (h : 2 ^ (s + 1) + 2 * s + 4 ≤ 4 * seamIntegerGreedyRemainder s) :
    seamIntegerGreedyRemainder (s + 1) + 2 ^ (s + 1) + 4 ≤
      4 * seamIntegerGreedyRemainder s := by
  have hc := carryTaken_le s
  have := remainder_succ_le_of_large hs (by omega)
  omega

/-- **The dichotomy.**  Every row either buys a late skip at the next row, or
hands down a remainder that has dropped by a full `2 ^ (s+1)`. -/
theorem dichotomy {s : ℕ} (hs : 3 ≤ s) :
    LargestSkipLateAt (s + 1) ∨
      seamIntegerGreedyRemainder (s + 1) + 2 ^ (s + 1) + 4 ≤
        4 * seamIntegerGreedyRemainder s := by
  by_cases h : 4 * seamIntegerGreedyRemainder s < 2 ^ (s + 1) + 4 + carryTaken s
  · exact Or.inl (SkipD3.largestSkipLateAt_of_late_skip (m := s) (by omega)
      (by omega) (by omega) (topRank_notMem_support hs h))
  · have := remainder_succ_le_of_large hs (by omega)
    exact Or.inr (by omega)

/-! ## 7. The finite escape window

Once the remainder is *below* `2 ^ s`, the deficit `2 ^ s - r s` quadruples at
every row that fails to buy a skip.  It cannot quadruple past `2 ^ (s+k)` for
more than `s` rows, so a skip must appear inside `[s+1, 2s+1]`. -/

/-- The quadrupling deficit invariant. -/
theorem deficit_grows {s K : ℕ} (hs : 3 ≤ s)
    (h : seamIntegerGreedyRemainder s < 2 ^ s)
    (hno : ∀ t : ℕ, s + 1 ≤ t → t ≤ s + K → ¬ LargestSkipLateAt t) :
    ∀ k : ℕ, k ≤ K →
      seamIntegerGreedyRemainder (s + k) +
          4 ^ k * (2 ^ s - seamIntegerGreedyRemainder s) ≤ 2 ^ (s + k) := by
  intro k
  induction k with
  | zero =>
      intro _
      simp only [Nat.add_zero, pow_zero, one_mul]
      omega
  | succ k ih =>
      intro hk
      have hkk := ih (by omega)
      have hpow : (2 : ℕ) ^ (s + k + 1) = 2 * 2 ^ (s + k) := by rw [pow_succ]; ring
      have hfour : (4 : ℕ) ^ (k + 1) * (2 ^ s - seamIntegerGreedyRemainder s)
          = 4 * (4 ^ k * (2 ^ s - seamIntegerGreedyRemainder s)) := by
        rw [pow_succ]; ring
      rw [show s + (k + 1) = s + k + 1 from rfl]
      rcases dichotomy (s := s + k) (by omega) with hlate | hstep
      · exact absurd hlate (hno (s + k + 1) (by omega) (by omega))
      · omega

/-- **The escape theorem, quantitative.**  A deficit of `2 ^ j` below `2 ^ s`
in the row-`s` remainder forces a late largest false rank within `s - j + 1`
rows: the deficit quadruples every row that fails to buy a skip, and it cannot
outrun `2 ^ (s+k)` for longer than that. -/
theorem exists_largestSkipLateAt_of_deficit {s j : ℕ} (hs : 3 ≤ s) (hjs : j ≤ s)
    (h : seamIntegerGreedyRemainder s + 2 ^ j ≤ 2 ^ s) :
    ∃ t : ℕ, s + 1 ≤ t ∧ t ≤ 2 * s - j + 1 ∧ LargestSkipLateAt t := by
  by_contra hcon
  have hjpos : 0 < (2 : ℕ) ^ j := by positivity
  have hno : ∀ t : ℕ, s + 1 ≤ t → t ≤ s + (s - j + 1) → ¬ LargestSkipLateAt t := by
    intro t h1 h2 ht
    exact hcon ⟨t, h1, by omega, ht⟩
  have key := deficit_grows hs (by omega) hno (s - j + 1) (le_refl _)
  have h1 : (4 : ℕ) ^ (s - j + 1) * 2 ^ j ≤
      4 ^ (s - j + 1) * (2 ^ s - seamIntegerGreedyRemainder s) :=
    Nat.mul_le_mul_left _ (by omega)
  have h2 : (4 : ℕ) ^ (s - j + 1) * 2 ^ j = 2 ^ (2 * (s - j + 1) + j) := by
    rw [show (4 : ℕ) = 2 ^ 2 by norm_num, ← pow_mul, ← pow_add]
  have h3 : (2 : ℕ) ^ (2 * (s - j + 1) + j) ≤ 2 ^ (s + (s - j + 1)) := by omega
  have h4 : 2 * (s - j + 1) + j ≤ s + (s - j + 1) :=
    (Nat.pow_le_pow_iff_right (by norm_num)).mp h3
  omega

/-- **The escape theorem.**  A row whose greedy remainder has dropped below
`2 ^ s` forces a late largest false rank at some row in the window
`[s+1, 2s+1]`. -/
theorem exists_largestSkipLateAt_of_remainder_lt {s : ℕ} (hs : 3 ≤ s)
    (h : seamIntegerGreedyRemainder s < 2 ^ s) :
    ∃ t : ℕ, s + 1 ≤ t ∧ t ≤ 2 * s + 1 ∧ LargestSkipLateAt t := by
  obtain ⟨t, h1, h2, h3⟩ :=
    exists_largestSkipLateAt_of_deficit (s := s) (j := 0) hs (by omega) (by simpa using h)
  exact ⟨t, h1, by omega, h3⟩

/-- **The reduction.**  Erdős `#257`'s `1/2` question is *implied* by a single
inequality holding infinitely often: `seamIntegerGreedyRemainder s < 2 ^ s`. -/
theorem half_mem_of_remainder_lt_cofinally
    (h : ∀ N : ℕ, ∃ s : ℕ, N ≤ s ∧ seamIntegerGreedyRemainder s < 2 ^ s) :
    (1 / 2 : ℝ) ∈ mersenneAchievementSet := by
  refine AngleD2.half_mem_of_unboundedLargestSkipLate ?_
  intro N
  obtain ⟨s, hsN, hrs⟩ := h (max N 3)
  have h3 : 3 ≤ s := le_trans (le_max_right N 3) hsN
  have hN : N ≤ s := le_trans (le_max_left N 3) hsN
  obtain ⟨t, ht1, _, hlate⟩ := exists_largestSkipLateAt_of_remainder_lt h3 hrs
  exact ⟨t, by omega, hlate⟩

/-- Contrapositive of the preceding reduction: if `1/2` is *not* achieved, then
from some row on the seam greedy remainder never again drops below `2 ^ s`. -/
theorem remainder_ge_of_half_notMem
    (h : (1 / 2 : ℝ) ∉ mersenneAchievementSet) :
    ∃ N : ℕ, ∀ s : ℕ, N ≤ s → 2 ^ s ≤ seamIntegerGreedyRemainder s := by
  by_contra hcon
  refine h (half_mem_of_remainder_lt_cofinally ?_)
  intro N
  simp only [not_exists, not_forall] at hcon
  obtain ⟨s, hs, hlt⟩ := hcon N
  exact ⟨s, hs, by omega⟩

/-! ## 8. Non-vacuity: the criterion really fires -/

/-- Kernel-computable form of the seam greedy remainder.  `seamWeightsFrom` is
defined by well-founded recursion; `SkipD3.wgt` is the same list by structural
recursion, so `rem` reduces inside the kernel. -/
def rem (s : ℕ) : ℕ :=
  seamSubsetTarget s - weightedBoolSum (SkipD3.wgt s 2 (s - 2)) (SkipD3.gb s)

theorem rem_eq (s : ℕ) : rem s = seamIntegerGreedyRemainder s := by
  simp only [rem, seamIntegerGreedyRemainder, integerGreedyRemainder,
    SkipD3.seamWeights_eq_wgt, SkipD3.gb]

/-- The criterion, in kernel-computable form. -/
theorem lateAt_succ_of_rem {s : ℕ} (hs : 3 ≤ s) (h : 4 * rem s ≤ 2 ^ (s + 1)) :
    LargestSkipLateAt (s + 1) :=
  largestSkipLateAt_succ_of_small_remainder hs (by rw [← rem_eq]; exact h)

section Witnesses

set_option maxRecDepth 8000000

/-- Smallest witness: `seamIntegerGreedyRemainder 14 = 392`, far below
`2 ^ 13 = 8192`, so rank `14` is skipped at row `15`. -/
theorem lateAt_15 : LargestSkipLateAt 15 :=
  lateAt_succ_of_rem (s := 14) (by norm_num) (by decide +kernel)

theorem lateAt_22 : LargestSkipLateAt 22 :=
  lateAt_succ_of_rem (s := 21) (by norm_num) (by decide +kernel)

theorem lateAt_36 : LargestSkipLateAt 36 :=
  lateAt_succ_of_rem (s := 35) (by norm_num) (by decide +kernel)

theorem lateAt_101 : LargestSkipLateAt 101 :=
  lateAt_succ_of_rem (s := 100) (by norm_num) (by decide +kernel)

/-- The first row past `Corr3`'s certified block `[501, 1200]`. -/
theorem lateAt_1201 : LargestSkipLateAt 1201 :=
  lateAt_succ_of_rem (s := 1200) (by norm_num) (by decide +kernel)

theorem lateAt_3002 : LargestSkipLateAt 3002 :=
  lateAt_succ_of_rem (s := 3001) (by norm_num) (by decide +kernel)

theorem lateAt_8001 : LargestSkipLateAt 8001 :=
  lateAt_succ_of_rem (s := 8000) (by norm_num) (by decide +kernel)

/-- A kernel-checked finite witness at row `12003`. -/
theorem lateAt_12003 : LargestSkipLateAt 12003 :=
  lateAt_succ_of_rem (s := 12002) (by norm_num) (by decide +kernel)

/-- The hypothesis of the escape theorem is satisfiable, and *not* only through
the immediate criterion: at `s = 20` the remainder `549353` sits below `2 ^ 20`
with a deficit past `2 ^ 18`, while `4 * rem 20 = 2197412 > 2 ^ 21`, so the
criterion does **not** fire at `20` and the deficit argument has to run.  The
quantitative form pins the resulting skip to the three-row window `[21, 23]`. -/
theorem escape_witness_20 :
    2 ^ 21 < 4 * seamIntegerGreedyRemainder 20 ∧
      ∃ t : ℕ, 21 ≤ t ∧ t ≤ 23 ∧ LargestSkipLateAt t := by
  refine ⟨by rw [← rem_eq]; decide +kernel, ?_⟩
  have h1 : seamIntegerGreedyRemainder 20 + 2 ^ 18 ≤ 2 ^ 20 := by
    rw [← rem_eq]; decide +kernel
  obtain ⟨t, ht1, ht2, ht3⟩ :=
    exists_largestSkipLateAt_of_deficit (s := 20) (j := 18) (by norm_num)
      (by norm_num) h1
  exact ⟨t, ht1, by omega, ht3⟩

/-- The hypothesis of the escape step — the *other* branch of `dichotomy` — is
satisfiable too: at `s = 19` the criterion misses by a wide margin
(`4 * r 19 = 3697820` against `2 ^ 20 + 42 = 1048618`), so the remainder really
does drop by a full `2 ^ 20` from row `19` to row `20`. -/
theorem escape_step_witness_19 :
    2 ^ (19 + 1) + 2 * 19 + 4 ≤ 4 * seamIntegerGreedyRemainder 19 ∧
      seamIntegerGreedyRemainder 20 + 2 ^ (19 + 1) + 4 ≤
        4 * seamIntegerGreedyRemainder 19 := by
  have hhyp : 2 ^ (19 + 1) + 2 * 19 + 4 ≤ 4 * seamIntegerGreedyRemainder 19 := by
    rw [← rem_eq]; decide +kernel
  exact ⟨hhyp, remainder_succ_le_of_large' (s := 19) (by norm_num) hhyp⟩

/-- The hypothesis of `half_mem_of_remainder_lt_cofinally` is satisfied at every
`N ≤ 12002`.  Cofinality — the one thing `#257` actually needs — is exactly what
is *not* proved here. -/
theorem remainder_lt_witness {N : ℕ} (hN : N ≤ 12002) :
    ∃ s : ℕ, N ≤ s ∧ seamIntegerGreedyRemainder s < 2 ^ s :=
  ⟨12002, hN, by rw [← rem_eq]; decide +kernel⟩

end Witnesses

/-! ## 9. Calibration counterexamples

The following witnesses separate the sufficient hypotheses above from their
conclusions.  They do not classify all possible refinements of those
hypotheses. -/

section Calibration

set_option maxRecDepth 8000000

/-- **The criterion is sufficient but not necessary.**  At `s = 19` the transfer
bound is far too weak — `4 * r 19 = 3697820` against `2 ^ 20 = 1048576` — and yet
the brand-new rank `19` really is skipped at row `20`.  Thus the displayed
sufficient inequality is not a necessary condition for that skip. -/
theorem criterion_not_necessary :
    2 ^ 20 < 4 * seamIntegerGreedyRemainder 19 ∧
      (19 : ℕ) ∉ seamWordSupport (seamGreedyWord 20) := by
  refine ⟨by rw [← rem_eq]; decide +kernel, ?_⟩
  exact SkipD3.notMem_support_of_gb_false (by norm_num) (by norm_num)
    (by decide +kernel)

/-- **A late skip does not supply the escape hypothesis.**  Row `19` has a late
largest false rank (`d = 14`, and `2 * 19 = 38 < 42 = 3 * 14`), yet its greedy
remainder is `924455 ≥ 524288 = 2 ^ 19`.  This is a concrete counterexample to
the implication from a late skip at row `s` to the escape hypothesis at the
same row. -/
theorem lateSkip_does_not_give_escape :
    LargestSkipLateAt 19 ∧ 2 ^ 19 ≤ seamIntegerGreedyRemainder 19 := by
  refine ⟨SkipD3.largestSkipLateAt_of_rowChk (s := 19) (d := 14) (by norm_num)
    (by norm_num) (by norm_num) (by decide +kernel), ?_⟩
  rw [← rem_eq]; decide +kernel

/-- The `GapDominates` estimate available for the seam weights.  This statement
does not claim that `2 ^ (s+1)` is the largest admissible gap parameter. -/
theorem gap_is_two_pow_succ {s : ℕ} (hs : 2 ≤ s) :
    GapDominates (2 ^ (s + 1)) (seamWeights s) :=
  seamWeights_gapDominates hs

end Calibration

end BitR3

end ErdosProblems
