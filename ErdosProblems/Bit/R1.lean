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
# Bit R1: the row-to-row law the forced run must obey — and why it survives it

`AngleD2.half_mem_iff_unboundedLargestSkipLate` reduces the `1/2` question of
Erdős `#257` to `LargestSkipLateAt s` at cofinally many rows.  Negating it gives
the **forced run**: `LargestSkipLateAt` fails from some row `N` on
(`not_half_mem_iff_exists_forcedRun`).  This file asks the question the
`Corr2` recurrence was built for — *does the row-to-row recurrence refute the
forced run?* — and answers it in three parts: a two-sided law the run must
obey, a single-scalar certificate falling out of it, and a proof that the law
by itself cannot finish the job.

## The mechanism

Row `s + 1` carries exactly one rank row `s` does not: the top rank `s`.  It is
*late* at row `s+1` (`2*(s+1) < 3*s` for `s ≥ 3`), so the forced run makes the
greedy take it, and its weight is exactly `2 ^ (s+2) + 4` (`top_weight`).  By
`Corr2.seamWeightsFrom_succ_row` the rest of row `s+1`'s weight word is the lift
`w ↦ 4*w + rowCarry s w` of row `s`'s (`liftedRow`), whose total carry budget is
at most `2*(s-2)` (`Corr2.rowCarriesFrom_sum_le`).  Running
`integerGreedyBits_maximal` in *both* directions across that lift — the row-`s`
greedy word pushed up into row `s+1`, and the row-`s+1` greedy word pulled back
down into row `s` — pins the two defects to each other.

## Main results

* `remainder_step_of_top_mem` / `remainder_step_of_not_largestSkipLateAt` —
  **the two-sided row law.**  For `s ≥ 3`, if `LargestSkipLateAt (s+1)` fails then

      R (s+1) + 2 ^ (s+1) + 4  ≤  4 * R s  ≤  R (s+1) + 2 ^ (s+1) + 2 * s

  where `R = seamIntegerGreedyRemainder`.  The *lower* half — the descent, which
  says the row step must lose the whole top weight — comes from pushing row `s`
  up.  The *upper* half — the ascent — comes from pulling row `s+1` back down,
  and is what makes the law two-sided.

* `forcedRun_defect_window` — the same statement as an equation.  Under the
  forced run, `R (s+1) = 4 * R s - 2 ^ (s+1) - c` with `4 ≤ c ≤ 2*s`: the tail of
  the defect sequence is a *deterministic* quadrupling map up to a correction
  confined to a window of width `2*s - 4`, against an a-priori spread of order
  `2 ^ (s+2)`.

* `largestSkipLateAt_succ_of_window_miss` (and its one-sided halves
  `..._of_ascent`, `..._of_descent`) — **the certificate.**  The theorem
  statement uses two scalars to decide
  the `#257` predicate: if `4 * R s - R (s+1) - 2 ^ (s+1)` leaves `[4, 2*s]`,
  then `LargestSkipLateAt (s+1)`.  The concrete scalar certificates below are
  computed from the greedy row words; the implication itself does not take a
  word hypothesis.

* `remainder_ge_of_no_late_window`, `exists_largestSkipLateAt_of_remainder_small`
  — iterating the descent forwards.  A dip to `R s ≤ 2 ^ s + 1` cannot survive
  `s + 2` further rows without going negative, so it forces a late largest false
  rank somewhere in the window `[s+1, 2*s+2]`.  Under the forced run this reads
  `2 ^ s + 2 ≤ R s` at every row (`remainder_ge_of_forcedRun`).

* `stepLaw_iterate`, `remainder_le_of_forcedRun_of_growth`,
  `remainder_band_of_forcedRun_of_growth` — iterating the ascent backwards.  The
  ascent is contracting by a factor `4` per row against a target that only
  doubles, so `R s` is squeezed *down* onto `2 ^ s`: modulo the size regime
  `R m ≤ 2 ^ (m+1)` measured at every computed row, the forced run confines the
  defect to the band `[2 ^ s + 2, 2 ^ s + 2*s + 1]`.

* `stepLaw_pow_add_two`, `exists_stepLaw` — **the sharp negative.**  The law is
  *consistent*: the explicit sequence `f s = 2 ^ s + 2` satisfies it at every
  row `s ≥ 3` (its correction is the constant `c = 6`, and `4 ≤ 6 ≤ 2*s`).  So
  no contradiction can ever be extracted from the row law alone.  **The
  recurrence does not refute the forced run** — it only pins it.

## Measurement

Outside the kernel, an arbitrary-precision replication of `seamWeights`,
`seamSubsetTarget` and `integerGreedyBits` was run on every `s ∈ [5, 501]`, plus
the spot rows `1495 … 1505`.  It reproduces this repository's earlier numbers
exactly: `Corr2`'s `seamIntegerGreedyRemainder 14 = 392` and
`seamIntegerGreedyRemainder 15 = 34333`; `H3`'s "`LargestSkipLateAt` at every
`s ∈ [5,400]` except `s = 5, 11, 12, 13`" (over `[5,500]` it fails at exactly
those four rows); `H4`'s `d₀(81) = 75`; `Corr3`'s record row `d₀(1148) = 1135`
(top run `12`), and `d₀(1500) = 1499`, `d₀(3000) = 2996`, `d₀(3001) = 3000`.

* At the three rows of the range where the law's hypothesis genuinely holds —
  `s = 10, 11, 12`, i.e. `LargestSkipLateAt` failing at `11, 12, 13` — the
  correction `c = 4*R s - R (s+1) - 2 ^ (s+1)` is `7, 8, 5`.  All three lie
  inside `[4, 2*s]`, as the law requires, and none is far from the constant `6`
  of the no-go sequence.
* The ascent certificate fires at `120` of the `496` rows, longest gap `9`; the
  descent certificate at `119`, longest gap `11`; their union at `239` rows
  (`48%`), longest gap `8`.  Not one fire is unsound.
* The band `[2 ^ s + 2, 2 ^ s + 2*s + 1]` is violated at `494` of the `495` rows
  `s ∈ [6, 500]`.  The single row inside it is `s = 8`, where `R 8 = 2 ^ 8 + 9`.
* The window certificate's hypothesis `R s ≤ 2 ^ s + 1` holds at `230` of those
  rows.

## What is certified in the kernel

No `sorry`, no `native_decide`, no new axiom; `decide +kernel` only, and every
theorem checks with axioms `[propext, Classical.choice, Quot.sound]`.

`§8` turns the certificate into `LargestSkipLateAt` at rows `8, 14, 15, 20, 26,
32, 38, 102, 401, 1500, 1501` from the two scalar remainders at adjacent rows.
Those scalars are themselves computed by `remOf` through `SkipD3.gb`, so this is
a scalar theorem interface, not a computation that avoids the greedy words.
Rows `1500` and `1501` lie beyond `Corr3`'s `[501, 1200]` block, but they do not
extend the corpus's overall certified reach: `SkipD3` can certify those rows
directly and also certifies row `3000`.  The same call at `s = 1498`, where the
replication says the certificate is silent, is rejected by the kernel, so the
displayed scalar instances are genuine and not a vacuous side condition.

## Non-vacuity

* `top_mem_eleven` — the hypothesis of `remainder_step_of_top_mem` is satisfied
  at `s = 11`, and `remainder_step_eleven` is the law there.
* `not_largestSkipLateAt_twelve` — the hypothesis of
  `remainder_step_of_not_largestSkipLateAt` is satisfied at `s = 11` as well:
  row `12` is one of the four rows where `LargestSkipLateAt` genuinely fails, its
  whole late zone `9, 10, 11` being selected.  `remainder_step_eleven'` and
  `defect_window_eleven` are the law and the window at that row (`c = 8`).
* `remainder_small_seven` / `exists_late_in_window_seven` — the hypothesis of
  the contrapositive certificate
  `exists_largestSkipLateAt_of_remainder_small` is satisfied at `s = 7`
  (`R 7 = 3`), and the conclusion is a late largest false rank in `[8, 16]`;
  `lateAt_8` shows it is already at the left end.
* `stepLaw_pow_add_two` exhibits a satisfying instance of `StepLaw`.

No instance is exhibited for `ForcedRun N`:
exhibiting one would settle Erdős `#257` negatively.  Every theorem carrying it
— `forcedRun_defect_window`, `stepLaw_of_forcedRun`, `remainder_ge_of_forcedRun`,
`remainder_le_of_forcedRun_of_growth`, `remainder_band_of_forcedRun_of_growth` —
is therefore conditional on an open statement, and may be vacuous.  The
localised forms carry no such hypothesis, but they do not all have known
instances.  `remainder_step_of_not_largestSkipLateAt` and
`exists_largestSkipLateAt_of_remainder_small` are witnessed above.
**MEASURED:** the hypothesis of `remainder_ge_of_no_late_window` holds at no
row of `[5,240]`; it needs at least `s+2 ≥ 7` consecutive non-late rows, while
the longest measured run in `[5,501]` has length `3`.  Its useful
non-vacuous form here is the contrapositive certificate.

## What this does *not* prove

Two things.  First, `remainder_le_of_forcedRun_of_growth` needs the growth
side condition `R m ≤ 2 ^ (m+1)`; that is measured at every row of `[6, 500]`
but is *not* proved here, and the obstruction is real — the greedy defect is
bounded above by the gap `w d₀ - Σ_{d > d₀} w d` at the largest false rank `d₀`,
which is only `O(2 ^ (s+1))` when `d₀` is close to `s`, i.e. precisely when
`LargestSkipLateAt` already holds.  Second, and decisively,
`stepLaw_pow_add_two` shows the whole approach is bounded: the row law is a
*necessary* condition on the defect sequence with an explicit solution, so it
cannot on its own force `LargestSkipLateAt` at even one row, let alone
cofinally many.  Any refutation of the forced run must use something the
recurrence does not see.
-/

namespace Erdos249257

namespace BitR1

open HalfCylinderIntegerGreedy
open ErdosProblems.BitCorr2

/-! ## 1. `weightedBoolSum` plumbing -/

theorem wbs_nil_weights (bs : List Bool) : weightedBoolSum [] bs = 0 := by
  cases bs <;> rfl

theorem wbs_nil_bits (ws : List ℕ) : weightedBoolSum ws [] = 0 := by
  cases ws <;> rfl

theorem wbs_cons_true (w : ℕ) (ws : List ℕ) (bs : List Bool) :
    weightedBoolSum (w :: ws) (true :: bs) = w + weightedBoolSum ws bs := rfl

theorem wbs_cons_false (w : ℕ) (ws : List ℕ) (bs : List Bool) :
    weightedBoolSum (w :: ws) (false :: bs) = weightedBoolSum ws bs := rfl

/-- A weighted subset sum splits along a concatenation once the bit word is cut
at the same place. -/
theorem wbs_append : ∀ (l₁ : List ℕ) (b₁ : List Bool), b₁.length = l₁.length →
    ∀ (l₂ : List ℕ) (b₂ : List Bool),
      weightedBoolSum (l₁ ++ l₂) (b₁ ++ b₂) =
        weightedBoolSum l₁ b₁ + weightedBoolSum l₂ b₂ := by
  intro l₁
  induction l₁ with
  | nil =>
      intro b₁ h l₂ b₂
      have hb : b₁ = [] := List.eq_nil_of_length_eq_zero (by simpa using h)
      subst hb
      simp [wbs_nil_weights]
  | cons w ws ih =>
      intro b₁ h l₂ b₂
      cases b₁ with
      | nil => simp at h
      | cons b bs =>
          simp only [List.length_cons, Nat.succ.injEq] at h
          cases b
          · simp only [List.cons_append, wbs_cons_false]
            exact ih bs h l₂ b₂
          · simp only [List.cons_append, wbs_cons_true, ih bs h l₂ b₂]
            omega

theorem lift_cons (w c : ℕ) (ws cs : List ℕ) :
    liftWeights (w :: ws) (c :: cs) = (4 * w + c) :: liftWeights ws cs := by
  simp [liftWeights]

theorem lift_nil_left (cs : List ℕ) : liftWeights [] cs = [] := by
  simp [liftWeights]

theorem liftWeights_length (ws cs : List ℕ) :
    (liftWeights ws cs).length = min ws.length cs.length := by
  simp [liftWeights]

/-- Selecting any bit word inside the lifted weights achieves at least four
times what the same word achieves in the base weights. -/
theorem four_mul_wbs_le_lift : ∀ (ws cs : List ℕ), cs.length = ws.length →
    ∀ bs : List Bool,
      4 * weightedBoolSum ws bs ≤ weightedBoolSum (liftWeights ws cs) bs := by
  intro ws
  induction ws with
  | nil =>
      intro cs _ bs
      rw [lift_nil_left, wbs_nil_weights]
  | cons w ws ih =>
      intro cs hlen bs
      cases cs with
      | nil => simp at hlen
      | cons c cs =>
          simp only [List.length_cons, Nat.succ.injEq] at hlen
          rw [lift_cons]
          cases bs with
          | nil =>
              rw [wbs_nil_bits, wbs_nil_bits]
          | cons b bs =>
              cases b
              · rw [wbs_cons_false, wbs_cons_false]
                exact ih cs hlen bs
              · rw [wbs_cons_true, wbs_cons_true]
                have := ih cs hlen bs
                omega

/-- …and at most four times that, plus the entire carry budget. -/
theorem wbs_lift_le : ∀ (ws cs : List ℕ), cs.length = ws.length →
    ∀ bs : List Bool,
      weightedBoolSum (liftWeights ws cs) bs ≤ 4 * weightedBoolSum ws bs + cs.sum := by
  intro ws
  induction ws with
  | nil =>
      intro cs _ bs
      rw [lift_nil_left, wbs_nil_weights]
      omega
  | cons w ws ih =>
      intro cs hlen bs
      cases cs with
      | nil => simp at hlen
      | cons c cs =>
          simp only [List.length_cons, Nat.succ.injEq] at hlen
          rw [lift_cons, List.sum_cons]
          cases bs with
          | nil =>
              rw [wbs_nil_bits, wbs_nil_bits]
              omega
          | cons b bs =>
              cases b
              · rw [wbs_cons_false, wbs_cons_false]
                have := ih cs hlen bs
                omega
              · rw [wbs_cons_true, wbs_cons_true]
                have := ih cs hlen bs
                omega

/-- A prefix of a gap-dominating word is gap-dominating. -/
theorem gapDominates_of_append_left {gap : ℕ} :
    ∀ (l₁ l₂ : List ℕ), GapDominates gap (l₁ ++ l₂) → GapDominates gap l₁ := by
  intro l₁
  induction l₁ with
  | nil => intro l₂ _; trivial
  | cons w ws ih =>
      intro l₂ h
      rw [List.cons_append, GapDominates] at h
      obtain ⟨hhead, htail⟩ := h
      refine ⟨?_, ih l₂ htail⟩
      have : ws.sum ≤ (ws ++ l₂).sum := by
        rw [List.sum_append]
        omega
      omega

/-! ## 2. The row step, split at the brand-new top rank -/

/-- Row `s+1`'s weight word with its brand-new top rank `s` removed: every
row-`s` weight quadruples and picks up its carry (`Corr2`). -/
def liftedRow (s : ℕ) : List ℕ := liftWeights (seamWeights s) (rowCarriesFrom s 2)

/-- The row-`s+1` greedy word restricted to that lifted prefix. -/
def preBits (s : ℕ) : List Bool :=
  integerGreedyBits (liftedRow s) (seamSubsetTarget (s + 1))

/-- What the row-`s+1` greedy has already spent when it reaches its top rank. -/
def preSum (s : ℕ) : ℕ := weightedBoolSum (liftedRow s) (preBits s)

theorem liftedRow_length (s : ℕ) : (liftedRow s).length = s - 2 := by
  rw [liftedRow, liftWeights_length, seamWeights_length_eq, rowCarriesFrom_length]
  simp

theorem preBits_length (s : ℕ) : (preBits s).length = s - 2 := by
  rw [preBits, integerGreedyBits_length, liftedRow_length]

theorem seamWeights_succ_split {s : ℕ} (hs : 2 ≤ s) :
    seamWeights (s + 1) = liftedRow s ++ [truncatedMersenneWeight (s + 1) s] := by
  rw [liftedRow]
  exact seamWeightsFrom_succ_row (le_refl 2) hs

theorem greedy_succ_split {s : ℕ} (hs : 2 ≤ s) :
    integerGreedyBits (seamWeights (s + 1)) (seamSubsetTarget (s + 1)) =
      preBits s ++
        integerGreedyBits [truncatedMersenneWeight (s + 1) s]
          (seamSubsetTarget (s + 1) - preSum s) := by
  rw [seamWeights_succ_split hs, integerGreedyBits_append, preBits, preSum, preBits]

/-- The brand-new top rank of row `s + 1` carries weight `2 ^ (s+2) + 4`. -/
theorem top_weight {s : ℕ} (hs : 3 ≤ s) :
    truncatedMersenneWeight (s + 1) s = 2 * 2 ^ (s + 1) + 4 := by
  rw [truncatedMersenneWeight_eq_twoPower_add_fourPower_of_lateRank
      (by omega : 2 ≤ s) (by omega : s < s + 1) (by omega : 2 * (s + 1) < 3 * s),
    show 2 * (s + 1) - s = s + 1 + 1 by omega, show s + 1 - s = 1 by omega,
    pow_succ]
  norm_num
  ring

/-- The top rank of row `s + 1` is selected exactly when the remainder entering
the last greedy step can still pay for it. -/
theorem top_mem_iff {s : ℕ} (hs : 3 ≤ s) :
    s ∈ seamWordSupport (seamGreedyWord (s + 1)) ↔
      truncatedMersenneWeight (s + 1) s ≤ seamSubsetTarget (s + 1) - preSum s := by
  rw [BitCorr.mem_seamGreedySupport_iff_getElem (s := s + 1) (e := s)
      (by omega) (by omega),
    greedy_succ_split (by omega),
    List.getElem?_append_right (by rw [preBits_length]),
    preBits_length, show s - 2 - (s - 2) = 0 by omega]
  by_cases hc : truncatedMersenneWeight (s + 1) s ≤ seamSubsetTarget (s + 1) - preSum s
  · simp [integerGreedyBits, hc]
  · simp [integerGreedyBits, hc]

/-! ## 3. The two-sided row law -/

/-- **The row law.**  Once the brand-new top rank of row `s+1` is selected, the
concrete seam greedy defect obeys a two-sided recurrence: it is pinned to a
window of width `2*s - 4` around `4 * R s - 2 ^ (s+1)`. -/
theorem remainder_step_of_top_mem {s : ℕ} (hs : 3 ≤ s)
    (htop : s ∈ seamWordSupport (seamGreedyWord (s + 1))) :
    seamIntegerGreedyRemainder (s + 1) + 2 ^ (s + 1) + 4 ≤
        4 * seamIntegerGreedyRemainder s ∧
      4 * seamIntegerGreedyRemainder s ≤
        seamIntegerGreedyRemainder (s + 1) + 2 ^ (s + 1) + 2 * s := by
  have hlin : 2 * s + 4 < 2 ^ (s + 1) := two_mul_add_four_lt_two_pow_succ (by omega)
  have hcslen : (rowCarriesFrom s 2).length = (seamWeights s).length := by
    rw [rowCarriesFrom_length, seamWeights_length_eq]
  have hcssum : (rowCarriesFrom s 2).sum ≤ 2 * (s - 2) :=
    rowCarriesFrom_sum_le s 2 (le_refl 2)
  -- the target recurrence and the top weight
  have h1 : seamSubsetTarget (s + 1) = 4 * seamSubsetTarget s + 2 ^ (s + 1) :=
    ErdosProblems.BitCorr2.seamSubsetTarget_succ (by omega)
  have h2 : truncatedMersenneWeight (s + 1) s = 2 * 2 ^ (s + 1) + 4 := top_weight hs
  -- the row-`s+1` achieved sum splits as prefix + top weight
  have htopbit := (top_mem_iff hs).mp htop
  have hgb : integerGreedyBits (seamWeights (s + 1)) (seamSubsetTarget (s + 1)) =
      preBits s ++ [true] := by
    rw [greedy_succ_split (by omega)]
    congr 1
    rw [integerGreedyBits, if_pos htopbit]
    rfl
  have hAsucc :
      weightedBoolSum (seamWeights (s + 1))
          (integerGreedyBits (seamWeights (s + 1)) (seamSubsetTarget (s + 1))) =
        preSum s + truncatedMersenneWeight (s + 1) s := by
    rw [hgb, seamWeights_succ_split (by omega),
      wbs_append _ _ (by rw [preBits_length, liftedRow_length]) _ _]
    rw [preSum]
    congr 1
  have h5 : seamIntegerGreedyRemainder (s + 1) =
      seamSubsetTarget (s + 1) - (preSum s + truncatedMersenneWeight (s + 1) s) := by
    rw [seamIntegerGreedyRemainder, integerGreedyRemainder, hAsucc]
  have h6 : preSum s + truncatedMersenneWeight (s + 1) s ≤ seamSubsetTarget (s + 1) := by
    rw [← hAsucc]
    exact integerGreedyBits_admissible _ _
  -- the row-`s` quantities
  have h3 : seamIntegerGreedyRemainder s =
      seamSubsetTarget s -
        weightedBoolSum (seamWeights s)
          (integerGreedyBits (seamWeights s) (seamSubsetTarget s)) := rfl
  have h4 : weightedBoolSum (seamWeights s)
      (integerGreedyBits (seamWeights s) (seamSubsetTarget s)) ≤ seamSubsetTarget s :=
    integerGreedyBits_admissible _ _
  -- the prefix word, read in the row-`s` weights
  have h7 : 4 * weightedBoolSum (seamWeights s) (preBits s) ≤ preSum s := by
    rw [preSum, liftedRow]
    exact four_mul_wbs_le_lift _ _ hcslen _
  have h8 : preSum s ≤
      4 * weightedBoolSum (seamWeights s) (preBits s) + (rowCarriesFrom s 2).sum := by
    rw [preSum, liftedRow]
    exact wbs_lift_le _ _ hcslen _
  have hA'T : weightedBoolSum (seamWeights s) (preBits s) ≤ seamSubsetTarget s := by
    omega
  have h10 : weightedBoolSum (seamWeights s) (preBits s) ≤
      weightedBoolSum (seamWeights s)
        (integerGreedyBits (seamWeights s) (seamSubsetTarget s)) :=
    integerGreedyBits_maximal (gap := 2 ^ (s + 1)) (by positivity)
      (seamWeights_gapDominates (by omega))
      (by rw [preBits_length, seamWeights_length_eq]) hA'T
  -- the row-`s` greedy word, read in the lifted weights
  have h11 : 4 * weightedBoolSum (seamWeights s)
        (integerGreedyBits (seamWeights s) (seamSubsetTarget s)) ≤
      weightedBoolSum (liftedRow s)
        (integerGreedyBits (seamWeights s) (seamSubsetTarget s)) := by
    rw [liftedRow]
    exact four_mul_wbs_le_lift _ _ hcslen _
  have h11' : weightedBoolSum (liftedRow s)
        (integerGreedyBits (seamWeights s) (seamSubsetTarget s)) ≤
      4 * weightedBoolSum (seamWeights s)
        (integerGreedyBits (seamWeights s) (seamSubsetTarget s)) +
        (rowCarriesFrom s 2).sum := by
    rw [liftedRow]
    exact wbs_lift_le _ _ hcslen _
  have hdom : GapDominates (2 ^ (s + 1 + 1)) (liftedRow s) :=
    gapDominates_of_append_left _ _
      (by rw [← seamWeights_succ_split (by omega)]
          exact seamWeights_gapDominates (by omega))
  have h12 : weightedBoolSum (liftedRow s)
        (integerGreedyBits (seamWeights s) (seamSubsetTarget s)) ≤ preSum s := by
    rw [preSum, preBits]
    refine integerGreedyBits_maximal (gap := 2 ^ (s + 1 + 1)) (by positivity) hdom
      (by rw [integerGreedyBits_length, seamWeights_length_eq, liftedRow_length]) ?_
    omega
  omega

/-! ## 4. The `#257` endpoint -/

/-- The forced run: `LargestSkipLateAt` fails from row `N` on. -/
def ForcedRun (N : ℕ) : Prop := ∀ s : ℕ, N ≤ s → ¬ LargestSkipLateAt s

/-- Failure of half membership is exactly a forced run. -/
theorem not_half_mem_iff_exists_forcedRun :
    (1 / 2 : ℝ) ∉ mersenneAchievementSet ↔ ∃ N : ℕ, ForcedRun N := by
  rw [AngleD2.half_mem_iff_unboundedLargestSkipLate, AngleD2.UnboundedLargestSkipLate]
  constructor
  · intro h
    by_contra hc
    exact h fun N => by
      by_contra hN
      exact hc ⟨N, fun s hs hp => hN ⟨s, hs, hp⟩⟩
  · rintro ⟨N, hN⟩ hcon
    obtain ⟨s, hs, hlate⟩ := hcon N
    exact hN s hs hlate

/-- Under the forced run, every brand-new top rank is selected. -/
theorem top_mem_of_not_largestSkipLateAt {s : ℕ} (hs : 3 ≤ s)
    (h : ¬ LargestSkipLateAt (s + 1)) :
    s ∈ seamWordSupport (seamGreedyWord (s + 1)) :=
  AngleD2.mem_of_late_of_not_largestSkipLateAt h (by omega) (by omega) (by omega)

/-- **The row law, in `#257` vocabulary.** -/
theorem remainder_step_of_not_largestSkipLateAt {s : ℕ} (hs : 3 ≤ s)
    (h : ¬ LargestSkipLateAt (s + 1)) :
    seamIntegerGreedyRemainder (s + 1) + 2 ^ (s + 1) + 4 ≤
        4 * seamIntegerGreedyRemainder s ∧
      4 * seamIntegerGreedyRemainder s ≤
        seamIntegerGreedyRemainder (s + 1) + 2 ^ (s + 1) + 2 * s :=
  remainder_step_of_top_mem hs (top_mem_of_not_largestSkipLateAt hs h)

/-- **The certificate, ascent side.**  If the defect falls too fast from row `s`
to row `s+1`, row `s+1` has a late largest false rank. -/
theorem largestSkipLateAt_succ_of_ascent {s : ℕ} (hs : 3 ≤ s)
    (h : seamIntegerGreedyRemainder (s + 1) + 2 ^ (s + 1) + 2 * s <
      4 * seamIntegerGreedyRemainder s) :
    LargestSkipLateAt (s + 1) := by
  by_contra hcon
  exact absurd (remainder_step_of_not_largestSkipLateAt hs hcon).2 (by omega)

/-- **The certificate, descent side.** -/
theorem largestSkipLateAt_succ_of_descent {s : ℕ} (hs : 3 ≤ s)
    (h : 4 * seamIntegerGreedyRemainder s <
      seamIntegerGreedyRemainder (s + 1) + 2 ^ (s + 1) + 4) :
    LargestSkipLateAt (s + 1) := by
  by_contra hcon
  exact absurd (remainder_step_of_not_largestSkipLateAt hs hcon).1 (by omega)

/-- **The certificate.**  A single scalar per row: if the one-step defect
`4 * R s - R (s+1) - 2 ^ (s+1)` leaves the window `[4, 2*s]`, row `s+1` has a
late largest false rank. -/
theorem largestSkipLateAt_succ_of_window_miss {s : ℕ} (hs : 3 ≤ s)
    (h : ¬ (seamIntegerGreedyRemainder (s + 1) + 2 ^ (s + 1) + 4 ≤
            4 * seamIntegerGreedyRemainder s ∧
          4 * seamIntegerGreedyRemainder s ≤
            seamIntegerGreedyRemainder (s + 1) + 2 ^ (s + 1) + 2 * s)) :
    LargestSkipLateAt (s + 1) := by
  by_contra hcon
  exact h (remainder_step_of_not_largestSkipLateAt hs hcon)

/-! ## 5. The sharp negative: the law alone cannot refute the forced run -/

/-- The abstract shape of the row law: a sequence obeying the same two-sided
recurrence the forced run imposes on `seamIntegerGreedyRemainder`. -/
def StepLaw (f : ℕ → ℕ) (N : ℕ) : Prop :=
  ∀ s : ℕ, N ≤ s →
    f (s + 1) + 2 ^ (s + 1) + 4 ≤ 4 * f s ∧ 4 * f s ≤ f (s + 1) + 2 ^ (s + 1) + 2 * s

/-- The forced run makes the concrete defect obey the law from `max N 3` on. -/
theorem stepLaw_of_forcedRun {N : ℕ} (h : ForcedRun N) :
    StepLaw seamIntegerGreedyRemainder (max N 3) := by
  intro s hs
  exact remainder_step_of_not_largestSkipLateAt (by omega)
    (h (s + 1) (by omega))

/-- **The no-go.**  The law is consistent: the explicit sequence `2 ^ s + 2`
obeys it at every row `s ≥ 3`.  So no contradiction can be extracted from the
row law alone — the forced run survives the recurrence. -/
theorem stepLaw_pow_add_two : StepLaw (fun s => 2 ^ s + 2) 3 := by
  intro s hs
  have hp : (2 : ℕ) ^ (s + 1) = 2 * 2 ^ s := by rw [pow_succ]; ring
  have hp2 : (2 : ℕ) ^ (s + 1 + 1) = 2 * 2 ^ (s + 1) := by rw [pow_succ]; ring
  simp only
  omega

/-- The no-go, packaged: a strictly positive solution of the law exists. -/
theorem exists_stepLaw : ∃ f : ℕ → ℕ, StepLaw f 3 ∧ ∀ s, 0 < f s :=
  ⟨fun s => 2 ^ s + 2, stepLaw_pow_add_two, fun s => by positivity⟩

/-- **The forced run in one equation.**  Under the forced run the whole tail of
the defect sequence is a *deterministic* quadrupling map, up to a correction
confined to the window `[4, 2*s]` — a window of width `2*s - 4` sitting inside
an a-priori range of size `2 ^ (s+2)`. -/
theorem forcedRun_defect_window {N : ℕ} (h : ForcedRun N) {s : ℕ} (hs : max N 3 ≤ s) :
    ∃ c : ℕ, 4 ≤ c ∧ c ≤ 2 * s ∧
      seamIntegerGreedyRemainder (s + 1) + 2 ^ (s + 1) + c =
        4 * seamIntegerGreedyRemainder s := by
  obtain ⟨h1, h2⟩ := stepLaw_of_forcedRun h s hs
  exact ⟨4 * seamIntegerGreedyRemainder s -
      (seamIntegerGreedyRemainder (s + 1) + 2 ^ (s + 1)),
    by omega, by omega, by omega⟩

/-! ## 6. Iterating the law backwards -/

/-- **The backward iteration.**  Any solution of the law is squeezed towards
`2 ^ s` by the rows above it: dividing through by `4 ^ k`, this reads
`f s ≤ f (s+k) / 4 ^ k + 2 ^ s * (1 - 2 ^ (-k)) + (s + k)`. -/
theorem stepLaw_iterate {f : ℕ → ℕ} {N : ℕ} (h : StepLaw f N) {s : ℕ} (hs : N ≤ s) :
    ∀ k : ℕ, 4 ^ k * f s + 2 ^ s * 2 ^ k + (s + k) ≤
      f (s + k) + 2 ^ s * 4 ^ k + (s + k) * 4 ^ k := by
  intro k
  induction k with
  | zero => simp
  | succ k ih =>
      have hstep : s + (k + 1) = s + k + 1 := by omega
      rw [hstep]
      have hlaw := (h (s + k) (by omega)).2
      have e1 : (4 : ℕ) ^ (k + 1) = 4 * 4 ^ k := by rw [pow_succ]; ring
      have e3 : (2 : ℕ) ^ (s + k + 1) = 2 * (2 ^ s * 2 ^ k) := by
        rw [pow_succ, pow_add]; ring
      have e4 : 4 ^ (k + 1) * f s = 4 * (4 ^ k * f s) := by rw [e1]; ring
      have e5 : (2 : ℕ) ^ s * 2 ^ (k + 1) = 2 * (2 ^ s * 2 ^ k) := by
        rw [pow_succ]; ring
      have e6 : (2 : ℕ) ^ s * 4 ^ (k + 1) = 4 * (2 ^ s * 4 ^ k) := by rw [e1]; ring
      have e7 : (s + k + 1) * 4 ^ (k + 1) = 4 * ((s + k) * 4 ^ k) + 4 * 4 ^ k := by
        rw [e1]; ring
      have e8 : (1 : ℕ) ≤ 4 ^ k := Nat.one_le_pow _ _ (by norm_num)
      omega

/-- **The pinning.**  If the forced run holds from `N` on *and* the defect stays
inside the size regime `R m ≤ 2 ^ (m+1)` measured at every computed row, then
the defect is squeezed to within `2*s + 1` of the single value `2 ^ s`, out of an
a-priori range of size `2 ^ (s+1)`.

The growth hypothesis is **not** proved here; see the module docstring. -/
theorem remainder_le_of_forcedRun_of_growth {N : ℕ} (h : ForcedRun N)
    (hg : ∀ m : ℕ, N ≤ m → seamIntegerGreedyRemainder m ≤ 2 ^ (m + 1))
    {s : ℕ} (hs : max N 3 ≤ s) :
    seamIntegerGreedyRemainder s ≤ 2 ^ s + 2 * s + 1 := by
  have hit := stepLaw_iterate (stepLaw_of_forcedRun h) hs s
  have hR : seamIntegerGreedyRemainder (s + s) ≤ 2 ^ (s + s + 1) := hg _ (by omega)
  have e1 : (2 : ℕ) ^ s * 2 ^ s = 4 ^ s := by
    rw [← pow_add, show s + s = 2 * s by omega, pow_mul]
    norm_num
  have e2 : (2 : ℕ) ^ (s + s + 1) = 2 * 4 ^ s := by
    have hss : (2 : ℕ) ^ (s + s) = 4 ^ s := by rw [← e1, pow_add]
    rw [pow_succ, hss]
    ring
  have expand : 4 ^ s * (2 ^ s + 2 * s + 1) =
      2 ^ s * 4 ^ s + (s + s) * 4 ^ s + 4 ^ s := by ring
  have key : 4 ^ s * seamIntegerGreedyRemainder s ≤ 4 ^ s * (2 ^ s + 2 * s + 1) := by
    omega
  exact Nat.le_of_mul_le_mul_left key (by positivity)

/-! ## 7. Iterating the law forwards -/

/-- **Forward iteration of the descent half, localised.**  If `LargestSkipLateAt`
fails on the whole window `[s+1, 2*s+2]`, the defect at row `s` cannot dip to
`2 ^ s + 1`: the descent would drive it below zero within `s + 2` further rows. -/
theorem remainder_ge_of_no_late_window {s : ℕ} (hs : 3 ≤ s)
    (h : ∀ t : ℕ, s ≤ t → t ≤ 2 * s + 1 → ¬ LargestSkipLateAt (t + 1)) :
    2 ^ s + 2 ≤ seamIntegerGreedyRemainder s := by
  rcases Nat.lt_or_ge (seamIntegerGreedyRemainder s) (2 ^ s + 2) with hlt | hge
  · exfalso
    have key : ∀ j : ℕ, j ≤ s + 2 →
        3 * seamIntegerGreedyRemainder (s + j) + 4 ^ j ≤ 3 * 2 ^ (s + j) + 4 := by
      intro j
      induction j with
      | zero =>
          intro _
          simp only [Nat.add_zero, pow_zero]
          omega
      | succ j ih =>
          intro hj
          have hprev := ih (by omega)
          have hlaw := (remainder_step_of_not_largestSkipLateAt (s := s + j) (by omega)
            (h (s + j) (by omega) (by omega))).1
          have e1 : (4 : ℕ) ^ (j + 1) = 4 * 4 ^ j := by rw [pow_succ]; ring
          have e2 : (2 : ℕ) ^ (s + j + 1) = 2 * 2 ^ (s + j) := by rw [pow_succ]; ring
          have e3 : s + (j + 1) = s + j + 1 := by omega
          rw [e3]
          omega
    have hbig := key (s + 2) le_rfl
    have e4 : (2 : ℕ) ^ (s + (s + 2)) = 4 ^ (s + 1) := by
      rw [show s + (s + 2) = 2 * (s + 1) by omega, pow_mul]
      norm_num
    have e5 : (4 : ℕ) ^ (s + 2) = 4 * 4 ^ (s + 1) := by
      rw [show s + 2 = s + 1 + 1 by omega, pow_succ]
      ring
    have e6 : (4 : ℕ) ^ 4 ≤ 4 ^ (s + 1) := Nat.pow_le_pow_right (by norm_num) (by omega)
    norm_num at e6
    omega
  · exact hge

/-- **The unconditional lower half of the pinning.**  Under the forced run the
defect never dips below `2 ^ s + 2`. -/
theorem remainder_ge_of_forcedRun {N : ℕ} (h : ForcedRun N) {s : ℕ} (hs : max N 3 ≤ s) :
    2 ^ s + 2 ≤ seamIntegerGreedyRemainder s :=
  remainder_ge_of_no_late_window (by omega) fun t h1 _ => h (t + 1) (by omega)

/-- **The window certificate.**  A single scalar: whenever the defect of row `s`
dips to `2 ^ s + 1`, some row of `[s+1, 2*s+2]` has a late largest false rank. -/
theorem exists_largestSkipLateAt_of_remainder_small {s : ℕ} (hs : 3 ≤ s)
    (h : seamIntegerGreedyRemainder s ≤ 2 ^ s + 1) :
    ∃ t : ℕ, s + 1 ≤ t ∧ t ≤ 2 * s + 2 ∧ LargestSkipLateAt t := by
  by_contra hcon
  have hall : ∀ t : ℕ, s ≤ t → t ≤ 2 * s + 1 → ¬ LargestSkipLateAt (t + 1) :=
    fun t h1 h2 hlate => hcon ⟨t + 1, by omega, by omega, hlate⟩
  have := remainder_ge_of_no_late_window hs hall
  omega

/-- **The band.**  Under the forced run, and inside the measured size regime,
the defect is confined to an interval of length `2*s` around `2 ^ s` — out of an
a-priori range of size `2 ^ (s+1)`. -/
theorem remainder_band_of_forcedRun_of_growth {N : ℕ} (h : ForcedRun N)
    (hg : ∀ m : ℕ, N ≤ m → seamIntegerGreedyRemainder m ≤ 2 ^ (m + 1))
    {s : ℕ} (hs : max N 3 ≤ s) :
    2 ^ s + 2 ≤ seamIntegerGreedyRemainder s ∧
      seamIntegerGreedyRemainder s ≤ 2 ^ s + 2 * s + 1 :=
  ⟨remainder_ge_of_forcedRun h hs, remainder_le_of_forcedRun_of_growth h hg hs⟩

/-! ## 8. Kernel-computable defects, and the certificate in action -/

/-- The concrete greedy defect, through `SkipD3`'s kernel-computable row word. -/
def remOf (s : ℕ) : ℕ :=
  seamSubsetTarget s - weightedBoolSum (SkipD3.wgt s 2 (s - 2)) (SkipD3.gb s)

theorem remOf_eq (s : ℕ) : seamIntegerGreedyRemainder s = remOf s := by
  rw [remOf, ← SkipD3.seamWeights_eq_wgt, SkipD3.gb_eq]
  rfl

theorem largestSkipLateAt_succ_of_remOf_ascent {s : ℕ} (hs : 3 ≤ s)
    (h : remOf (s + 1) + 2 ^ (s + 1) + 2 * s < 4 * remOf s) :
    LargestSkipLateAt (s + 1) := by
  refine largestSkipLateAt_succ_of_ascent hs ?_
  rw [remOf_eq, remOf_eq]
  exact h

theorem largestSkipLateAt_succ_of_remOf_descent {s : ℕ} (hs : 3 ≤ s)
    (h : 4 * remOf s < remOf (s + 1) + 2 ^ (s + 1) + 4) :
    LargestSkipLateAt (s + 1) := by
  refine largestSkipLateAt_succ_of_descent hs ?_
  rw [remOf_eq, remOf_eq]
  exact h

section Certificates

set_option maxRecDepth 8000000

theorem lateAt_8 : LargestSkipLateAt 8 :=
  largestSkipLateAt_succ_of_remOf_descent (s := 7) (by norm_num) (by decide +kernel)

theorem lateAt_14 : LargestSkipLateAt 14 :=
  largestSkipLateAt_succ_of_remOf_ascent (s := 13) (by norm_num) (by decide +kernel)

theorem lateAt_15 : LargestSkipLateAt 15 :=
  largestSkipLateAt_succ_of_remOf_descent (s := 14) (by norm_num) (by decide +kernel)

theorem lateAt_20 : LargestSkipLateAt 20 :=
  largestSkipLateAt_succ_of_remOf_ascent (s := 19) (by norm_num) (by decide +kernel)

theorem lateAt_26 : LargestSkipLateAt 26 :=
  largestSkipLateAt_succ_of_remOf_ascent (s := 25) (by norm_num) (by decide +kernel)

theorem lateAt_32 : LargestSkipLateAt 32 :=
  largestSkipLateAt_succ_of_remOf_ascent (s := 31) (by norm_num) (by decide +kernel)

theorem lateAt_38 : LargestSkipLateAt 38 :=
  largestSkipLateAt_succ_of_remOf_ascent (s := 37) (by norm_num) (by decide +kernel)

theorem lateAt_102 : LargestSkipLateAt 102 :=
  largestSkipLateAt_succ_of_remOf_ascent (s := 101) (by norm_num) (by decide +kernel)

theorem lateAt_401 : LargestSkipLateAt 401 :=
  largestSkipLateAt_succ_of_remOf_ascent (s := 400) (by norm_num) (by decide +kernel)

/-- A scalar-interface certificate at row `1500`.  The two remainders used by
the certificate are computed from the concrete greedy words; the point is the
form of the implication, not an extension of the corpus's certified range. -/
theorem lateAt_1500 : LargestSkipLateAt 1500 :=
  largestSkipLateAt_succ_of_remOf_descent (s := 1499) (by norm_num) (by decide +kernel)

/-- …and at row `1501`. -/
theorem lateAt_1501 : LargestSkipLateAt 1501 :=
  largestSkipLateAt_succ_of_remOf_ascent (s := 1500) (by norm_num) (by decide +kernel)

end Certificates

/-! ## 9. Non-vacuity -/

section NonVacuity

set_option maxRecDepth 8000000

/-- The hypothesis of `remainder_step_of_top_mem` is satisfiable: the brand-new
top rank `11` of row `12` really is selected. -/
theorem top_mem_eleven : (11 : ℕ) ∈ seamWordSupport (seamGreedyWord 12) := by
  rw [SkipD3.mem_support_iff (by norm_num) (by norm_num)]
  decide +kernel

/-- …so the row law fires at a concrete row. -/
theorem remainder_step_eleven :
    seamIntegerGreedyRemainder 12 + 2 ^ 12 + 4 ≤ 4 * seamIntegerGreedyRemainder 11 ∧
      4 * seamIntegerGreedyRemainder 11 ≤ seamIntegerGreedyRemainder 12 + 2 ^ 12 + 2 * 11 :=
  remainder_step_of_top_mem (by norm_num) top_mem_eleven

/-- The hypothesis of `remainder_step_of_not_largestSkipLateAt` is satisfiable:
row `12` is one of the four rows of `[5, 3000]` at which `LargestSkipLateAt`
genuinely fails.  Every rank of its late zone — `9`, `10`, `11` — is selected. -/
theorem not_largestSkipLateAt_twelve : ¬ LargestSkipLateAt 12 := by
  rintro ⟨d, ⟨hd2, hds, hdnot, -⟩, hlate⟩
  refine hdnot ?_
  have h9 : 9 ≤ d := by omega
  have h12 : d < 12 := hds
  rw [SkipD3.mem_support_iff (by omega) (by omega)]
  interval_cases d <;> decide +kernel

/-- …so the row law in `#257` vocabulary fires at a concrete row too. -/
theorem remainder_step_eleven' :
    seamIntegerGreedyRemainder 12 + 2 ^ 12 + 4 ≤ 4 * seamIntegerGreedyRemainder 11 ∧
      4 * seamIntegerGreedyRemainder 11 ≤ seamIntegerGreedyRemainder 12 + 2 ^ 12 + 2 * 11 :=
  remainder_step_of_not_largestSkipLateAt (by norm_num) not_largestSkipLateAt_twelve

/-- The hypothesis of `exists_largestSkipLateAt_of_remainder_small` is
satisfiable: row `7` has defect `3`, far below `2 ^ 7 + 1`. -/
theorem remainder_small_seven : seamIntegerGreedyRemainder 7 ≤ 2 ^ 7 + 1 := by
  rw [remOf_eq]
  decide +kernel

/-- …and the window certificate then produces a late largest false rank
somewhere in `[8, 16]` — `lateAt_8` says it is already at the left end. -/
theorem exists_late_in_window_seven :
    ∃ t : ℕ, 8 ≤ t ∧ t ≤ 16 ∧ LargestSkipLateAt t :=
  exists_largestSkipLateAt_of_remainder_small (by norm_num) remainder_small_seven

/-- The defect window of `forcedRun_defect_window` is realised, with room to
spare, at the same row: `4 * R 11 - R 12 - 2 ^ 12 = 8`, inside `[4, 22]`. -/
theorem defect_window_eleven :
    ∃ c : ℕ, 4 ≤ c ∧ c ≤ 2 * 11 ∧
      seamIntegerGreedyRemainder 12 + 2 ^ 12 + c = 4 * seamIntegerGreedyRemainder 11 := by
  obtain ⟨h1, h2⟩ := remainder_step_eleven'
  exact ⟨4 * seamIntegerGreedyRemainder 11 - (seamIntegerGreedyRemainder 12 + 2 ^ 12),
    by omega, by omega, by omega⟩

end NonVacuity

end BitR1

end Erdos249257
