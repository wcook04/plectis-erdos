/-
Copyright (c) 2026 Will Cook. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Will Cook
-/
import ErdosProblems.Skip.D2
import ErdosProblems.Bit.Corr1
import ErdosProblems.Bit.R2

/-!
# Rem C4: a refinement of the late-skip remainder bound

`AngleD2.half_mem_iff_unboundedLargestSkipLate` makes the `1/2` endpoint of
Erdős `#257` equivalent to `LargestSkipLateAt s` at cofinally many rows, and
`Bit/R2` shows that `seamIntegerGreedyRemainder s ≤ 2 ^ s` at cofinally many
rows is sufficient.

This file does **not** supply the first late-skip size law.  The imported
theorem `three_mul_remainder_lt_exactLateGap` already proves the main
three-times bound below (with the removable side condition `5 ≤ s`), and
`Bit/R2.three_mul_remainder_lt_of_largestSkipLateAt` already gives

    `3 * ρ s < 7 * 2 ^ s + 4`

on every late row.  The genuine quantitative refinement proved here is
`six_mul_remainder_lt_of_largestSkipLate`:

    `6 * ρ s < 13 * 2 ^ s + 8`.

Thus the late-row constant improves from approximately `7/3` to `13/6`.
No bound in this file is unconditional at an arbitrary row, and no theorem
here decides whether the required rows occur cofinally.

## The mechanism

Let `D` be the largest false rank of row `s` (`IsLargestFalseRank`).  Two
exact facts combine:

* `greedy_skip_tail` — a purely list-level property of the descending integer
  greedy.  If position `k` is rejected and every later position is accepted,
  then the *final* remainder plus the entire accepted tail is still strictly
  below the rejected weight.  Transported to the seam word this is
  `remainder_add_tail_lt_weight`:

      `ρ s + Σ_{d=D+1}^{s-1} w s d  <  w s D`.

* `truncatedMersenneWeight_top_band` — inside the late zone `2 s < 3 d` the
  floor `⌊4 ^ s / (2 ^ d - 1)⌋` collapses to the two-term binary value
  `2 ^ (2s-d) + 4 ^ (s-d)`, so the tail telescopes exactly
  (`sum_seamWeightsFrom_top_band`).

Substituting the closed form makes the `2 ^ (2s-D)` head cancel, and what
survives is a bound of size `2 ^ (s+1)`, not `4 ^ s`.

## Main results

* `remainder_add_tail_lt_weight` — the exact seam skip law (no side condition
  beyond `D` being the largest false rank).
* `three_mul_remainder_lt_of_lateSkip` — a reproving of the imported graded
  form without its side condition `5 ≤ s`:
  `3 ρ s < 3 · 2 ^ (s+1) + 2 · 4 ^ (s-D) + 4`.
* `remainder_lt_of_lateSkip` — `ρ s < 2 ^ (s+1) + 4 ^ (s-D)`.
* `remainder_lt_of_terminal_skip` — at gap `1` (terminal rank skipped) this is
  `ρ s < 2 ^ (s+1) + 4`; the rejected weight is exactly
  `2 ^ (s+1) + 4`.
* `six_mul_remainder_lt_of_largestSkipLate` — the strongest constant-factor
  bound in this file, `6 ρ s < 13 · 2 ^ s + 8`.
* `remainder_lt_two_pow_succ_add_of_largestSkipLate` and
  `remainder_lt_of_largestSkipLate` — weaker corollaries.  On every row where
  the conditional predicate `LargestSkipLateAt` holds, they give

      `ρ s < 2 ^ (s+1) + 2 ^ (s-2) < 3 · 2 ^ s`.

* `remainder_below_three_halfPoint_cofinally_of_half_mem`, `half_mem_sandwich`
  — a necessary implication for `#257`, already obtainable from
  `Skip/D2` and the stronger imported `Bit/R2` ceiling.  It does not prove
  either the sufficient cofinal condition or membership of `1/2`.

## Certificates (anti-vacuity)

`seamIntegerGreedyRemainder_fourteen` computes `ρ 14 = 392` outright;
`isLargestFalseRank_fourteen` proves the terminal rank `13` is the largest
false rank of row `14`, so the hypotheses of every conditional statement above
have a concrete instance, and `remainder_fourteen_lt_sharp`, `remainder_fourteen_lt`,
`remainder_twenty_lt` are their concrete numeric instances.
-/

namespace ErdosProblems.RemC4

open Erdos249257
open Erdos249257.HalfCylinderIntegerGreedy

/-! ## The exact truncated weight in the top band `2 * s < 3 * d` -/

/-- In the top band `2 * s < 3 * d` (with `d < s`) the truncated Mersenne
weight collapses to a two-term binary value:
`⌊4 ^ s / (2 ^ d - 1)⌋ = 2 ^ (2 * s - d) + 4 ^ (s - d)`. -/
theorem truncatedMersenneWeight_top_band
    {s d : ℕ} (hd2 : 2 ≤ d) (hds : d < s) (hband : 2 * s < 3 * d) :
    truncatedMersenneWeight s d = 2 ^ (2 * s - d) + 4 ^ (s - d) := by
  have hb : 2 * (s - d) = 2 * s - 2 * d := by omega
  set b : ℕ := 2 * (s - d) with hbdef
  have hb2 : 2 ≤ b := by omega
  have hbk : b < d := by omega
  have hsum : 2 * s = 2 * d + b := by omega
  have hak : 2 * s - d = d + b := by omega
  have hfour : (4 : ℕ) ^ (s - d) = 2 ^ b := by
    rw [hbdef, pow_mul]
    norm_num
  have h4s : (4 : ℕ) ^ s = 2 ^ (2 * s) := by
    rw [pow_mul]; norm_num
  have hone : 1 ≤ (2 : ℕ) ^ d := Nat.one_le_two_pow
  -- the key exact multiplication
  have hkey : (2 ^ d - 1) * (2 ^ (d + b) + 2 ^ b) + 2 ^ b = 2 ^ (2 * d + b) := by
    have h1 : (2 : ℕ) ^ (d + b) = 2 ^ d * 2 ^ b := by rw [← pow_add]
    have h2 : (2 : ℕ) ^ (2 * d + b) = 2 ^ d * (2 ^ d * 2 ^ b) := by
      rw [pow_add, two_mul, pow_add, mul_assoc]
    have hstep : ((2 : ℕ) ^ d - 1) * (2 ^ d * 2 ^ b + 2 ^ b)
        = 2 ^ d * (2 ^ d * 2 ^ b + 2 ^ b) - (2 ^ d * 2 ^ b + 2 ^ b) := by
      rw [Nat.sub_mul, one_mul]
    have hexpand : (2 : ℕ) ^ d * (2 ^ d * 2 ^ b + 2 ^ b)
        = 2 ^ d * (2 ^ d * 2 ^ b) + 2 ^ d * 2 ^ b := by ring
    have hle1 : (2 : ℕ) ^ b ≤ 2 ^ d * 2 ^ b := by
      calc (2 : ℕ) ^ b = 1 * 2 ^ b := (one_mul _).symm
        _ ≤ 2 ^ d * 2 ^ b := Nat.mul_le_mul_right _ hone
    have hle2 : (2 : ℕ) ^ d * 2 ^ b ≤ 2 ^ d * (2 ^ d * 2 ^ b) := by
      calc (2 : ℕ) ^ d * 2 ^ b = 2 ^ d * (1 * 2 ^ b) := by rw [one_mul]
        _ ≤ 2 ^ d * (2 ^ d * 2 ^ b) :=
          Nat.mul_le_mul_left _ (Nat.mul_le_mul_right _ hone)
    rw [h1, h2, hstep, hexpand]
    omega
  have hsmall : (2 : ℕ) ^ b < 2 ^ d - 1 := by
    have h1 : (2 : ℕ) ^ b ≤ 2 ^ (d - 1) := Nat.pow_le_pow_right (by norm_num) (by omega)
    have h2 : (2 : ℕ) ^ (d - 1) + 2 ^ (d - 1) = 2 ^ d := by
      rw [← two_mul, ← pow_succ']
      congr 1
      omega
    have h3 : (2 : ℕ) ≤ 2 ^ (d - 1) := by
      calc (2 : ℕ) = 2 ^ 1 := (pow_one 2).symm
        _ ≤ 2 ^ (d - 1) := Nat.pow_le_pow_right (by norm_num) (by omega)
    omega
  have hcomm : (2 ^ (d + b) + 2 ^ b) * (2 ^ d - 1)
      = (2 ^ d - 1) * (2 ^ (d + b) + 2 ^ b) := Nat.mul_comm _ _
  have hdist : (2 ^ d - 1) * (2 ^ (d + b) + 2 ^ b + 1)
      = (2 ^ d - 1) * (2 ^ (d + b) + 2 ^ b) + (2 ^ d - 1) := by
    rw [Nat.mul_add, Nat.mul_one]
  rw [truncatedMersenneWeight, h4s, hak, hfour, hsum]
  refine Nat.div_eq_of_lt_le ?_ ?_
  · calc (2 ^ (d + b) + 2 ^ b) * (2 ^ d - 1)
        = (2 ^ d - 1) * (2 ^ (d + b) + 2 ^ b) := hcomm
      _ ≤ (2 ^ d - 1) * (2 ^ (d + b) + 2 ^ b) + 2 ^ b := Nat.le_add_right _ _
      _ = 2 ^ (2 * d + b) := hkey
  · calc (2 : ℕ) ^ (2 * d + b)
        = (2 ^ d - 1) * (2 ^ (d + b) + 2 ^ b) + 2 ^ b := hkey.symm
      _ < (2 ^ d - 1) * (2 ^ (d + b) + 2 ^ b) + (2 ^ d - 1) :=
          Nat.add_lt_add_left hsmall _
      _ = (2 ^ d - 1) * (2 ^ (d + b) + 2 ^ b + 1) := hdist.symm
      _ = (2 ^ (d + b) + 2 ^ b + 1) * (2 ^ d - 1) := Nat.mul_comm _ _

/-! ## Closed form for the tail of the weight word inside the top band -/

/-- Tail sum of the seam weight word from rank `k` upward, in the top band. -/
theorem sum_seamWeightsFrom_top_band (s : ℕ) :
    ∀ j k : ℕ, k + j = s → 2 ≤ k → 2 * s < 3 * k →
      3 * (seamWeightsFrom s k).sum + 3 * 2 ^ (s + 1) + 4
        = 3 * 2 ^ (2 * s - k + 1) + 4 ^ (s - k + 1) := by
  intro j
  induction j with
  | zero =>
      intro k hk _ _
      have hks : k = s := by omega
      subst hks
      rw [seamWeightsFrom_eq_nil (le_refl k)]
      simp only [List.sum_nil, Nat.mul_zero, Nat.zero_add]
      rw [show 2 * k - k + 1 = k + 1 by omega, show k - k + 1 = 1 by omega]
      norm_num
  | succ j ih =>
      intro k hk hk2 hband
      have hks : k < s := by omega
      have hband' : 2 * s < 3 * (k + 1) := by omega
      have hih := ih (k + 1) (by omega) (by omega) hband'
      have hw := truncatedMersenneWeight_top_band (s := s) (d := k) hk2 hks hband
      rw [seamWeightsFrom_eq_cons hks, List.sum_cons, hw]
      have he1 : 2 * s - (k + 1) + 1 = 2 * s - k := by omega
      have he2 : s - (k + 1) + 1 = s - k := by omega
      rw [he1, he2] at hih
      have hp1 : (2 : ℕ) ^ (2 * s - k + 1) = 2 * 2 ^ (2 * s - k) := by
        rw [pow_succ]; ring
      have hp2 : (4 : ℕ) ^ (s - k + 1) = 4 * 4 ^ (s - k) := by
        rw [pow_succ]; ring
      rw [hp1, hp2]
      omega

/-! ## Descending greedy: state at a skipped position -/

theorem integerGreedyRemainder_cons (w : ℕ) (ws : List ℕ) (C : ℕ) :
    integerGreedyRemainder (w :: ws) C
      = if w ≤ C then integerGreedyRemainder ws (C - w)
        else integerGreedyRemainder ws C := by
  unfold integerGreedyRemainder
  rw [integerGreedyBits]
  split_ifs with hw
  · have hval : weightedBoolSum (w :: ws) (true :: integerGreedyBits ws (C - w))
        = w + weightedBoolSum ws (integerGreedyBits ws (C - w)) := rfl
    rw [hval]
    omega
  · rfl

/-- If the descending greedy accepts every weight, the remainder is exactly
the deficit `C - Σ`. -/
theorem greedy_allTrue :
    ∀ (l : List ℕ) (C : ℕ),
      (∀ (j : ℕ) (b : Bool), (integerGreedyBits l C)[j]? = some b → b = true) →
      l.sum ≤ C ∧ integerGreedyRemainder l C = C - l.sum := by
  intro l
  induction l with
  | nil =>
      intro C _
      refine ⟨by simp, ?_⟩
      simp [integerGreedyRemainder, weightedBoolSum]
  | cons w ws ih =>
      intro C hall
      have hw : w ≤ C := by
        by_contra hw
        have h0 : (integerGreedyBits (w :: ws) C)[0]? = some false := by
          rw [integerGreedyBits, if_neg hw]
          simp
        have := hall 0 false h0
        exact Bool.false_ne_true this
      have htail : ∀ (j : ℕ) (b : Bool),
          (integerGreedyBits ws (C - w))[j]? = some b → b = true := by
        intro j b hj
        refine hall (j + 1) b ?_
        rw [integerGreedyBits, if_pos hw]
        simpa using hj
      obtain ⟨hsum, hrem⟩ := ih (C - w) htail
      refine ⟨?_, ?_⟩
      · rw [List.sum_cons]; omega
      · rw [integerGreedyRemainder_cons, if_pos hw, hrem, List.sum_cons]
        omega

/-- **The skipped-position law.**  If the descending greedy rejects the weight
at position `k` and accepts every weight after it, then the final remainder
plus the whole accepted tail is still strictly below the rejected weight. -/
theorem greedy_skip_tail :
    ∀ (l : List ℕ) (C k wk : ℕ),
      l[k]? = some wk →
      (integerGreedyBits l C)[k]? = some false →
      (∀ (j : ℕ) (b : Bool), k < j →
        (integerGreedyBits l C)[j]? = some b → b = true) →
      integerGreedyRemainder l C + (l.drop (k + 1)).sum < wk := by
  intro l
  induction l with
  | nil => intro C k wk hk _ _; simp at hk
  | cons w ws ih =>
      intro C k wk hk hfalse htrue
      cases k with
      | zero =>
          have hwk : w = wk := by simpa using hk
          subst hwk
          have hw : ¬ (w ≤ C) := by
            intro hw
            have hb : (integerGreedyBits (w :: ws) C)[0]? = some true := by
              rw [integerGreedyBits, if_pos hw]
              simp
            rw [hb] at hfalse
            simp at hfalse
          have hall : ∀ (j : ℕ) (b : Bool),
              (integerGreedyBits ws C)[j]? = some b → b = true := by
            intro j b hj
            refine htrue (j + 1) b (by omega) ?_
            rw [integerGreedyBits, if_neg hw]
            simpa using hj
          obtain ⟨hsum, hrem⟩ := greedy_allTrue ws C hall
          rw [integerGreedyRemainder_cons, if_neg hw, hrem]
          simp only [List.drop_succ_cons, List.drop_zero]
          omega
      | succ k =>
          have hk' : ws[k]? = some wk := by simpa using hk
          by_cases hw : w ≤ C
          · have hbits : integerGreedyBits (w :: ws) C
                = true :: integerGreedyBits ws (C - w) := by
              rw [integerGreedyBits, if_pos hw]
            rw [hbits] at hfalse htrue
            have hfalse' : (integerGreedyBits ws (C - w))[k]? = some false := by
              simpa using hfalse
            have htrue' : ∀ (j : ℕ) (b : Bool), k < j →
                (integerGreedyBits ws (C - w))[j]? = some b → b = true := by
              intro j b hj hb
              exact htrue (j + 1) b (by omega) (by simpa using hb)
            have hrec := ih (C - w) k wk hk' hfalse' htrue'
            rw [integerGreedyRemainder_cons, if_pos hw]
            simpa using hrec
          · have hbits : integerGreedyBits (w :: ws) C
                = false :: integerGreedyBits ws C := by
              rw [integerGreedyBits, if_neg hw]
            rw [hbits] at hfalse htrue
            have hfalse' : (integerGreedyBits ws C)[k]? = some false := by
              simpa using hfalse
            have htrue' : ∀ (j : ℕ) (b : Bool), k < j →
                (integerGreedyBits ws C)[j]? = some b → b = true := by
              intro j b hj hb
              exact htrue (j + 1) b (by omega) (by simpa using hb)
            have hrec := ih C k wk hk' hfalse' htrue'
            rw [integerGreedyRemainder_cons, if_neg hw]
            simpa using hrec

/-! ## Positional description of the seam weight word -/

theorem seamWeightsFrom_getElem? (s : ℕ) :
    ∀ (j k : ℕ), k + j < s →
      (seamWeightsFrom s k)[j]? = some (truncatedMersenneWeight s (k + j)) := by
  intro j
  induction j with
  | zero =>
      intro k hk
      rw [seamWeightsFrom_eq_cons (by omega : k < s)]
      simp
  | succ j ih =>
      intro k hk
      rw [seamWeightsFrom_eq_cons (by omega : k < s)]
      rw [List.getElem?_cons_succ, ih (k + 1) (by omega)]
      congr 2
      omega

theorem seamWeightsFrom_drop (s : ℕ) :
    ∀ (j k : ℕ), (seamWeightsFrom s k).drop j = seamWeightsFrom s (k + j) := by
  intro j
  induction j with
  | zero => intro k; simp
  | succ j ih =>
      intro k
      by_cases hk : k < s
      · rw [seamWeightsFrom_eq_cons hk, List.drop_succ_cons, ih (k + 1)]
        congr 1
        omega
      · rw [seamWeightsFrom_eq_nil (by omega), seamWeightsFrom_eq_nil (by omega)]
        simp

/-! ## Bridge: seam word support versus greedy bits -/

theorem seamGreedyWord_getElem? {s j : ℕ} (hj : j < s - 2) :
    (integerGreedyBits (seamWeights s) (seamSubsetTarget s))[j]?
      = some ((seamGreedyWord s) ⟨j, hj⟩) := by
  have hlen : (integerGreedyBits (seamWeights s) (seamSubsetTarget s)).length
      = s - 2 := by
    rw [integerGreedyBits_length, seamWeights_length_eq]
  rw [List.getElem?_eq_getElem (by omega)]
  congr 1

theorem mem_seamWordSupport_iff_greedyBit {s d : ℕ} (hd2 : 2 ≤ d) (hds : d < s) :
    d ∈ seamWordSupport (seamGreedyWord s) ↔
      (integerGreedyBits (seamWeights s) (seamSubsetTarget s))[d - 2]?
        = some true := by
  have hj : d - 2 < s - 2 := by omega
  rw [seamGreedyWord_getElem? hj]
  constructor
  · intro hmem
    obtain ⟨i, hi, hdi⟩ := mem_seamWordSupport_iff.mp hmem
    have hieq : i = ⟨d - 2, hj⟩ := by
      apply Fin.ext
      change (i : ℕ) = d - 2
      omega
    rw [hieq] at hi
    rw [hi]
  · intro h
    have hval : (seamGreedyWord s) ⟨d - 2, hj⟩ = true := by
      simpa using h
    refine mem_seamWordSupport_iff.mpr ⟨⟨d - 2, hj⟩, hval, ?_⟩
    change d = (d - 2) + 2
    omega

/-! ## The exact skip law for the seam greedy -/

/-- **The seam skip law.**  If `D` is the largest false rank of row `s`, then
the final greedy remainder plus the entire accepted suffix `D+1,…,s-1` is
still strictly below the one weight the greedy could not afford at `D`. -/
theorem remainder_add_tail_lt_weight
    {s D : ℕ} (hD : IsLargestFalseRank (seamGreedyWord s) D) :
    seamIntegerGreedyRemainder s + (seamWeightsFrom s (D + 1)).sum
      < truncatedMersenneWeight s D := by
  obtain ⟨hd2, hds, hdnot, hfull⟩ := hD
  have hj : D - 2 < s - 2 := by omega
  have hk : (seamWeights s)[D - 2]? = some (truncatedMersenneWeight s D) := by
    have hget := seamWeightsFrom_getElem? s (D - 2) 2 (by omega)
    rw [show (2 : ℕ) + (D - 2) = D by omega] at hget
    rw [seamWeights]
    exact hget
  have hne : (integerGreedyBits (seamWeights s) (seamSubsetTarget s))[D - 2]?
      ≠ some true := by
    intro h
    exact hdnot ((mem_seamWordSupport_iff_greedyBit hd2 hds).mpr h)
  have hbitfalse :
      (integerGreedyBits (seamWeights s) (seamSubsetTarget s))[D - 2]?
        = some false := by
    rw [seamGreedyWord_getElem? hj] at hne ⊢
    rcases Bool.eq_false_or_eq_true ((seamGreedyWord s) ⟨D - 2, hj⟩) with h | h
    · rw [h] at hne; exact absurd rfl hne
    · rw [h]
  have hlen : (integerGreedyBits (seamWeights s) (seamSubsetTarget s)).length
      = s - 2 := by
    rw [integerGreedyBits_length, seamWeights_length_eq]
  have htrue : ∀ (j : ℕ) (b : Bool), D - 2 < j →
      (integerGreedyBits (seamWeights s) (seamSubsetTarget s))[j]? = some b →
      b = true := by
    intro j b hjgt hb
    have hjlt : j < s - 2 := by
      by_contra hcon
      rw [List.getElem?_eq_none (by omega)] at hb
      exact absurd hb (by simp)
    have hmem := hfull (j + 2) (by omega) (by omega)
    have hbit := (mem_seamWordSupport_iff_greedyBit (by omega) (by omega)).mp hmem
    rw [show j + 2 - 2 = j by omega] at hbit
    rw [hbit] at hb
    simpa using hb.symm
  have hmain := greedy_skip_tail (seamWeights s) (seamSubsetTarget s) (D - 2)
    (truncatedMersenneWeight s D) hk hbitfalse htrue
  have hdrop : (seamWeights s).drop (D - 2 + 1) = seamWeightsFrom s (D + 1) := by
    rw [seamWeights, seamWeightsFrom_drop]
    congr 1
    omega
  rw [hdrop] at hmain
  exact hmain

/-! ## Conditional quantitative bounds -/

/-- **PROVED, conditional.**  A late largest false rank `D` (`2s < 3D`)
implies the displayed upper bound.  The imported
`three_mul_remainder_lt_exactLateGap` already proves the same conclusion under
the additional side condition `5 ≤ s`. -/
theorem three_mul_remainder_lt_of_lateSkip
    {s D : ℕ} (hD : IsLargestFalseRank (seamGreedyWord s) D)
    (hband : 2 * s < 3 * D) :
    3 * seamIntegerGreedyRemainder s
      < 3 * 2 ^ (s + 1) + 2 * 4 ^ (s - D) + 4 := by
  have hd2 : 2 ≤ D := hD.1
  have hds : D < s := hD.2.1
  have hlt := remainder_add_tail_lt_weight hD
  rw [truncatedMersenneWeight_top_band hd2 hds hband] at hlt
  have hsum := sum_seamWeightsFrom_top_band s (s - (D + 1)) (D + 1)
    (by omega) (by omega) (by omega)
  rw [show 2 * s - (D + 1) + 1 = 2 * s - D by omega,
    show s - (D + 1) + 1 = s - D by omega] at hsum
  omega

/-- **PROVED, conditional.**  Division-free repackaging: a late largest false
rank `D` puts the seam greedy remainder strictly below
`2 ^ (s + 1) + 4 ^ (s - D)`. -/
theorem remainder_lt_of_lateSkip
    {s D : ℕ} (hD : IsLargestFalseRank (seamGreedyWord s) D)
    (hband : 2 * s < 3 * D) :
    seamIntegerGreedyRemainder s < 2 ^ (s + 1) + 4 ^ (s - D) := by
  have hds : D < s := hD.2.1
  have h := three_mul_remainder_lt_of_lateSkip hD hband
  have hfour : (4 : ℕ) ≤ 4 ^ (s - D) := by
    calc (4 : ℕ) = 4 ^ 1 := (pow_one 4).symm
      _ ≤ 4 ^ (s - D) := Nat.pow_le_pow_right (by norm_num) (by omega)
  omega

/-- **PROVED, conditional.**  If the greedy skips the terminal rank `s - 1`,
the remainder is below `2 ^ (s+1) + 4`. -/
theorem remainder_lt_of_terminal_skip
    {s : ℕ} (hD : IsLargestFalseRank (seamGreedyWord s) (s - 1)) (hs : 5 ≤ s) :
    seamIntegerGreedyRemainder s < 2 ^ (s + 1) + 4 := by
  have hband : 2 * s < 3 * (s - 1) := by omega
  have h := three_mul_remainder_lt_of_lateSkip hD hband
  rw [show s - (s - 1) = 1 by omega] at h
  norm_num at h
  omega

/-- **PROVED, conditional; strongest constant here.**  On every row where
`LargestSkipLateAt` holds,
`6 * seamIntegerGreedyRemainder s < 13 * 2 ^ s + 8`.
This improves the imported `Bit/R2` late-row ceiling from approximately
`(7/3) * 2 ^ s` to approximately `(13/6) * 2 ^ s`.  It does not establish
that such rows occur cofinally. -/
theorem six_mul_remainder_lt_of_largestSkipLate
    {s : ℕ} (h : LargestSkipLateAt s) :
    6 * seamIntegerGreedyRemainder s < 13 * 2 ^ s + 8 := by
  obtain ⟨D, hD, hband⟩ := h
  have hd2 : 2 ≤ D := hD.1
  have hds : D < s := hD.2.1
  have hmain := three_mul_remainder_lt_of_lateSkip hD hband
  have hpow : (4 : ℕ) ^ (s - D) ≤ 2 ^ (s - 2) := by
    have h2 : (4 : ℕ) ^ (s - D) = 2 ^ (2 * (s - D)) := by
      rw [pow_mul]; norm_num
    rw [h2]
    exact Nat.pow_le_pow_right (by norm_num) (by omega)
  have hps : (2 : ℕ) ^ (s + 1) = 2 * 2 ^ s := by rw [pow_succ]; ring
  have hps2 : (2 : ℕ) ^ s = 2 ^ (s - 2) * 4 := by
    rw [show (4 : ℕ) = 2 ^ 2 by norm_num, ← pow_add]
    congr 1
    omega
  omega

/-- **PROVED, conditional; weaker corollary.**  A late row has remainder below
`3 * 2 ^ s`.  This is weaker than both the preceding `13/6` bound and the
imported `Bit/R2` `7/3` ceiling. -/
theorem remainder_lt_of_largestSkipLate
    {s : ℕ} (h : LargestSkipLateAt s) :
    seamIntegerGreedyRemainder s < 3 * 2 ^ s := by
  obtain ⟨D, hD, _⟩ := h
  have hd2 : 2 ≤ D := hD.1
  have hds : D < s := hD.2.1
  have h6 := six_mul_remainder_lt_of_largestSkipLate ⟨D, hD, ‹2 * s < 3 * D›⟩
  have hbig : (8 : ℕ) ≤ 2 ^ s := by
    calc (8 : ℕ) = 2 ^ 3 := by norm_num
      _ ≤ 2 ^ s := Nat.pow_le_pow_right (by norm_num) (by omega)
  omega

/-- **PROVED, conditional; weaker corollary.**  On every late row the seam
greedy remainder is below `2 ^ (s + 1) + 2 ^ (s - 2)`, i.e. below
`2.25 · 2 ^ s`.  The `13/6` bound above is stronger. -/
theorem remainder_lt_two_pow_succ_add_of_largestSkipLate
    {s : ℕ} (h : LargestSkipLateAt s) :
    seamIntegerGreedyRemainder s < 2 ^ (s + 1) + 2 ^ (s - 2) := by
  obtain ⟨D, hD, hband⟩ := h
  have hd2 : 2 ≤ D := hD.1
  have hds : D < s := hD.2.1
  have hmain := remainder_lt_of_lateSkip hD hband
  have hpow : (4 : ℕ) ^ (s - D) ≤ 2 ^ (s - 2) := by
    have h2 : (4 : ℕ) ^ (s - D) = 2 ^ (2 * (s - D)) := by
      rw [pow_mul]; norm_num
    rw [h2]
    exact Nat.pow_le_pow_right (by norm_num) (by omega)
  omega

/-! ## What this says about Erdős `#257` -/

/-- **PROVED implication, not a resolution of `#257`.**  If `1/2` lies in the
Mersenne achievement set then the seam greedy remainder is below
`3 · 2 ^ s` at cofinally many rows.  This conclusion already follows from
`Skip/D2` and the stronger imported `Bit/R2` late-row ceiling. -/
theorem remainder_below_three_halfPoint_cofinally_of_half_mem
    (h : (1 / 2 : ℝ) ∈ mersenneAchievementSet) :
    ∀ N : ℕ, ∃ s : ℕ, N ≤ s ∧ seamIntegerGreedyRemainder s < 3 * 2 ^ s := by
  intro N
  obtain ⟨s, hsN, hlate⟩ := AngleD2.half_mem_iff_unboundedLargestSkipLate.mp h N
  exact ⟨s, hsN, remainder_lt_of_largestSkipLate hlate⟩

/-- **PROVED pair of implications, neither premise discharged.**  `Bit/R2`
proves that `ρ s ≤ 2 ^ s` cofinally is sufficient for membership of `1/2`.
Conversely, membership implies the weaker cofinal bound
`ρ s < 3 · 2 ^ s`.  The second implication is already derivable from
`Skip/D2` and `Bit/R2`; the conjunction does not decide either premise and
does not resolve `#257`. -/
theorem half_mem_sandwich :
    (ErdosProblems.BitR2.RemainderReachesHalfPointCofinally →
        (1 / 2 : ℝ) ∈ mersenneAchievementSet) ∧
    ((1 / 2 : ℝ) ∈ mersenneAchievementSet →
        ∀ N : ℕ, ∃ s : ℕ, N ≤ s ∧ seamIntegerGreedyRemainder s < 3 * 2 ^ s) :=
  ⟨ErdosProblems.BitR2.half_mem_of_remainderReachesHalfPointCofinally,
    remainder_below_three_halfPoint_cofinally_of_half_mem⟩

/-! ## PROVED finite certificates for the conditional hypothesis -/

private theorem seamWeights_fourteen :
    seamWeights 14 =
      [89478485, 38347922, 17895697, 8659208, 4260880, 2113665,
        1052688, 525314, 262400, 131136, 65552, 32772] := by
  rw [seamWeights]
  rw [seamWeightsFrom_eq_cons (by norm_num : 2 < 14),
    seamWeightsFrom_eq_cons (by norm_num : 3 < 14),
    seamWeightsFrom_eq_cons (by norm_num : 4 < 14),
    seamWeightsFrom_eq_cons (by norm_num : 5 < 14),
    seamWeightsFrom_eq_cons (by norm_num : 6 < 14),
    seamWeightsFrom_eq_cons (by norm_num : 7 < 14),
    seamWeightsFrom_eq_cons (by norm_num : 8 < 14),
    seamWeightsFrom_eq_cons (by norm_num : 9 < 14),
    seamWeightsFrom_eq_cons (by norm_num : 10 < 14),
    seamWeightsFrom_eq_cons (by norm_num : 11 < 14),
    seamWeightsFrom_eq_cons (by norm_num : 12 < 14),
    seamWeightsFrom_eq_cons (by norm_num : 13 < 14),
    seamWeightsFrom_eq_nil (by norm_num : 14 ≤ 14)]
  norm_num [truncatedMersenneWeight]

private theorem seamSubsetTarget_fourteen : seamSubsetTarget 14 = 134201344 := by
  norm_num [seamSubsetTarget]

private theorem greedyBits_fourteen :
    integerGreedyBits (seamWeights 14) (seamSubsetTarget 14) =
      [true, true, false, false, true, true,
        false, false, false, false, false, false] := by
  rw [seamWeights_fourteen, seamSubsetTarget_fourteen]
  norm_num [integerGreedyBits]

/-- The row-`14` seam greedy remainder, exactly. -/
theorem seamIntegerGreedyRemainder_fourteen :
    seamIntegerGreedyRemainder 14 = 392 := by
  rw [seamIntegerGreedyRemainder, integerGreedyRemainder, greedyBits_fourteen,
    seamWeights_fourteen, seamSubsetTarget_fourteen]
  norm_num [weightedBoolSum]

/-- Row `14` really does have its *terminal* rank `13` as largest false rank:
the hypothesis of `remainder_lt_of_terminal_skip` is inhabited. -/
theorem isLargestFalseRank_fourteen :
    IsLargestFalseRank (seamGreedyWord 14) 13 := by
  refine ⟨by norm_num, by norm_num, ?_, ?_⟩
  · intro hmem
    have hbit := (mem_seamWordSupport_iff_greedyBit
      (by norm_num : (2 : ℕ) ≤ 13) (by norm_num : (13 : ℕ) < 14)).mp hmem
    rw [greedyBits_fourteen] at hbit
    norm_num at hbit
  · intro e hde hes
    omega

/-- Concrete instance of the terminal-skip bound. -/
theorem remainder_fourteen_lt_sharp :
    seamIntegerGreedyRemainder 14 < 2 ^ (14 + 1) + 4 :=
  remainder_lt_of_terminal_skip isLargestFalseRank_fourteen (by norm_num)

/-- Concrete instance of the weaker `3 * 2 ^ s` corollary at row `14`. -/
theorem remainder_fourteen_lt :
    seamIntegerGreedyRemainder 14 < 3 * 2 ^ 14 :=
  remainder_lt_of_largestSkipLate Erdos249257.largestSkipLateAt_fourteen

/-- Concrete instance of the weaker `3 * 2 ^ s` corollary at row `20`, from
the independent bit certificate of `Bit/Corr1`. -/
theorem remainder_twenty_lt :
    seamIntegerGreedyRemainder 20 < 3 * 2 ^ 20 :=
  remainder_lt_of_largestSkipLate
    Erdos249257.BitCorr.Concrete.largestSkipLateAt_twenty

end ErdosProblems.RemC4
