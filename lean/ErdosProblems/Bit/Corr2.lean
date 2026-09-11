/-
Copyright (c) 2026 Will Cook. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Will Cook
-/
import Erdos249257.HalfCylinderIntegerGreedy

/-!
# Bit Corr2: alternative row-to-row formulas for the seam integer greedy

The concrete #257 half-membership socket is the deterministic sequence

  `seamIntegerGreedyRemainder s =`
  `  integerGreedyRemainder (seamWeights s) (seamSubsetTarget s)`

and the late-zone take/skip word `seamGreedyWord s` it produces.  Everything
here is about comparing row `s + 1` with row `s`.  The imported corpus already
contains the target recurrence, the weight recurrence through `rowPulse`, and
an exact next-remainder trichotomy.  This file supplies an alternative formula
`rowCarry` for `rowPulse`, list-lifting lemmas, and a general upper bound.

## What is proved

* `seamSubsetTarget_succ` — **PROVED, already present upstream for `s ≥ 2`.**
  The target quadruples exactly, with a single clean
  correction: `seamSubsetTarget (s+1) = 4 * seamSubsetTarget s + 2 ^ (s+1)`.

* `truncatedMersenneWeight_succ_row` — **PROVED in an alternative form.**
  Every weight quadruples exactly, up to an additive carry
  `rowCarry s d = 2 ^ ((2*s) % d + 2) / (2 ^ d - 1)`, and
  `rowCarry_le_two` says that carry is at most `2`.  The adversarial verifier
  proves this carry equals the imported `rowPulse`.

* `rowCarry_eq_two` / `rowCarry_eq_one` / `rowCarry_eq_zero` — the carry is a
  pure divisibility indicator:

      rowCarry s d = 2  ⟺  d ∣ 2*s + 1
      rowCarry s d = 1  ⟸  d ∣ 2*s + 2
      rowCarry s d = 0  ⟸  d ∤ 2*s+1 and d ∤ 2*s+2

  so the row-to-row perturbation of the weight word is supported on divisors
  of `2*s+1` and `2*s+2` below `s`.  No divisor-count asymptotic is proved here.

* `seamWeightsFrom_succ_row` — consequently the row-`s+1` weight word is
  literally the lift `w ↦ 4*w + rowCarry` of the row-`s` word, with the one
  brand-new rank `s` appended.

* `seamIntegerGreedyRemainder_succ_le` — **PROVED upper bound**, unconditional for
  every `s ≥ 3`:

      seamIntegerGreedyRemainder (s+1) ≤ 4 * seamIntegerGreedyRemainder s + 2^(s+1)

  proved by lifting the row-`s` greedy support into row `s+1` (declining the
  new rank) and invoking `integerGreedyBits_maximal`.  It is weaker than the
  exact imported next-remainder trichotomy and can be numerically loose.

* `integerGreedyBits_lift_split` and `seamGreedy_succ_first_difference` — the
  **first-disagreement law**: either the row-`s` word is a prefix of the
  row-`s+1` word, or the first rank where they differ is skipped at row `s`
  and taken at row `s+1`.  A take on the common prefix is never lost.

Both branches are exhibited concretely: `first_difference_right_branch_thirteen`
(`s = 13`, rank `7` flips skip → take) and `first_difference_left_branch_fourteen`
(`s = 14`, rows `14`/`15` agree on every shared rank).

## A branch formula measured in this file

Write `S(s)` for the greedy support of row `s`, `Δ(s,D) = Σ_{d ∈ S(s), d < D}
rowCarry s d`, and `dl s = 2*s/3 + 1` for the first late rank.  Then whenever
rows `s` and `s+1` agree on the shared ranks `2, …, s-1`:

    seamIntegerGreedyRemainder (s+1)
      = 4 * seamIntegerGreedyRemainder s + 2^(s+1) - Δ(s, s)
          - [s ∈ S(s+1)] * truncatedMersenneWeight (s+1) s

and, for the late-zone entering remainder `r s`,

    r (s+1) = 4 * r s + 2^(s+1) - Δ(s, dl s)
                - [dl s ∈ S(s+1) and dl (s+1) = dl s + 1]
                    * truncatedMersenneWeight (s+1) (dl s)

with `dl (s+1) - dl s = 0` when `s ≡ 0 mod 3` and `1` otherwise.  **MEASURED,
NOT PROVED IN THIS FILE:** both were checked against an arbitrary-precision
replication for every `s ∈ [6,6000]`:
zero violations on the `2265` rows in `[6,3000]` where the shared patterns
agree, and zero violations of the proved inequality anywhere.  Later
`Three/T2.lean` proves the corresponding exact branch recurrences.
-/
namespace ErdosProblems.BitCorr2

open Erdos249257.HalfCylinderIntegerGreedy

/-! ## The target recurrence -/

theorem seamSubsetTarget_succ {s : ℕ} (hs : 1 ≤ s) :
    seamSubsetTarget (s + 1) = 4 * seamSubsetTarget s + 2 ^ (s + 1) := by
  have hle : 2 ^ s ≤ 2 ^ (2 * s - 1) :=
    Nat.pow_le_pow_right (by norm_num) (by omega)
  have h1 : 2 ^ (2 * (s + 1) - 1) = 4 * 2 ^ (2 * s - 1) := by
    rw [show 2 * (s + 1) - 1 = (2 * s - 1) + 2 by omega, pow_add]
    ring
  have h2 : (2 : ℕ) ^ (s + 1) = 2 * 2 ^ s := by rw [pow_succ]; ring
  unfold seamSubsetTarget
  omega

/-! ## The weight recurrence -/

/-- Euclidean identity for the truncated Mersenne weight: the remainder of
`4 ^ s` modulo `2 ^ d - 1` is exactly `2 ^ ((2 * s) % d)`. -/
theorem four_pow_eq_truncatedMersenneWeight_mul_add
    {s d : ℕ} (hd : 2 ≤ d) :
    4 ^ s = truncatedMersenneWeight s d * (2 ^ d - 1) + 2 ^ ((2 * s) % d) := by
  set q := (2 * s) / d with hq
  set r := (2 * s) % d with hr
  have hdivmod : 2 * s = d * q + r := by
    rw [hq, hr]; simpa [Nat.mul_comm] using (Nat.div_add_mod (2 * s) d).symm
  have hpowOne : 1 ≤ 2 ^ d := Nat.one_le_pow _ _ (by norm_num)
  have hgeom :
      (∑ i ∈ Finset.range q, (2 ^ d) ^ i) * (2 ^ d - 1) + 1 = (2 ^ d) ^ q := by
    simpa only [Nat.sub_add_cancel hpowOne] using
      (geom_sum_mul_add (R := ℕ) (2 ^ d - 1) q)
  rw [truncatedMersenneWeight_eq_geometricCore hd, ← hq, ← hr]
  calc
    4 ^ s = 2 ^ (2 * s) := by rw [show (4 : ℕ) = 2 ^ 2 by norm_num, ← pow_mul]
    _ = 2 ^ (d * q + r) := by rw [hdivmod]
    _ = 2 ^ r * (2 ^ d) ^ q := by rw [pow_add, pow_mul]; ring
    _ = 2 ^ r * ((∑ i ∈ Finset.range q, (2 ^ d) ^ i) * (2 ^ d - 1) + 1) := by
        rw [hgeom]
    _ = 2 ^ r * (∑ i ∈ Finset.range q, (2 ^ d) ^ i) * (2 ^ d - 1) + 2 ^ r := by
        ring

/-- The carry that the row step `s ↦ s + 1` adds on top of the exact
quadrupling of the rank-`d` weight. -/
def rowCarry (s d : ℕ) : ℕ := 2 ^ ((2 * s) % d + 2) / (2 ^ d - 1)

/-- **Exact weight recurrence.**  Every truncated Mersenne weight quadruples
from row `s` to row `s + 1`, up to an additive carry `rowCarry s d ≤ 2`. -/
theorem truncatedMersenneWeight_succ_row {s d : ℕ} (hd : 2 ≤ d) :
    truncatedMersenneWeight (s + 1) d =
      4 * truncatedMersenneWeight s d + rowCarry s d := by
  have hpowNat : 1 < 2 ^ d := one_lt_pow₀ (by omega) (by omega)
  have hb : 0 < 2 ^ d - 1 := by omega
  have hdec := four_pow_eq_truncatedMersenneWeight_mul_add (s := s) (d := d) hd
  have hmodlt : 2 ^ ((2 * s) % d + 2) % (2 ^ d - 1) < 2 ^ d - 1 := Nat.mod_lt _ hb
  have hcarry :
      rowCarry s d * (2 ^ d - 1) + 2 ^ ((2 * s) % d + 2) % (2 ^ d - 1)
        = 2 ^ ((2 * s) % d + 2) := Nat.div_add_mod' _ _
  have hexp : (2 : ℕ) ^ ((2 * s) % d + 2) = 4 * 2 ^ ((2 * s) % d) := by
    rw [pow_add]; ring
  have hkey :
      4 ^ (s + 1) =
        (2 ^ d - 1) * (4 * truncatedMersenneWeight s d + rowCarry s d) +
          2 ^ ((2 * s) % d + 2) % (2 ^ d - 1) := by
    have h4 : (4 : ℕ) ^ (s + 1) = 4 * 4 ^ s := by ring
    rw [h4, hdec]
    calc
      4 * (truncatedMersenneWeight s d * (2 ^ d - 1) + 2 ^ ((2 * s) % d))
          = (2 ^ d - 1) * (4 * truncatedMersenneWeight s d) +
              4 * 2 ^ ((2 * s) % d) := by ring
      _ = (2 ^ d - 1) * (4 * truncatedMersenneWeight s d) +
              2 ^ ((2 * s) % d + 2) := by rw [hexp]
      _ = (2 ^ d - 1) * (4 * truncatedMersenneWeight s d) +
              (rowCarry s d * (2 ^ d - 1) +
                2 ^ ((2 * s) % d + 2) % (2 ^ d - 1)) := by rw [hcarry]
      _ = (2 ^ d - 1) * (4 * truncatedMersenneWeight s d + rowCarry s d) +
              2 ^ ((2 * s) % d + 2) % (2 ^ d - 1) := by ring
  have hunfold : truncatedMersenneWeight (s + 1) d = 4 ^ (s + 1) / (2 ^ d - 1) := rfl
  rw [hunfold, hkey, Nat.mul_add_div hb, Nat.div_eq_of_lt hmodlt, Nat.add_zero]

theorem rowCarry_le_two {s d : ℕ} (hd : 2 ≤ d) : rowCarry s d ≤ 2 := by
  have hpowNat : 1 < 2 ^ d := one_lt_pow₀ (by omega) (by omega)
  have hb : 0 < 2 ^ d - 1 := by omega
  have hrlt : (2 * s) % d < d := Nat.mod_lt _ (by omega)
  have hle : (2 : ℕ) ^ ((2 * s) % d + 2) ≤ 2 ^ (d + 1) :=
    Nat.pow_le_pow_right (by norm_num) (by omega)
  have hsplit : (2 : ℕ) ^ (d + 1) = 2 * 2 ^ d := by rw [pow_succ]; ring
  have h4 : (4 : ℕ) ≤ 2 ^ d := by
    calc (4 : ℕ) = 2 ^ 2 := by norm_num
    _ ≤ 2 ^ d := Nat.pow_le_pow_right (by norm_num) hd
  have hlt : rowCarry s d < 3 := by
    unfold rowCarry
    rw [Nat.div_lt_iff_lt_mul hb]
    omega
  omega

/-! ## The divisibility trichotomy for the carry -/

theorem mod_eq_pred_of_dvd {s d : ℕ} (hd : 2 ≤ d) (h : d ∣ 2 * s + 1) :
    (2 * s) % d = d - 1 := by
  obtain ⟨m, hm⟩ := h
  have h0 : (2 * s + 1) % d = 0 := by rw [hm, Nat.mul_mod_right]
  have hr : (2 * s) % d < d := Nat.mod_lt _ (by omega)
  have hsplit : (2 * s + 1) % d = ((2 * s) % d + 1) % d := by
    conv_lhs => rw [Nat.add_mod]
    simp [Nat.mod_eq_of_lt (show 1 < d by omega)]
  rcases Nat.lt_or_ge ((2 * s) % d + 1) d with hlt | hge
  · rw [Nat.mod_eq_of_lt hlt] at hsplit; omega
  · omega

theorem mod_eq_sub_two_of_dvd {s d : ℕ} (hd : 2 ≤ d) (h : d ∣ 2 * s + 2) :
    (2 * s) % d = d - 2 := by
  obtain ⟨m, hm⟩ := h
  have h0 : (2 * s + 2) % d = 0 := by rw [hm, Nat.mul_mod_right]
  have hr : (2 * s) % d < d := Nat.mod_lt _ (by omega)
  rcases Nat.lt_or_ge d 3 with hd2 | hd3
  · have hde : d = 2 := by omega
    subst hde
    simp
  · have hsplit : (2 * s + 2) % d = ((2 * s) % d + 2) % d := by
      conv_lhs => rw [Nat.add_mod]
      simp [Nat.mod_eq_of_lt (show 2 < d by omega)]
    rcases Nat.lt_or_ge ((2 * s) % d + 2) d with hlt | hge
    · rw [Nat.mod_eq_of_lt hlt] at hsplit; omega
    · have hlt2 : (2 * s) % d + 2 - d < d := by omega
      have heq : ((2 * s) % d + 2) % d = (2 * s) % d + 2 - d := by
        rw [Nat.mod_eq_sub_mod hge, Nat.mod_eq_of_lt hlt2]
      omega

theorem dvd_of_mod_eq_pred {s d : ℕ} (hd : 2 ≤ d) (h : (2 * s) % d = d - 1) :
    d ∣ 2 * s + 1 := by
  have hq := Nat.div_add_mod (2 * s) d
  refine ⟨(2 * s) / d + 1, ?_⟩
  rw [Nat.mul_add, Nat.mul_one]
  omega

theorem dvd_of_mod_eq_sub_two {s d : ℕ} (hd : 2 ≤ d)
    (h : (2 * s) % d = d - 2) : d ∣ 2 * s + 2 := by
  have hq := Nat.div_add_mod (2 * s) d
  refine ⟨(2 * s) / d + 1, ?_⟩
  rw [Nat.mul_add, Nat.mul_one]
  omega

/-- Carry `2` exactly on the ranks dividing `2 * s + 1`. -/
theorem rowCarry_eq_two {s d : ℕ} (hd : 2 ≤ d) (h : d ∣ 2 * s + 1) :
    rowCarry s d = 2 := by
  have hpowNat : 1 < 2 ^ d := one_lt_pow₀ (by omega) (by omega)
  have hmod := mod_eq_pred_of_dvd hd h
  have h4 : (4 : ℕ) ≤ 2 ^ d := by
    calc (4 : ℕ) = 2 ^ 2 := by norm_num
    _ ≤ 2 ^ d := Nat.pow_le_pow_right (by norm_num) hd
  have hexp : (2 * s) % d + 2 = d + 1 := by omega
  have hsplit : (2 : ℕ) ^ (d + 1) = 2 * 2 ^ d := by rw [pow_succ]; ring
  unfold rowCarry
  rw [hexp]
  exact Nat.div_eq_of_lt_le (by omega) (by omega)

/-- Carry `1` exactly on the ranks dividing `2 * s + 2` (and not `2 * s + 1`). -/
theorem rowCarry_eq_one {s d : ℕ} (hd : 2 ≤ d) (h : d ∣ 2 * s + 2) :
    rowCarry s d = 1 := by
  have hpowNat : 1 < 2 ^ d := one_lt_pow₀ (by omega) (by omega)
  have hmod := mod_eq_sub_two_of_dvd hd h
  have h4 : (4 : ℕ) ≤ 2 ^ d := by
    calc (4 : ℕ) = 2 ^ 2 := by norm_num
    _ ≤ 2 ^ d := Nat.pow_le_pow_right (by norm_num) hd
  have hexp : (2 * s) % d + 2 = d := by omega
  unfold rowCarry
  rw [hexp]
  exact Nat.div_eq_of_lt_le (by omega) (by omega)

/-- Carry `0` off both divisor families. -/
theorem rowCarry_eq_zero {s d : ℕ} (hd : 2 ≤ d)
    (h1 : ¬ d ∣ 2 * s + 1) (h2 : ¬ d ∣ 2 * s + 2) : rowCarry s d = 0 := by
  have hpowNat : 1 < 2 ^ d := one_lt_pow₀ (by omega) (by omega)
  have hr : (2 * s) % d < d := Nat.mod_lt _ (by omega)
  have hne1 : (2 * s) % d ≠ d - 1 := fun h => h1 (dvd_of_mod_eq_pred hd h)
  have hne2 : (2 * s) % d ≠ d - 2 := fun h => h2 (dvd_of_mod_eq_sub_two hd h)
  have hle : (2 : ℕ) ^ ((2 * s) % d + 2) ≤ 2 ^ (d - 1) :=
    Nat.pow_le_pow_right (by norm_num) (by omega)
  have hhalf : (2 : ℕ) ^ (d - 1) * 2 = 2 ^ d := by
    rw [← pow_succ]; congr 1; omega
  have h2le : (2 : ℕ) ≤ 2 ^ (d - 1) := by
    calc (2 : ℕ) = 2 ^ 1 := by norm_num
    _ ≤ 2 ^ (d - 1) := Nat.pow_le_pow_right (by norm_num) (by omega)
  unfold rowCarry
  exact Nat.div_eq_of_lt (by omega)

/-! ## Non-vacuity: all three carry branches are realised -/

example : (3 : ℕ) ∣ 2 * 13 + 1 := by decide
example : (4 : ℕ) ∣ 2 * 13 + 2 := by decide

theorem rowCarry_thirteen_three : rowCarry 13 3 = 2 :=
  rowCarry_eq_two (by norm_num) (by decide)

theorem rowCarry_thirteen_four : rowCarry 13 4 = 1 :=
  rowCarry_eq_one (by norm_num) (by decide)

theorem rowCarry_thirteen_five : rowCarry 13 5 = 0 :=
  rowCarry_eq_zero (by norm_num) (by decide) (by decide)

theorem truncatedMersenneWeight_fourteen_three :
    truncatedMersenneWeight 14 3 = 4 * truncatedMersenneWeight 13 3 + 2 := by
  rw [truncatedMersenneWeight_succ_row (by norm_num), rowCarry_thirteen_three]

theorem seamSubsetTarget_fifteen_recurrence :
    seamSubsetTarget 15 = 4 * seamSubsetTarget 14 + 2 ^ 15 :=
  seamSubsetTarget_succ (by norm_num)

/-! ## Lifting the row-`s` greedy word into row `s + 1` -/

/-- Selecting the row-`s` greedy support inside row `s + 1` (and declining the
brand-new rank `s`) multiplies the achieved subset sum by exactly four, up to a
carry budget of at most two per selected rank. -/
theorem weightedBoolSum_seamWeightsFrom_succ (s d : ℕ) (hd : 2 ≤ d)
    (bs : List Bool) (hlen : bs.length = (seamWeightsFrom s d).length) :
    ∃ δ : ℕ, δ ≤ 2 * (seamWeightsFrom s d).length ∧
      weightedBoolSum (seamWeightsFrom (s + 1) d) (bs ++ [false]) =
        4 * weightedBoolSum (seamWeightsFrom s d) bs + δ := by
  by_cases hds : d < s
  · rw [seamWeightsFrom_eq_cons hds] at hlen ⊢
    rw [seamWeightsFrom_eq_cons (show d < s + 1 by omega)]
    cases bs with
    | nil => simp at hlen
    | cons b bs' =>
        simp only [List.length_cons, Nat.succ.injEq] at hlen
        obtain ⟨δ', hδ', hsum'⟩ :=
          weightedBoolSum_seamWeightsFrom_succ s (d + 1) (by omega) bs' hlen
        cases b
        · refine ⟨δ', by simp only [List.length_cons]; omega, ?_⟩
          simpa only [List.cons_append, weightedBoolSum] using hsum'
        · refine ⟨rowCarry s d + δ', ?_, ?_⟩
          · have := rowCarry_le_two (s := s) (d := d) hd
            simp only [List.length_cons]
            omega
          · have hw := truncatedMersenneWeight_succ_row (s := s) (d := d) hd
            simp only [List.cons_append, weightedBoolSum]
            rw [hw, hsum']
            ring
  · have hnil : seamWeightsFrom s d = [] := seamWeightsFrom_eq_nil (by omega)
    rw [hnil] at hlen ⊢
    have hbs : bs = [] := List.eq_nil_of_length_eq_zero (by simpa using hlen)
    subst hbs
    refine ⟨0, by simp, ?_⟩
    by_cases hds' : d < s + 1
    · rw [seamWeightsFrom_eq_cons hds']
      simp [weightedBoolSum]
    · rw [seamWeightsFrom_eq_nil (by omega)]
      simp [weightedBoolSum]
termination_by s - d
decreasing_by omega

theorem seamWeightsFrom_length (s d : ℕ) :
    (seamWeightsFrom s d).length = s - d := by
  by_cases h : d < s
  · rw [seamWeightsFrom_eq_cons h, List.length_cons, seamWeightsFrom_length s (d + 1)]
    omega
  · rw [seamWeightsFrom_eq_nil (by omega)]
    simp only [List.length_nil]
    omega
termination_by s - d
decreasing_by omega

/-- **The remainder recurrence.**  The concrete seam integer-greedy remainder
of row `s + 1` is at most four times the row-`s` remainder plus the exact
target increment `2 ^ (s + 1)`.  Unconditional for every `s ≥ 3`. -/
theorem seamIntegerGreedyRemainder_succ_le {s : ℕ} (hs : 3 ≤ s) :
    seamIntegerGreedyRemainder (s + 1) ≤
      4 * seamIntegerGreedyRemainder s + 2 ^ (s + 1) := by
  have hT : seamSubsetTarget (s + 1) = 4 * seamSubsetTarget s + 2 ^ (s + 1) :=
    seamSubsetTarget_succ (by omega)
  have hlin : 2 * s + 4 < 2 ^ (s + 1) := two_mul_add_four_lt_two_pow_succ (by omega)
  have hlenW : (seamWeightsFrom s 2).length = s - 2 := seamWeightsFrom_length s 2
  have hlenW' : (seamWeightsFrom (s + 1) 2).length = s - 1 := by
    rw [seamWeightsFrom_length]; omega
  simp only [seamIntegerGreedyRemainder, integerGreedyRemainder, seamWeights]
  have hglen :
      (integerGreedyBits (seamWeightsFrom s 2) (seamSubsetTarget s)).length
        = (seamWeightsFrom s 2).length := integerGreedyBits_length _ _
  have hGle :
      weightedBoolSum (seamWeightsFrom s 2)
        (integerGreedyBits (seamWeightsFrom s 2) (seamSubsetTarget s)) ≤
          seamSubsetTarget s := integerGreedyBits_admissible _ _
  obtain ⟨δ, hδ, hsum⟩ :=
    weightedBoolSum_seamWeightsFrom_succ s 2 (le_refl 2)
      (integerGreedyBits (seamWeightsFrom s 2) (seamSubsetTarget s)) hglen
  rw [hlenW] at hδ
  have hlen' :
      (integerGreedyBits (seamWeightsFrom s 2) (seamSubsetTarget s) ++
          [false]).length = (seamWeightsFrom (s + 1) 2).length := by
    rw [List.length_append, hglen, hlenW, hlenW']
    simp only [List.length_singleton]
    omega
  have hadm :
      weightedBoolSum (seamWeightsFrom (s + 1) 2)
        (integerGreedyBits (seamWeightsFrom s 2) (seamSubsetTarget s) ++
          [false]) ≤ seamSubsetTarget (s + 1) := by
    rw [hsum, hT]; omega
  have hmax := integerGreedyBits_maximal
    (gap := 2 ^ (s + 1 + 1)) (by positivity)
    (seamWeightsFrom_gapDominates (s := s + 1) (d := 2) (by omega) (by omega))
    hlen' hadm
  rw [hsum] at hmax
  have hfinal := integerGreedyBits_admissible (seamWeightsFrom (s + 1) 2)
    (seamSubsetTarget (s + 1))
  omega

/-! ## The shape of the first row-to-row disagreement -/

/-- Row `s + 1`'s weight word on the shared ranks, written as a lift of row
`s`'s: each weight quadruples and picks up its carry. -/
def liftWeights (ws cs : List ℕ) : List ℕ :=
  List.zipWith (fun w c => 4 * w + c) ws cs

theorem integerGreedyBits_append (ws : List ℕ) :
    ∀ (vs : List ℕ) (C : ℕ),
      integerGreedyBits (ws ++ vs) C =
        integerGreedyBits ws C ++
          integerGreedyBits vs
            (C - weightedBoolSum ws (integerGreedyBits ws C)) := by
  induction ws with
  | nil =>
      intro vs C
      simp [integerGreedyBits, weightedBoolSum]
  | cons w ws ih =>
      intro vs C
      rw [List.cons_append]
      by_cases hw : w ≤ C
      · rw [integerGreedyBits, if_pos hw, integerGreedyBits, if_pos hw,
          List.cons_append, ih vs (C - w)]
        congr 2
        congr 1
        simp only [weightedBoolSum]
        omega
      · rw [integerGreedyBits, if_neg hw, integerGreedyBits, if_neg hw,
          List.cons_append, ih vs C]
        congr 2

/-- **Parallel-run dichotomy.**  If the successor capacity dominates by at
least the total carry budget, then either the two descending greedy words
agree outright, or the first place they differ is a rank that the base run
*skips* and the lifted run *takes*.  A take can never become a skip. -/
theorem integerGreedyBits_lift_split (ws : List ℕ) :
    ∀ (cs : List ℕ), cs.length = ws.length → ∀ (C E : ℕ), cs.sum ≤ E →
      integerGreedyBits ws C = integerGreedyBits (liftWeights ws cs) (4 * C + E)
      ∨ ∃ (p b₁ b₂ : List Bool),
          integerGreedyBits ws C = p ++ false :: b₁ ∧
          integerGreedyBits (liftWeights ws cs) (4 * C + E) = p ++ true :: b₂ := by
  induction ws with
  | nil =>
      intro cs _ C E _
      left
      simp [liftWeights, integerGreedyBits]
  | cons w ws ih =>
      intro cs hlen C E hE
      cases cs with
      | nil => simp at hlen
      | cons c cs =>
          simp only [List.length_cons, Nat.succ.injEq] at hlen
          simp only [List.sum_cons] at hE
          have hlift : liftWeights (w :: ws) (c :: cs) =
              (4 * w + c) :: liftWeights ws cs := by
            simp [liftWeights]
          rw [hlift]
          by_cases hw : w ≤ C
          · have hw' : 4 * w + c ≤ 4 * C + E := by omega
            rw [integerGreedyBits, if_pos hw, integerGreedyBits, if_pos hw']
            have hcap : 4 * C + E - (4 * w + c) = 4 * (C - w) + (E - c) := by omega
            rw [hcap]
            rcases ih cs hlen (C - w) (E - c) (by omega) with h | ⟨p, b₁, b₂, h₁, h₂⟩
            · exact Or.inl (by rw [h])
            · exact Or.inr ⟨true :: p, b₁, b₂, by rw [h₁]; rfl, by rw [h₂]; rfl⟩
          · rw [integerGreedyBits, if_neg hw]
            by_cases hw' : 4 * w + c ≤ 4 * C + E
            · rw [integerGreedyBits, if_pos hw']
              exact Or.inr ⟨[], integerGreedyBits ws C,
                integerGreedyBits (liftWeights ws cs) (4 * C + E - (4 * w + c)),
                by simp, by simp⟩
            · rw [integerGreedyBits, if_neg hw']
              rcases ih cs hlen C E (by omega) with h | ⟨p, b₁, b₂, h₁, h₂⟩
              · exact Or.inl (by rw [h])
              · exact Or.inr ⟨false :: p, b₁, b₂, by rw [h₁]; rfl, by rw [h₂]; rfl⟩

/-! ## The carry word, and the row-`s+1` weight word as a lift -/

/-- The carries at ranks `d, d+1, …, s-1`, aligned with `seamWeightsFrom s d`. -/
def rowCarriesFrom (s : ℕ) : ℕ → List ℕ
  | d => if h : d < s then rowCarry s d :: rowCarriesFrom s (d + 1) else []
termination_by d => s - d
decreasing_by omega

theorem rowCarriesFrom_eq_cons {s d : ℕ} (h : d < s) :
    rowCarriesFrom s d = rowCarry s d :: rowCarriesFrom s (d + 1) := by
  rw [rowCarriesFrom]; simp [h]

theorem rowCarriesFrom_eq_nil {s d : ℕ} (h : s ≤ d) : rowCarriesFrom s d = [] := by
  rw [rowCarriesFrom]; simp [Nat.not_lt.mpr h]

theorem rowCarriesFrom_length (s d : ℕ) :
    (rowCarriesFrom s d).length = s - d := by
  by_cases h : d < s
  · rw [rowCarriesFrom_eq_cons h, List.length_cons, rowCarriesFrom_length s (d + 1)]
    omega
  · rw [rowCarriesFrom_eq_nil (by omega)]
    simp only [List.length_nil]
    omega
termination_by s - d
decreasing_by omega

theorem rowCarriesFrom_sum_le (s d : ℕ) (hd : 2 ≤ d) :
    (rowCarriesFrom s d).sum ≤ 2 * (s - d) := by
  by_cases h : d < s
  · rw [rowCarriesFrom_eq_cons h, List.sum_cons]
    have h1 := rowCarry_le_two (s := s) (d := d) hd
    have h2 := rowCarriesFrom_sum_le s (d + 1) (by omega)
    omega
  · rw [rowCarriesFrom_eq_nil (by omega)]
    simp
termination_by s - d
decreasing_by omega

/-- **Row-word recurrence.**  The row-`s+1` weight word is exactly the lift of
the row-`s` weight word, with the one brand-new rank `s` appended. -/
theorem seamWeightsFrom_succ_row {s d : ℕ} (hd : 2 ≤ d) (hds : d ≤ s) :
    seamWeightsFrom (s + 1) d =
      liftWeights (seamWeightsFrom s d) (rowCarriesFrom s d) ++
        [truncatedMersenneWeight (s + 1) s] := by
  by_cases h : d < s
  · rw [seamWeightsFrom_eq_cons (show d < s + 1 by omega),
      seamWeightsFrom_eq_cons h, rowCarriesFrom_eq_cons h,
      show liftWeights (truncatedMersenneWeight s d :: seamWeightsFrom s (d + 1))
          (rowCarry s d :: rowCarriesFrom s (d + 1)) =
          (4 * truncatedMersenneWeight s d + rowCarry s d) ::
            liftWeights (seamWeightsFrom s (d + 1)) (rowCarriesFrom s (d + 1)) from by
        simp [liftWeights],
      List.cons_append, truncatedMersenneWeight_succ_row hd]
    congr 1
    exact seamWeightsFrom_succ_row (show 2 ≤ d + 1 by omega) (by omega)
  · have hde : d = s := by omega
    subst hde
    rw [seamWeightsFrom_eq_cons (show d < d + 1 by omega),
      seamWeightsFrom_eq_nil (le_refl d), rowCarriesFrom_eq_nil (le_refl d),
      seamWeightsFrom_eq_nil (le_refl (d + 1))]
    simp [liftWeights]
termination_by s - d
decreasing_by omega

/-- **First-disagreement law for consecutive rows.**  Either the row-`s`
greedy take/skip word is a prefix of the row-`s+1` word (the two rows agree on
every shared rank), or the first rank where they differ is one that row `s`
*skips* and row `s+1` *takes*.  No rank taken at row `s` on the common prefix
can be dropped at row `s+1`. -/
theorem seamGreedy_succ_first_difference {s : ℕ} (hs : 3 ≤ s) :
    integerGreedyBits (seamWeights s) (seamSubsetTarget s) <+:
        integerGreedyBits (seamWeights (s + 1)) (seamSubsetTarget (s + 1))
    ∨ ∃ (p b₁ b₂ : List Bool),
        integerGreedyBits (seamWeights s) (seamSubsetTarget s) =
            p ++ false :: b₁ ∧
          (p ++ true :: b₂) <+:
            integerGreedyBits (seamWeights (s + 1)) (seamSubsetTarget (s + 1)) := by
  have hT : seamSubsetTarget (s + 1) = 4 * seamSubsetTarget s + 2 ^ (s + 1) :=
    seamSubsetTarget_succ (by omega)
  have hdecomp : seamWeightsFrom (s + 1) 2 =
      liftWeights (seamWeightsFrom s 2) (rowCarriesFrom s 2) ++
        [truncatedMersenneWeight (s + 1) s] :=
    seamWeightsFrom_succ_row (le_refl 2) (by omega)
  have hlenc : (rowCarriesFrom s 2).length = (seamWeightsFrom s 2).length := by
    rw [rowCarriesFrom_length, seamWeightsFrom_length]
  have hcsum : (rowCarriesFrom s 2).sum ≤ 2 ^ (s + 1) := by
    have h1 := rowCarriesFrom_sum_le s 2 (le_refl 2)
    have hlin := two_mul_add_four_lt_two_pow_succ (show 3 ≤ s by omega)
    omega
  simp only [seamWeights]
  rw [hdecomp, hT, integerGreedyBits_append]
  rcases integerGreedyBits_lift_split (seamWeightsFrom s 2) (rowCarriesFrom s 2)
      hlenc (seamSubsetTarget s) (2 ^ (s + 1)) hcsum with h | ⟨p, b₁, b₂, h₁, h₂⟩
  · exact Or.inl (by rw [h]; exact List.prefix_append _ _)
  · exact Or.inr ⟨p, b₁, b₂, h₁, by rw [h₂]; exact List.prefix_append _ _⟩

/-! ## Concrete witnesses (anti-vacuity)

Every theorem above has only the numeric hypotheses `2 ≤ d` / `3 ≤ s`, which
are satisfied by every row the corpus works with.  The witnesses below pin the
concrete values anyway, and — crucially — show that **both** branches of
`seamGreedy_succ_first_difference` actually occur. -/

theorem seamWeights_13 :
    seamWeights 13 = [22369621, 9586980, 4473924, 2164802, 1065220, 528416, 263172, 131328, 65600, 32784, 16388] := by
  unfold seamWeights
  rw [
    seamWeightsFrom_eq_cons (by norm_num : 2 < 13),
    seamWeightsFrom_eq_cons (by norm_num : 3 < 13),
    seamWeightsFrom_eq_cons (by norm_num : 4 < 13),
    seamWeightsFrom_eq_cons (by norm_num : 5 < 13),
    seamWeightsFrom_eq_cons (by norm_num : 6 < 13),
    seamWeightsFrom_eq_cons (by norm_num : 7 < 13),
    seamWeightsFrom_eq_cons (by norm_num : 8 < 13),
    seamWeightsFrom_eq_cons (by norm_num : 9 < 13),
    seamWeightsFrom_eq_cons (by norm_num : 10 < 13),
    seamWeightsFrom_eq_cons (by norm_num : 11 < 13),
    seamWeightsFrom_eq_cons (by norm_num : 12 < 13),
    seamWeightsFrom_eq_nil (by norm_num : 13 ≤ 13)]
  norm_num [truncatedMersenneWeight]

theorem seamWeights_14 :
    seamWeights 14 = [89478485, 38347922, 17895697, 8659208, 4260880, 2113665, 1052688, 525314, 262400, 131136, 65552, 32772] := by
  unfold seamWeights
  rw [
    seamWeightsFrom_eq_cons (by norm_num : 2 < 14),
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

theorem seamWeights_15 :
    seamWeights 15 = [357913941, 153391689, 71582788, 34636833, 17043521, 8454660, 4210752, 2101256, 1049601, 524544, 262208, 131088, 65540] := by
  unfold seamWeights
  rw [
    seamWeightsFrom_eq_cons (by norm_num : 2 < 15),
    seamWeightsFrom_eq_cons (by norm_num : 3 < 15),
    seamWeightsFrom_eq_cons (by norm_num : 4 < 15),
    seamWeightsFrom_eq_cons (by norm_num : 5 < 15),
    seamWeightsFrom_eq_cons (by norm_num : 6 < 15),
    seamWeightsFrom_eq_cons (by norm_num : 7 < 15),
    seamWeightsFrom_eq_cons (by norm_num : 8 < 15),
    seamWeightsFrom_eq_cons (by norm_num : 9 < 15),
    seamWeightsFrom_eq_cons (by norm_num : 10 < 15),
    seamWeightsFrom_eq_cons (by norm_num : 11 < 15),
    seamWeightsFrom_eq_cons (by norm_num : 12 < 15),
    seamWeightsFrom_eq_cons (by norm_num : 13 < 15),
    seamWeightsFrom_eq_cons (by norm_num : 14 < 15),
    seamWeightsFrom_eq_nil (by norm_num : 15 ≤ 15)]
  norm_num [truncatedMersenneWeight]

theorem seamGreedyBits_13 :
    integerGreedyBits (seamWeights 13) (seamSubsetTarget 13) =
      [true, true, false, false, true] ++
        false :: [true, true, true, true, true] := by
  rw [seamWeights_13, show seamSubsetTarget 13 = 33546240 by
    norm_num [seamSubsetTarget]]
  norm_num [integerGreedyBits]

theorem seamGreedyBits_14 :
    integerGreedyBits (seamWeights 14) (seamSubsetTarget 14) =
      [true, true, false, false, true] ++
        true :: [false, false, false, false, false, false] := by
  rw [seamWeights_14, show seamSubsetTarget 14 = 134201344 by
    norm_num [seamSubsetTarget]]
  norm_num [integerGreedyBits]

theorem seamGreedyBits_15 :
    integerGreedyBits (seamWeights 15) (seamSubsetTarget 15) =
      [true, true, false, false, true, true, false, false, false, false,
        false, false, false] := by
  rw [seamWeights_15, show seamSubsetTarget 15 = 536838144 by
    norm_num [seamSubsetTarget]]
  norm_num [integerGreedyBits]

/-- The *right* branch of `seamGreedy_succ_first_difference` is realised at
`s = 13`: rank `7` is skipped at row `13` and taken at row `14`. -/
theorem first_difference_right_branch_thirteen :
    ∃ (p b₁ b₂ : List Bool),
      integerGreedyBits (seamWeights 13) (seamSubsetTarget 13) = p ++ false :: b₁ ∧
        (p ++ true :: b₂) <+:
          integerGreedyBits (seamWeights 14) (seamSubsetTarget 14) :=
  ⟨[true, true, false, false, true], [true, true, true, true, true],
    [false, false, false, false, false, false], seamGreedyBits_13,
    by rw [seamGreedyBits_14]⟩

/-- The *left* branch is realised at `s = 14`: rows `14` and `15` agree on
every shared rank. -/
theorem first_difference_left_branch_fourteen :
    integerGreedyBits (seamWeights 14) (seamSubsetTarget 14) <+:
      integerGreedyBits (seamWeights 15) (seamSubsetTarget 15) := by
  rw [seamGreedyBits_14, seamGreedyBits_15]
  exact ⟨[false], by norm_num⟩

theorem seamIntegerGreedyRemainder_14 : seamIntegerGreedyRemainder 14 = 392 := by
  unfold seamIntegerGreedyRemainder integerGreedyRemainder
  rw [seamGreedyBits_14, seamWeights_14, show seamSubsetTarget 14 = 134201344 by
    norm_num [seamSubsetTarget]]
  norm_num [weightedBoolSum]

theorem seamIntegerGreedyRemainder_15 : seamIntegerGreedyRemainder 15 = 34333 := by
  unfold seamIntegerGreedyRemainder integerGreedyRemainder
  rw [seamGreedyBits_15, seamWeights_15, show seamSubsetTarget 15 = 536838144 by
    norm_num [seamSubsetTarget]]
  norm_num [weightedBoolSum]

/-- The remainder recurrence instantiated, and nearly sharp: the true value is
`34333`, the bound is `4 * 392 + 2 ^ 15 = 34336`, a defect of exactly `3`,
which is the total carry `rowCarry 14 d` over the four selected ranks
`d = 2, 3, 6, 7`. -/
theorem remainder_recurrence_witness_fourteen :
    seamIntegerGreedyRemainder 15 ≤ 4 * seamIntegerGreedyRemainder 14 + 2 ^ 15 :=
  seamIntegerGreedyRemainder_succ_le (by norm_num)

theorem remainder_recurrence_defect_fourteen :
    4 * seamIntegerGreedyRemainder 14 + 2 ^ 15 - seamIntegerGreedyRemainder 15 = 3 := by
  rw [seamIntegerGreedyRemainder_14, seamIntegerGreedyRemainder_15]
  norm_num

end ErdosProblems.BitCorr2
