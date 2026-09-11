/-
Copyright (c) 2026 Will Cook. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Will Cook
-/
import ErdosProblems.Bit.R2

/-!
# Rem C5: what weight-counting can and cannot say about the seam remainder

`Bit/R2` reduces the `1/2` question of Erdős `#257` to a single inequality on
the deterministic sequence

    `rem s = seamIntegerGreedyRemainder s = integerGreedyRemainder (seamWeights s)
              (seamSubsetTarget s)`,

and names the one missing input: *an unconditional upper bound on `rem` at an
arbitrary row that beats the trivial `rem t ≤ seamSubsetTarget t ≈ 4 ^ t / 2`.*
This file attacks that by counting/pigeonhole on the weight word alone, and
settles exactly how far that method reaches.

## The abstract engine

`greedyRemainder_le_of_tailDominated`: for **any** weight list `l` and capacity
`C`,

    (∀ suffix `w :: t` of `l`, `w ≤ t.sum + B`)  →  `C ≤ l.sum + B`
      →  `integerGreedyRemainder l C ≤ B`.

Both hypotheses are properties of `l` and of the single number `C`; nothing
about the arithmetic of the seam enters.  The optimal `B` for a word is the
largest *head slack* `w_j - (sum of the weights after j)`.

## Positive: the method does beat `4 ^ t / 2`

* `seamIntegerGreedyRemainder_add_tail_le` — unconditional, every `s ≥ 3`:

      `rem s + (w_3 + ... + w_{s-1}) ≤ w_2`.

* `eight_mul_remainder_le` — unconditional, every `s ≥ 6`: `8 * rem s ≤ 4 ^ s`.
  This file proves that improvement by weight counting.  It is not the
  strongest bound in the current corpus: `Rem/C6.lean` later proves
  `8 * rem s < 2 ^ (2*s-1)` and `rem s < 4^s/31`.

* `remainder_add_tail_le_of_skipsRank` — **localised.**  If the greedy skips
  rank `a` at row `s` (`SkipsRank s a`, a decidable condition on the residual
  carried into rank `a`), then `rem s + (w_{a+1} + ... + w_{s-1}) ≤ w_a`.
  The later the skip, the smaller the bound.
* `obeysCeiling_of_skipsRank`, `obeysCeiling_of_skipsLast` — the localised bound
  discharges `Bit/R2`'s `ObeysRemainderCeiling` whenever the head slack at a
  skipped rank is below `(7/3) * 2 ^ s`; in particular whenever the *last* rank
  `s - 1` is skipped, since then the slack is exactly `w_{s-1} = 2 ^ (s+1) + 4`
  (`weight_last`).  `R2` proves that ceiling only at *good* rows; here it is
  certified at rows `11` and `12`, which `R2` proves are **bad**
  (`ceiling_at_bad_rows`).

## Negative, and it is sharp

The method stops at `Θ(4 ^ s)`, and this is not slack in the argument:

* `greedyRemainder_at_head_sub_one` — at the capacity `w_2 - 1` the descending
  greedy skips the head and then takes the entire tail, so its remainder is
  **exactly** the head slack minus one;
* `counting_bound_sharp` — that remainder is at least `(4 ^ s - 35) / 21`;
* `head_lt_target` — and `w_2 - 1` is a strictly *smaller* admissible capacity
  than `seamSubsetTarget s`;
* `exists_admissible_capacity_remainder_gt_two_pow` — hence for every `s ≥ 6`
  the same weight word carries an admissible capacity whose greedy remainder
  **exceeds `2 ^ s`**.

So `rem s ≤ 2 ^ s` is not a consequence of the exact weight word together
with only the generic admissibility inequality on an otherwise arbitrary
capacity: the upper bound `4 ^ s / 8` and the
attained lower bound `(4 ^ s - 35) / 21` bracket the method's answer within a
factor `8/3`, and both are `Θ(4 ^ s)`.  This generic weight-counting method
cannot resolve `#257`; the counterexample shows that a successful argument
must use information distinguishing the specific target
`2 ^ (2s-1) - 2 ^ s` from other admissible capacities.

The concrete C5 suggestion — "if two consecutive weights differ by less than
`2 ^ s`" — is refuted outright by `consecutive_gap_ge`: adjacent seam weights
differ by at least `2 ^ (s+1)`, always.

## Non-vacuity

Every hypothesis used is exhibited in the kernel: `skipsRank_eight`,
`skipsRank_eleven`, `skipsRank_twelve` (so `obeysCeiling_eight`,
`obeysCeiling_eleven`, `obeysCeiling_twelve` are live), and
`counting_bound_sharp_eight` computes the sharpness witness at `s = 8`
(remainder `4443`, versus `2 ^ 8 = 256`).  The two unconditional bounds have no
hypothesis beyond a numeric floor on `s`.

Axiom audit (run separately, `#print axioms`): every result below depends on
exactly `[propext, Classical.choice, Quot.sound]`.
-/

namespace ErdosProblems.RemC5

open Erdos249257
open Erdos249257.HalfCylinderIntegerGreedy

/-! ## Abstract descending-greedy calculus -/

theorem greedyRemainder_nil (C : ℕ) : integerGreedyRemainder [] C = C := by
  simp [integerGreedyRemainder, weightedBoolSum]

theorem greedyRemainder_cons_take {w C : ℕ} (t : List ℕ) (h : w ≤ C) :
    integerGreedyRemainder (w :: t) C = integerGreedyRemainder t (C - w) := by
  unfold integerGreedyRemainder
  rw [integerGreedyBits, if_pos h]
  show C - (w + weightedBoolSum t (integerGreedyBits t (C - w))) = _
  omega

theorem greedyRemainder_cons_skip {w C : ℕ} (t : List ℕ) (h : ¬ w ≤ C) :
    integerGreedyRemainder (w :: t) C = integerGreedyRemainder t C := by
  unfold integerGreedyRemainder
  rw [integerGreedyBits, if_neg h]
  rfl

theorem greedyRemainder_eq_sub_sum :
    ∀ (l : List ℕ) {C : ℕ}, l.sum ≤ C → integerGreedyRemainder l C = C - l.sum := by
  intro l
  induction l with
  | nil => intro C _; simp [greedyRemainder_nil]
  | cons w t ih =>
      intro C hC
      simp only [List.sum_cons] at hC ⊢
      rw [greedyRemainder_cons_take t (by omega), ih (by omega)]
      omega

theorem greedyRemainder_append :
    ∀ (l₁ l₂ : List ℕ) (C : ℕ),
      integerGreedyRemainder (l₁ ++ l₂) C
        = integerGreedyRemainder l₂ (integerGreedyRemainder l₁ C) := by
  intro l₁
  induction l₁ with
  | nil => intro l₂ C; simp [greedyRemainder_nil]
  | cons w t ih =>
      intro l₂ C
      by_cases h : w ≤ C
      · rw [List.cons_append, greedyRemainder_cons_take _ h,
          greedyRemainder_cons_take _ h, ih]
      · rw [List.cons_append, greedyRemainder_cons_skip _ h,
          greedyRemainder_cons_skip _ h, ih]

/-- Every entry is at most `B` above the sum of the entries strictly after it. -/
def TailDominated (B : ℕ) : List ℕ → Prop
  | [] => True
  | w :: t => w ≤ t.sum + B ∧ TailDominated B t

/-- **The counting bound.**  A descending greedy on a tail-dominated word leaves
at most `B`, provided the capacity itself is within `B` of the total. -/
theorem greedyRemainder_le_of_tailDominated :
    ∀ (l : List ℕ) {C B : ℕ}, TailDominated B l → C ≤ l.sum + B →
      integerGreedyRemainder l C ≤ B := by
  intro l
  induction l with
  | nil => intro C B _ hC; simpa [greedyRemainder_nil] using hC
  | cons w t ih =>
      intro C B hdom hC
      obtain ⟨hhead, htail⟩ := hdom
      simp only [List.sum_cons] at hC
      by_cases h : w ≤ C
      · rw [greedyRemainder_cons_take t h]
        exact ih htail (by omega)
      · rw [greedyRemainder_cons_skip t h]
        exact ih htail (by omega)


/-! ## Seam-specific structure -/

theorem tail_sum_succ {s d : ℕ} (h : d < s) :
    (seamWeightsFrom s d).sum
      = truncatedMersenneWeight s d + (seamWeightsFrom s (d + 1)).sum := by
  rw [seamWeightsFrom_eq_cons h, List.sum_cons]

theorem tail_sum_le_weight {s d : ℕ} (hs : 2 ≤ s) (hd : 1 ≤ d) (hds : d < s) :
    (seamWeightsFrom s (d + 1)).sum ≤ truncatedMersenneWeight s d := by
  have h := truncatedMersenneWeight_dominanceGap hs hd hds
  exact le_trans (Nat.le_add_left _ _) h

/-- Consecutive seam weights at least halve. -/
theorem two_mul_weight_succ_le {s d : ℕ} (hd : 1 ≤ d) :
    2 * truncatedMersenneWeight s (d + 1) ≤ truncatedMersenneWeight s d := by
  have hpos : 0 < 2 ^ d - 1 := by
    have : 2 ≤ 2 ^ d := by
      calc (2 : ℕ) = 2 ^ 1 := by norm_num
        _ ≤ 2 ^ d := Nat.pow_le_pow_right (by norm_num) hd
    omega
  have hle : 2 * (2 ^ d - 1) ≤ 2 ^ (d + 1) - 1 := by
    have : (2 : ℕ) ^ (d + 1) = 2 * 2 ^ d := by rw [pow_succ]; ring
    omega
  have h1 : (4 : ℕ) ^ s / (2 ^ (d + 1) - 1) ≤ 4 ^ s / (2 * (2 ^ d - 1)) :=
    Nat.div_le_div_left hle (by omega)
  have h2 : (4 : ℕ) ^ s / (2 * (2 ^ d - 1)) = 4 ^ s / (2 ^ d - 1) / 2 := by
    rw [Nat.div_div_eq_div_mul]
    ring_nf
  have h3 : 2 * ((4 : ℕ) ^ s / (2 ^ d - 1) / 2) ≤ 4 ^ s / (2 ^ d - 1) := by
    have := Nat.div_mul_le_self ((4 : ℕ) ^ s / (2 ^ d - 1)) 2
    omega
  unfold truncatedMersenneWeight
  omega

/-- The head weight `truncatedMersenneWeight s a` dominates every later weight by
at least as much as it dominates its own tail. -/
theorem seam_chain (s a : ℕ) (ha : 1 ≤ a) (j : ℕ) (hj : a ≤ j) (hjs : j < s) :
    truncatedMersenneWeight s j + (seamWeightsFrom s (a + 1)).sum
      ≤ (seamWeightsFrom s (j + 1)).sum + truncatedMersenneWeight s a := by
  induction j, hj using Nat.le_induction with
  | base => omega
  | succ j hj ih =>
      have hjs' : j < s := by omega
      have hstep := ih hjs'
      have hsplit := tail_sum_succ (s := s) (d := j + 1) hjs
      have hhalf := two_mul_weight_succ_le (s := s) (d := j) (by omega)
      omega


/-- Tail-dominance of the whole seam suffix from `a`, with the *exact* head
slack `w_a - (tail after a)` as the constant. -/
theorem seam_tailDominated (s a : ℕ) (hs : 2 ≤ s) (ha : 1 ≤ a) (has : a < s)
    (j : ℕ) (hj : a ≤ j) :
    TailDominated (truncatedMersenneWeight s a - (seamWeightsFrom s (a + 1)).sum)
      (seamWeightsFrom s j) := by
  by_cases hjs : j < s
  · rw [seamWeightsFrom_eq_cons hjs, TailDominated]
    refine ⟨?_, seam_tailDominated s a hs ha has (j + 1) (by omega)⟩
    have hchain := seam_chain s a ha j hj hjs
    have hdom := tail_sum_le_weight hs ha has
    omega
  · rw [seamWeightsFrom_eq_nil (s := s) (d := j) (by omega)]
    trivial
termination_by s - j
decreasing_by omega

theorem four_pow_eq_two_pow (s : ℕ) : (4 : ℕ) ^ s = 2 ^ (2 * s) := by
  rw [show (4 : ℕ) = 2 ^ 2 by norm_num, ← pow_mul, Nat.mul_comm]

theorem four_pow_le_three_mul_head (s : ℕ) :
    (4 : ℕ) ^ s ≤ 3 * truncatedMersenneWeight s 2 + 2 := by
  have h := Nat.div_add_mod ((4 : ℕ) ^ s) 3
  have h2 : (4 : ℕ) ^ s % 3 < 3 := Nat.mod_lt _ (by norm_num)
  unfold truncatedMersenneWeight
  norm_num at h ⊢
  omega

theorem target_le_two_mul_head {s : ℕ} (hs : 1 ≤ s) :
    seamSubsetTarget s ≤ 2 * truncatedMersenneWeight s 2 := by
  have hpow : 2 * 2 ^ (2 * s - 1) = (4 : ℕ) ^ s := by
    rw [four_pow_eq_two_pow, ← pow_succ']
    congr 1
    omega
  have h := four_pow_le_three_mul_head s
  have h2 : (1 : ℕ) ≤ 2 ^ s := Nat.one_le_two_pow
  unfold seamSubsetTarget
  omega

/-- **The counting/pigeonhole bound for the seam word, unconditional.**  For any
admissible capacity the descending greedy leaves at most the head slack
`w_2 - (w_3 + ... + w_{s-1})`. -/
theorem seam_remainder_bound (s : ℕ) (hs : 3 ≤ s) (C : ℕ)
    (hC : C ≤ 2 * truncatedMersenneWeight s 2) :
    integerGreedyRemainder (seamWeights s) C + (seamWeightsFrom s 3).sum
      ≤ truncatedMersenneWeight s 2 := by
  have hdom : (seamWeightsFrom s 3).sum ≤ truncatedMersenneWeight s 2 :=
    tail_sum_le_weight (by omega) (by norm_num) (by omega)
  have hsum : (seamWeights s).sum
      = truncatedMersenneWeight s 2 + (seamWeightsFrom s 3).sum := by
    rw [seamWeights]; exact tail_sum_succ (by omega)
  have htd := seam_tailDominated s 2 (by omega) (by norm_num) (by omega) 2 le_rfl
  have hmain := greedyRemainder_le_of_tailDominated (seamWeights s)
    (C := C) (B := truncatedMersenneWeight s 2 - (seamWeightsFrom s 3).sum)
    (by rw [seamWeights]; exact htd) (by omega)
  omega

/-- Specialisation to the actual seam target. -/
theorem seamIntegerGreedyRemainder_add_tail_le (s : ℕ) (hs : 3 ≤ s) :
    seamIntegerGreedyRemainder s + (seamWeightsFrom s 3).sum
      ≤ truncatedMersenneWeight s 2 :=
  seam_remainder_bound s hs _ (target_le_two_mul_head (by omega))


/-! ## The unconditional numeric bound -/

theorem four_pow_lt_weight_mul {s d : ℕ} (hd : 1 ≤ d) :
    (4 : ℕ) ^ s < (2 ^ d - 1) * truncatedMersenneWeight s d + (2 ^ d - 1) := by
  have h2 : (2 : ℕ) ≤ 2 ^ d := by
    calc (2 : ℕ) = 2 ^ 1 := by norm_num
      _ ≤ 2 ^ d := Nat.pow_le_pow_right (by norm_num) hd
  have hpos : 0 < 2 ^ d - 1 := by omega
  have h := Nat.div_add_mod ((4 : ℕ) ^ s) (2 ^ d - 1)
  have hm := Nat.mod_lt ((4 : ℕ) ^ s) hpos
  unfold truncatedMersenneWeight
  omega

/-- **Unconditional upper bound at an arbitrary row.**  `8 * rem s ≤ 4 ^ s`.
The corpus's previous unconditional bound at an arbitrary row was the trivial
`rem s ≤ seamSubsetTarget s`, i.e. essentially `4 ^ s / 2`. -/
theorem eight_mul_remainder_le (s : ℕ) (hs : 6 ≤ s) :
    8 * seamIntegerGreedyRemainder s ≤ 4 ^ s := by
  have hmain := seamIntegerGreedyRemainder_add_tail_le s (by omega)
  have e3 : (seamWeightsFrom s 3).sum
      = truncatedMersenneWeight s 3 + (seamWeightsFrom s 4).sum :=
    tail_sum_succ (by omega)
  have e4 : (seamWeightsFrom s 4).sum
      = truncatedMersenneWeight s 4 + (seamWeightsFrom s 5).sum :=
    tail_sum_succ (by omega)
  have hq : truncatedMersenneWeight s 2 * 3 ≤ 4 ^ s := by
    rw [truncatedMersenneWeight]
    norm_num
    exact Nat.div_mul_le_self _ _
  have b3 : (4 : ℕ) ^ s < 7 * truncatedMersenneWeight s 3 + 7 := by
    have h := four_pow_lt_weight_mul (s := s) (d := 3) (by norm_num)
    norm_num at h
    omega
  have b4 : (4 : ℕ) ^ s < 15 * truncatedMersenneWeight s 4 + 15 := by
    have h := four_pow_lt_weight_mul (s := s) (d := 4) (by norm_num)
    norm_num at h
    omega
  have hbig : (4096 : ℕ) ≤ 4 ^ s := by
    calc (4096 : ℕ) = 4 ^ 6 := by norm_num
      _ ≤ 4 ^ s := Nat.pow_le_pow_right (by norm_num) hs
  omega

/-! ## Sharpness: the counting bound is attained on the same word -/

theorem head_weight_small {s d : ℕ} (hd : 3 ≤ d) :
    7 * 2 ^ d * truncatedMersenneWeight s d ≤ 8 * 4 ^ s := by
  have hpow : (8 : ℕ) ≤ 2 ^ d := by
    calc (8 : ℕ) = 2 ^ 3 := by norm_num
      _ ≤ 2 ^ d := Nat.pow_le_pow_right (by norm_num) hd
  set W := truncatedMersenneWeight s d with hW
  have hq : W * (2 ^ d - 1) ≤ 4 ^ s := by
    rw [hW, truncatedMersenneWeight]; exact Nat.div_mul_le_self _ _
  have h7 : 7 * W ≤ 4 ^ s := by
    have h1 : W ≤ 4 ^ s / 7 := by
      rw [hW, truncatedMersenneWeight]
      exact Nat.div_le_div_left (by omega) (by norm_num)
    have h2 : 7 * ((4 : ℕ) ^ s / 7) ≤ 4 ^ s := by
      have := Nat.div_mul_le_self ((4 : ℕ) ^ s) 7
      omega
    omega
  obtain ⟨m, hm⟩ : ∃ m, 2 ^ d = m + 1 := ⟨2 ^ d - 1, by omega⟩
  rw [hm] at hq ⊢
  simp only [Nat.add_sub_cancel] at hq
  calc 7 * (m + 1) * W = 7 * (W * m) + 7 * W := by ring
    _ ≤ 7 * 4 ^ s + 4 ^ s := Nat.add_le_add (Nat.mul_le_mul_left 7 hq) h7
    _ = 8 * 4 ^ s := by ring

theorem tail_sum_small (s d : ℕ) (hd : 3 ≤ d) :
    7 * 2 ^ (d - 1) * (seamWeightsFrom s d).sum ≤ 8 * 4 ^ s := by
  by_cases hds : d < s
  · have hsplit := tail_sum_succ (s := s) (d := d) hds
    have ih := tail_sum_small s (d + 1) (by omega)
    have hhead := head_weight_small (s := s) (d := d) hd
    have hp : 2 ^ d = 2 * 2 ^ (d - 1) := by
      rw [← pow_succ']; congr 1; omega
    have hp' : (d + 1) - 1 = d := by omega
    rw [hp'] at ih
    rw [hsplit]
    set P := 2 ^ (d - 1) with hP
    set A := truncatedMersenneWeight s d with hA
    set B := (seamWeightsFrom s (d + 1)).sum with hB
    have e1 : 7 * (2 * P) * A = 2 * (7 * P * A) := by ring
    have e2 : 7 * (2 * P) * B = 2 * (7 * P * B) := by ring
    rw [hp, e1] at hhead
    rw [hp, e2] at ih
    have e3 : 7 * P * (A + B) = 7 * P * A + 7 * P * B := by ring
    rw [e3]
    omega
  · rw [seamWeightsFrom_eq_nil (s := s) (d := d) (by omega)]
    simp
termination_by s - d
decreasing_by omega

theorem four_mul_two_pow_le {s : ℕ} (hs : 3 ≤ s) : 4 * 2 ^ s ≤ 2 ^ (2 * s - 1) := by
  have : (4 : ℕ) * 2 ^ s = 2 ^ (s + 2) := by rw [pow_add]; ring
  rw [this]
  exact Nat.pow_le_pow_right (by norm_num) (by omega)

/-- The head weight is a strictly smaller admissible capacity than the seam
target. -/
theorem head_lt_target {s : ℕ} (hs : 3 ≤ s) :
    truncatedMersenneWeight s 2 < seamSubsetTarget s := by
  have hpow : 2 * 2 ^ (2 * s - 1) = (4 : ℕ) ^ s := by
    rw [four_pow_eq_two_pow, ← pow_succ']
    congr 1
    omega
  have h := four_pow_le_three_mul_head s
  have h4 := four_mul_two_pow_le hs
  have hq : truncatedMersenneWeight s 2 * 3 ≤ 4 ^ s := by
    rw [truncatedMersenneWeight]
    norm_num
    exact Nat.div_mul_le_self _ _
  have hone : (1 : ℕ) ≤ 2 ^ s := Nat.one_le_two_pow
  unfold seamSubsetTarget
  omega

/-- **Sharpness.**  At the admissible capacity `w_2 - 1` the descending greedy
skips the head and then takes the whole tail, so the remainder is exactly the
head slack minus one. -/
theorem greedyRemainder_at_head_sub_one (s : ℕ) (hs : 3 ≤ s) :
    integerGreedyRemainder (seamWeights s) (truncatedMersenneWeight s 2 - 1)
      = truncatedMersenneWeight s 2 - 1 - (seamWeightsFrom s 3).sum := by
  have hgap := truncatedMersenneWeight_dominanceGap (s := s) (d := 2)
    (by omega) (by norm_num) (by omega)
  have h2 : (2 : ℕ) ≤ 2 ^ (s + 1) := by
    calc (2 : ℕ) = 2 ^ 1 := by norm_num
      _ ≤ 2 ^ (s + 1) := Nat.pow_le_pow_right (by norm_num) (by omega)
  rw [seamWeights, seamWeightsFrom_eq_cons (show 2 < s by omega),
    greedyRemainder_cons_skip _ (by omega)]
  exact greedyRemainder_eq_sub_sum _ (by omega)

/-- **The C5 no-go, quantitative.**  The seam word admits an admissible capacity
whose descending-greedy remainder is at least `(4 ^ s - 35) / 21`.  Since the
counting bound `seam_remainder_bound` is a property of the *word alone*, no
gap/pigeonhole argument over `seamWeights s` can produce a remainder bound below
`(4 ^ s - 35) / 21`; in particular none can reach `2 ^ s`. -/
theorem counting_bound_sharp (s : ℕ) (hs : 3 ≤ s) :
    4 ^ s ≤
      21 * integerGreedyRemainder (seamWeights s) (truncatedMersenneWeight s 2 - 1) + 35 := by
  have hval := greedyRemainder_at_head_sub_one s hs
  have hgap := truncatedMersenneWeight_dominanceGap (s := s) (d := 2)
    (by omega) (by norm_num) (by omega)
  have h2 : (2 : ℕ) ≤ 2 ^ (s + 1) := by
    calc (2 : ℕ) = 2 ^ 1 := by norm_num
      _ ≤ 2 ^ (s + 1) := Nat.pow_le_pow_right (by norm_num) (by omega)
  have htail := tail_sum_small s 3 (by norm_num)
  norm_num at htail
  have hhead := four_pow_le_three_mul_head s
  rw [hval]
  omega



/-- **The C5 verdict.**  For every `s ≥ 6` the seam weight word carries an
admissible capacity — strictly below the seam target itself — whose
descending-greedy remainder exceeds `2 ^ s`.  Hence `rem s ≤ 2 ^ s` is not a
consequence of any property of `seamWeights s` together with admissibility of
the capacity: no counting, gap or pigeonhole argument over the weight word can
deliver it. -/
theorem exists_admissible_capacity_remainder_gt_two_pow (s : ℕ) (hs : 6 ≤ s) :
    ∃ C : ℕ, C < seamSubsetTarget s ∧
      2 ^ s < integerGreedyRemainder (seamWeights s) C := by
  refine ⟨truncatedMersenneWeight s 2 - 1, ?_, ?_⟩
  · have h := head_lt_target (s := s) (by omega)
    omega
  · have hsharp := counting_bound_sharp s (by omega)
    have hX : (64 : ℕ) ≤ 2 ^ s := by
      calc (64 : ℕ) = 2 ^ 6 := by norm_num
        _ ≤ 2 ^ s := Nat.pow_le_pow_right (by norm_num) hs
    have h4 : (4 : ℕ) ^ s = 2 ^ s * 2 ^ s := by
      rw [four_pow_eq_two_pow, two_mul, pow_add]
    have hsq : 64 * 2 ^ s ≤ 4 ^ s := by
      rw [h4]
      exact Nat.mul_le_mul hX (le_refl (2 ^ s))
    omega

/-! ## Localising the bound at a skipped rank -/

theorem seamWeightsFrom_drop (s : ℕ) :
    ∀ (k a : ℕ), (seamWeightsFrom s a).drop k = seamWeightsFrom s (a + k) := by
  intro k
  induction k with
  | zero => intro a; simp
  | succ k ih =>
      intro a
      by_cases h : a < s
      · rw [seamWeightsFrom_eq_cons h, List.drop_succ_cons, ih]
        congr 1
        omega
      · rw [seamWeightsFrom_eq_nil (s := s) (d := a) (by omega),
          seamWeightsFrom_eq_nil (s := s) (d := a + (k + 1)) (by omega)]
        simp

/-- The residual the descending greedy carries into rank `a` of row `s`. -/
def seamEnteringRemainder (s a : ℕ) : ℕ :=
  integerGreedyRemainder ((seamWeights s).take (a - 2)) (seamSubsetTarget s)

/-- Row `s` *skips* rank `a`: the residual entering that rank is below the
weight there, so the greedy leaves the rank unselected. -/
def SkipsRank (s a : ℕ) : Prop :=
  seamEnteringRemainder s a < truncatedMersenneWeight s a

theorem seam_remainder_split (s a : ℕ) (h2 : 2 ≤ a) :
    seamIntegerGreedyRemainder s
      = integerGreedyRemainder (seamWeightsFrom s a) (seamEnteringRemainder s a) := by
  have hd : (seamWeights s).drop (a - 2) = seamWeightsFrom s a := by
    rw [seamWeights, seamWeightsFrom_drop]
    congr 1
    omega
  unfold seamIntegerGreedyRemainder seamEnteringRemainder
  conv_lhs => rw [← List.take_append_drop (a - 2) (seamWeights s)]
  rw [greedyRemainder_append, hd]

/-- **The localised counting bound.**  If row `s` skips rank `a`, the seam
remainder is at most the head slack at `a`. -/
theorem remainder_add_tail_le_of_skipsRank {s a : ℕ} (hs : 3 ≤ s) (h2 : 2 ≤ a)
    (has : a < s) (hskip : SkipsRank s a) :
    seamIntegerGreedyRemainder s + (seamWeightsFrom s (a + 1)).sum
      ≤ truncatedMersenneWeight s a := by
  have hdom := tail_sum_le_weight (s := s) (d := a) (by omega) (by omega) has
  have htd := seam_tailDominated s a (by omega) (by omega) has a le_rfl
  have hsum := tail_sum_succ (s := s) (d := a) has
  unfold SkipsRank at hskip
  rw [seam_remainder_split s a h2]
  have hmain := greedyRemainder_le_of_tailDominated (seamWeightsFrom s a)
    (C := seamEnteringRemainder s a)
    (B := truncatedMersenneWeight s a - (seamWeightsFrom s (a + 1)).sum)
    htd (by omega)
  omega

/-- **Ceiling from a late skip.**  Whenever the head slack at a skipped rank is
below `(7/3) * 2 ^ s`, row `s` obeys `Bit/R2`'s remainder ceiling — with no
assumption that the row is good. -/
theorem obeysCeiling_of_skipsRank {s a : ℕ} (hs : 3 ≤ s) (h2 : 2 ≤ a) (has : a < s)
    (hskip : SkipsRank s a)
    (hslack : 3 * truncatedMersenneWeight s a
        < 7 * 2 ^ s + 4 + 3 * (seamWeightsFrom s (a + 1)).sum) :
    ErdosProblems.BitR2.ObeysRemainderCeiling s := by
  have h := remainder_add_tail_le_of_skipsRank hs h2 has hskip
  unfold ErdosProblems.BitR2.ObeysRemainderCeiling
  omega

/-! ### The last rank -/

theorem weight_last (s : ℕ) (hs : 4 ≤ s) :
    truncatedMersenneWeight s (s - 1) = 2 ^ (s + 1) + 4 := by
  obtain ⟨t, ht⟩ : ∃ t, 2 ^ (s - 1) = t + 1 := ⟨2 ^ (s - 1) - 1, by
    have : (1 : ℕ) ≤ 2 ^ (s - 1) := Nat.one_le_two_pow
    omega⟩
  have ht5 : 5 ≤ t := by
    have h8 : (8 : ℕ) ≤ 2 ^ (s - 1) := by
      calc (8 : ℕ) = 2 ^ 3 := by norm_num
        _ ≤ 2 ^ (s - 1) := Nat.pow_le_pow_right (by norm_num) (by omega)
    omega
  have h4 : (4 : ℕ) ^ s = 4 * ((t + 1) * (t + 1)) := by
    have hrw : (4 : ℕ) * ((t + 1) * (t + 1)) = 2 ^ 2 * (2 ^ (s - 1) * 2 ^ (s - 1)) := by
      rw [ht]; norm_num
    rw [hrw, ← pow_add, ← pow_add, four_pow_eq_two_pow]
    congr 1
    omega
  have hsucc : (2 : ℕ) ^ (s + 1) = 4 * (t + 1) := by
    rw [← ht, show s + 1 = (s - 1) + 2 by omega, pow_add]
    ring
  have hden : (2 : ℕ) ^ (s - 1) - 1 = t := by omega
  rw [truncatedMersenneWeight, hden, h4, hsucc]
  refine Nat.div_eq_of_lt_le ?_ ?_
  · nlinarith
  · nlinarith

theorem remainder_le_of_skipsLast {s : ℕ} (hs : 4 ≤ s) (hskip : SkipsRank s (s - 1)) :
    seamIntegerGreedyRemainder s ≤ 2 ^ (s + 1) + 4 := by
  have h := remainder_add_tail_le_of_skipsRank (s := s) (a := s - 1)
    (by omega) (by omega) (by omega) hskip
  rw [show s - 1 + 1 = s by omega,
    seamWeightsFrom_eq_nil (s := s) (d := s) le_rfl, weight_last s hs] at h
  simpa using h

theorem obeysCeiling_of_skipsLast {s : ℕ} (hs : 4 ≤ s) (hskip : SkipsRank s (s - 1)) :
    ErdosProblems.BitR2.ObeysRemainderCeiling s := by
  have h := remainder_le_of_skipsLast hs hskip
  have hp : (2 : ℕ) ^ (s + 1) = 2 * 2 ^ s := by rw [pow_succ]; ring
  have h16 : (16 : ℕ) ≤ 2 ^ s := by
    calc (16 : ℕ) = 2 ^ 4 := by norm_num
      _ ≤ 2 ^ s := Nat.pow_le_pow_right (by norm_num) hs
  unfold ErdosProblems.BitR2.ObeysRemainderCeiling
  omega

/-! ### The C5 premise is empty -/

/-- Consecutive seam weights never come within `2 ^ s` of each other: the
adjacent gap is at least `2 ^ (s+1)`.  So the "two consecutive weights differ by
less than `2 ^ s`" hypothesis of the C5 programme is never satisfied. -/
theorem consecutive_gap_ge {s d : ℕ} (hs : 2 ≤ s) (hd : 1 ≤ d) (hds : d + 1 < s) :
    2 ^ (s + 1) + truncatedMersenneWeight s (d + 1) ≤ truncatedMersenneWeight s d := by
  have hgap := truncatedMersenneWeight_dominanceGap hs hd (by omega)
  have hsplit := tail_sum_succ (s := s) (d := d + 1) hds
  omega


/-! ## Non-vacuity: every hypothesis above is exhibited -/

section Witnesses

private theorem seamWeights_eight :
    seamWeights 8 = [21845, 9362, 4369, 2114, 1040, 516] := by
  unfold seamWeights
  rw [seamWeightsFrom_eq_cons (by norm_num : 2 < 8),
    seamWeightsFrom_eq_cons (by norm_num : 3 < 8),
    seamWeightsFrom_eq_cons (by norm_num : 4 < 8),
    seamWeightsFrom_eq_cons (by norm_num : 5 < 8),
    seamWeightsFrom_eq_cons (by norm_num : 6 < 8),
    seamWeightsFrom_eq_cons (by norm_num : 7 < 8),
    seamWeightsFrom_eq_nil (by norm_num : 8 ≤ 8)]
  norm_num [truncatedMersenneWeight]

/-- Row `8` skips its last rank `7`. -/
theorem skipsRank_eight : SkipsRank 8 7 := by
  unfold SkipsRank seamEnteringRemainder
  rw [seamWeights_eight,
    show seamSubsetTarget 8 = 32512 by norm_num [seamSubsetTarget],
    show truncatedMersenneWeight 8 7 = 516 by norm_num [truncatedMersenneWeight]]
  norm_num [integerGreedyRemainder, integerGreedyBits, weightedBoolSum]

theorem obeysCeiling_eight : ErdosProblems.BitR2.ObeysRemainderCeiling 8 :=
  obeysCeiling_of_skipsLast (by norm_num) (by simpa using skipsRank_eight)

/-! ### The ceiling at genuinely bad rows -/

private theorem seamWeights_eleven :
    seamWeights 11 =
      [1398101, 599186, 279620, 135300, 66576, 33026, 16448, 8208, 4100] := by
  unfold seamWeights
  rw [seamWeightsFrom_eq_cons (by norm_num : 2 < 11),
    seamWeightsFrom_eq_cons (by norm_num : 3 < 11),
    seamWeightsFrom_eq_cons (by norm_num : 4 < 11),
    seamWeightsFrom_eq_cons (by norm_num : 5 < 11),
    seamWeightsFrom_eq_cons (by norm_num : 6 < 11),
    seamWeightsFrom_eq_cons (by norm_num : 7 < 11),
    seamWeightsFrom_eq_cons (by norm_num : 8 < 11),
    seamWeightsFrom_eq_cons (by norm_num : 9 < 11),
    seamWeightsFrom_eq_cons (by norm_num : 10 < 11),
    seamWeightsFrom_eq_nil (by norm_num : 11 ≤ 11)]
  norm_num [truncatedMersenneWeight]

private theorem seamTail_eleven : (seamWeightsFrom 11 8).sum = 28756 := by
  rw [seamWeightsFrom_eq_cons (by norm_num : 8 < 11),
    seamWeightsFrom_eq_cons (by norm_num : 9 < 11),
    seamWeightsFrom_eq_cons (by norm_num : 10 < 11),
    seamWeightsFrom_eq_nil (by norm_num : 11 ≤ 11)]
  norm_num [truncatedMersenneWeight]

/-- Row `11` skips rank `7`. -/
theorem skipsRank_eleven : SkipsRank 11 7 := by
  unfold SkipsRank seamEnteringRemainder
  rw [seamWeights_eleven,
    show seamSubsetTarget 11 = 2095104 by norm_num [seamSubsetTarget],
    show truncatedMersenneWeight 11 7 = 33026 by norm_num [truncatedMersenneWeight]]
  norm_num [integerGreedyRemainder, integerGreedyBits, weightedBoolSum]

theorem obeysCeiling_eleven : ErdosProblems.BitR2.ObeysRemainderCeiling 11 := by
  refine obeysCeiling_of_skipsRank (s := 11) (a := 7) (by norm_num) (by norm_num)
    (by norm_num) skipsRank_eleven ?_
  rw [show (7 : ℕ) + 1 = 8 from rfl, seamTail_eleven,
    show truncatedMersenneWeight 11 7 = 33026 by norm_num [truncatedMersenneWeight]]
  norm_num

private theorem seamWeights_twelve :
    seamWeights 12 =
      [5592405, 2396745, 1118481, 541200, 266305, 132104, 65793, 32832, 16400,
        8196] := by
  unfold seamWeights
  rw [seamWeightsFrom_eq_cons (by norm_num : 2 < 12),
    seamWeightsFrom_eq_cons (by norm_num : 3 < 12),
    seamWeightsFrom_eq_cons (by norm_num : 4 < 12),
    seamWeightsFrom_eq_cons (by norm_num : 5 < 12),
    seamWeightsFrom_eq_cons (by norm_num : 6 < 12),
    seamWeightsFrom_eq_cons (by norm_num : 7 < 12),
    seamWeightsFrom_eq_cons (by norm_num : 8 < 12),
    seamWeightsFrom_eq_cons (by norm_num : 9 < 12),
    seamWeightsFrom_eq_cons (by norm_num : 10 < 12),
    seamWeightsFrom_eq_cons (by norm_num : 11 < 12),
    seamWeightsFrom_eq_nil (by norm_num : 12 ≤ 12)]
  norm_num [truncatedMersenneWeight]

private theorem seamTail_twelve : (seamWeightsFrom 12 8).sum = 123221 := by
  rw [seamWeightsFrom_eq_cons (by norm_num : 8 < 12),
    seamWeightsFrom_eq_cons (by norm_num : 9 < 12),
    seamWeightsFrom_eq_cons (by norm_num : 10 < 12),
    seamWeightsFrom_eq_cons (by norm_num : 11 < 12),
    seamWeightsFrom_eq_nil (by norm_num : 12 ≤ 12)]
  norm_num [truncatedMersenneWeight]

theorem skipsRank_twelve : SkipsRank 12 7 := by
  unfold SkipsRank seamEnteringRemainder
  rw [seamWeights_twelve,
    show seamSubsetTarget 12 = 8384512 by norm_num [seamSubsetTarget],
    show truncatedMersenneWeight 12 7 = 132104 by norm_num [truncatedMersenneWeight]]
  norm_num [integerGreedyRemainder, integerGreedyBits, weightedBoolSum]

theorem obeysCeiling_twelve : ErdosProblems.BitR2.ObeysRemainderCeiling 12 := by
  refine obeysCeiling_of_skipsRank (s := 12) (a := 7) (by norm_num) (by norm_num)
    (by norm_num) skipsRank_twelve ?_
  rw [show (7 : ℕ) + 1 = 8 from rfl, seamTail_twelve,
    show truncatedMersenneWeight 12 7 = 132104 by norm_num [truncatedMersenneWeight]]
  norm_num

/-- **The point of the localised bound.**  Rows `11` and `12` are *bad* — `Bit/R2`
proves `¬ LargestSkipLateAt` there, so its good-row ceiling
`three_mul_remainder_lt_of_largestSkipLateAt` says nothing — and yet the ceiling
holds, certified here from the skip at rank `7` alone. -/
theorem ceiling_at_bad_rows :
    (ErdosProblems.BitR2.ObeysRemainderCeiling 11 ∧ ¬ LargestSkipLateAt 11) ∧
      (ErdosProblems.BitR2.ObeysRemainderCeiling 12 ∧ ¬ LargestSkipLateAt 12) :=
  ⟨⟨obeysCeiling_eleven, ErdosProblems.BitR2.not_largestSkipLateAt_eleven⟩,
    ⟨obeysCeiling_twelve, ErdosProblems.BitR2.not_largestSkipLateAt_twelve⟩⟩

/-- The no-go, concretely at `s = 8`: the same weight word, at the admissible
capacity `w_2 - 1 = 21844`, leaves `4443`, which is `17` times `2 ^ 8 = 256`. -/
theorem counting_bound_sharp_eight :
    integerGreedyRemainder (seamWeights 8) (truncatedMersenneWeight 8 2 - 1) = 4443 := by
  rw [seamWeights_eight,
    show truncatedMersenneWeight 8 2 = 21845 by norm_num [truncatedMersenneWeight]]
  norm_num [integerGreedyRemainder, integerGreedyBits, weightedBoolSum]

end Witnesses


end ErdosProblems.RemC5
