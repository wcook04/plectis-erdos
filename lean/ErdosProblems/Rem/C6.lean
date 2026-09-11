import Erdos249257.HalfCylinderIntegerGreedy

/-!
# C6 — skipped-rank upper bounds for the seam integer-greedy remainder

This file was written as a *devil's advocate* pass on

  `RemainderReachesHalfPointCofinally := ∀ N, ∃ s, N ≤ s ∧ 5 ≤ s ∧ ρ s ≤ 2 ^ s`

where `ρ s = seamIntegerGreedyRemainder s`.  The refutation attempt failed
decisively (see the measurement note at the end of this file), so what is
recorded here is the positive structure that the failed refutation exposed.

The corpus already contains the unconditional counting bound
`RemC5.eight_mul_remainder_le : 8 * ρ s ≤ 4^s`.  This file supplies related
skipped-rank bounds and improves that estimate at rank `5`.

Contents.

* A reusable description of the descending integer greedy as a left fold:
  `integerGreedyRemainder_cons`, `integerGreedyRemainder_append`,
  `integerGreedyRemainder_le`.
* `integerGreedyRemainder_lt_of_skipped`: **the greedy remainder is strictly
  below every weight the greedy declines.**  This re-proves the corpus lever
  already available as
  `seamIntegerGreedyRemainder_lt_truncatedWeight_of_false`.
* `SeamSkipsAt s d`, the corpus-faithful statement that the seam greedy
  declines rank `d`, and `seamIntegerGreedyRemainder_lt_of_skip`.
* `truncatedMersenneWeight_late`: for `2 * s < 3 * d` and `d < s` the weight is
  *exactly* `2 ^ (2 * s - d) + 2 ^ (2 * s - 2 * d)` — two bits.  In particular
  `truncatedMersenneWeight s (s - 1) = 2 ^ (s + 1) + 4`.
* `seamIntegerGreedyRemainder_lt_of_late_skip` and
  `late_skip_beats_trivial`: a declined rank `d` past two thirds of the row
  forces `2 ^ (d - 2) * ρ s < 2 ^ (2 * s - 1)`, i.e. it beats the trivial bound
  by the exponential factor `2 ^ (d - 2) ≥ 2 ^ (⌊2 * s / 3⌋ - 1)`.
* `SeamSkipsLast s d` — `d` is the *largest* declined rank — and the resulting
  consequences.  The proof uses the higher-weight sum to cancel the leading
  term of the rank-`d` weight.  The adversarial verifier shows the same
  exponential estimate follows from a plain late skip together with the
  existing tail-domination bound, so maximality is not what buys the gain.
  - `seamIntegerGreedyRemainder_lt_of_largest_skip` (no lateness hypothesis):
    `ρ s < 2 ^ (2 * s - 2 * d + 1) + 2 ^ (s + 1)`.
  - `seamIntegerGreedyRemainder_lt_of_late_largest_skip`:
    `ρ s < 2 ^ (s + 1) + 2 ^ (2 * s - 2 * d)`, and hence
    `seamIntegerGreedyRemainder_lt_three_mul_two_pow`: **`ρ s < 3 * 2 ^ s`**.
  - `late_largest_skip_beats_trivial`: `2 ^ (s - 3) * ρ s < 2 ^ (2 * s - 1)`.
    That is the trivial bound improved by the factor `2 ^ (s - 3)`.
* An **unconditional** instance: ranks `4` and `5` are declined at every row
  `s ≥ 6`, hence `8 * ρ s < 2 ^ (2 * s - 1)` for all `s ≥ 6`
  (`seamIntegerGreedyRemainder_lt_of_rank_five`, `eight_mul_remainder_lt`).
* Anti-vacuity, proved outright: `SeamSkipsAt 14 13` and
  `seamSkipsLast_fourteen_thirteen` — a *late* skip (`2 * 14 < 3 * 13`) at the
  terminal rank — with the exact value `seamIntegerGreedyRemainder 14 = 392`;
  and `seamSkipsLast_sixteen_fourteen`, where the suffix above the largest
  declined rank is genuinely non-empty.

What this does **not** do: it does not prove the target.  The bound
`ρ s < 3 * 2 ^ s` at a late row is now within a constant factor of the target
`ρ s ≤ 2 ^ s`, but a constant factor is exactly the room the descent law needs
(see the measurement note below).
-/

namespace ErdosProblems.RemC6

open Erdos249257 Erdos249257.HalfCylinderIntegerGreedy

/-! ## 1. The descending integer greedy as a left fold -/

theorem integerGreedyRemainder_nil (C : ℕ) : integerGreedyRemainder [] C = C := rfl

/-- One step of the descending greedy. -/
theorem integerGreedyRemainder_cons (w : ℕ) (ws : List ℕ) (C : ℕ) :
    integerGreedyRemainder (w :: ws) C
      = integerGreedyRemainder ws (if w ≤ C then C - w else C) := by
  by_cases h : w ≤ C
  · have hadm := integerGreedyBits_admissible ws (C - w)
    simp only [integerGreedyRemainder, integerGreedyBits, if_pos h, weightedBoolSum]
    omega
  · simp only [integerGreedyRemainder, integerGreedyBits, if_neg h, weightedBoolSum]

/-- The greedy never increases the capacity. -/
theorem integerGreedyRemainder_le (ws : List ℕ) (C : ℕ) :
    integerGreedyRemainder ws C ≤ C := by
  induction ws generalizing C with
  | nil => exact le_of_eq (integerGreedyRemainder_nil C)
  | cons w ws ih =>
      rw [integerGreedyRemainder_cons]
      by_cases h : w ≤ C
      · simp only [if_pos h]
        exact le_trans (ih (C - w)) (by omega)
      · simp only [if_neg h]
        exact ih C

/-- The greedy on a concatenation is the greedy on the tail started from the
remainder of the head. -/
theorem integerGreedyRemainder_append (pre post : List ℕ) (C : ℕ) :
    integerGreedyRemainder (pre ++ post) C
      = integerGreedyRemainder post (integerGreedyRemainder pre C) := by
  induction pre generalizing C with
  | nil => simp [integerGreedyRemainder_nil]
  | cons w pre ih =>
      simp only [List.cons_append, integerGreedyRemainder_cons, ih]

/-- **The lever.**  If the descending greedy reaches a weight `w` with a
residual strictly below `w`, then the *final* remainder is strictly below `w`
as well: everything after that point only shrinks the residual. -/
theorem integerGreedyRemainder_lt_of_skipped
    (pre post : List ℕ) (w C : ℕ)
    (h : integerGreedyRemainder pre C < w) :
    integerGreedyRemainder (pre ++ w :: post) C < w := by
  rw [integerGreedyRemainder_append, integerGreedyRemainder_cons,
    if_neg (not_le.mpr h)]
  exact lt_of_le_of_lt (integerGreedyRemainder_le post _) h

/-! ## 2. Declined ranks of the seam greedy -/

/-- The seam weight word splits at every rank. -/
theorem seamWeightsFrom_split (s : ℕ) {a b : ℕ} (hab : a ≤ b) :
    ∃ pre : List ℕ, seamWeightsFrom s a = pre ++ seamWeightsFrom s b := by
  induction b, hab using Nat.le_induction with
  | base => exact ⟨[], by simp⟩
  | succ b hab ih =>
      obtain ⟨pre, hpre⟩ := ih
      by_cases hbs : b < s
      · refine ⟨pre ++ [truncatedMersenneWeight s b], ?_⟩
        rw [hpre, seamWeightsFrom_eq_cons hbs]
        simp
      · refine ⟨pre, ?_⟩
        rw [hpre, seamWeightsFrom_eq_nil (by omega : s ≤ b),
          seamWeightsFrom_eq_nil (by omega : s ≤ b + 1)]

/-- Rank `d` is *declined* by the descending seam greedy at row `s`: the
residual left after ranks `2,…,d-1` have been offered is strictly below the
rank-`d` weight.  This is stated purely in terms of the corpus's own
`seamWeights`, `seamSubsetTarget`, `truncatedMersenneWeight` and
`integerGreedyRemainder`. -/
def SeamSkipsAt (s d : ℕ) : Prop :=
  ∃ pre : List ℕ,
    seamWeights s = pre ++ seamWeightsFrom s d ∧
      integerGreedyRemainder pre (seamSubsetTarget s) < truncatedMersenneWeight s d

/-- A declined rank bounds the whole remainder. -/
theorem seamIntegerGreedyRemainder_lt_of_skip {s d : ℕ} (hds : d < s)
    (h : SeamSkipsAt s d) :
    seamIntegerGreedyRemainder s < truncatedMersenneWeight s d := by
  obtain ⟨pre, hsplit, hlt⟩ := h
  have hcons :
      seamWeights s
        = pre ++ truncatedMersenneWeight s d :: seamWeightsFrom s (d + 1) := by
    rw [hsplit, seamWeightsFrom_eq_cons hds]
  show integerGreedyRemainder (seamWeights s) (seamSubsetTarget s) < _
  rw [hcons]
  exact integerGreedyRemainder_lt_of_skipped _ _ _ _ hlt

/-! ## 3. The exact shape of a late weight -/

/-- **Two-bit closed form.**  Past two thirds of the row the truncated
Mersenne weight is exactly a sum of two powers of two. -/
theorem truncatedMersenneWeight_late {s d : ℕ}
    (hd : 2 ≤ d) (hds : d < s) (hlate : 2 * s < 3 * d) :
    truncatedMersenneWeight s d = 2 ^ (2 * s - d) + 2 ^ (2 * s - 2 * d) := by
  have hq : (2 * s) / d = 2 := by
    refine Nat.div_eq_of_lt_le ?_ ?_ <;> omega
  have hr : (2 * s) % d = 2 * s - 2 * d := by
    have hdm := Nat.div_add_mod (2 * s) d
    rw [hq] at hdm
    omega
  rw [truncatedMersenneWeight_eq_geometricCore hd, hq, hr]
  rw [Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_zero]
  have hexp : 2 * s - 2 * d + d = 2 * s - d := by omega
  calc
    2 ^ (2 * s - 2 * d) * (0 + (2 ^ d) ^ 0 + (2 ^ d) ^ 1)
        = 2 ^ (2 * s - 2 * d) + 2 ^ (2 * s - 2 * d + d) := by
          rw [pow_zero, pow_one, pow_add]
          ring
    _ = 2 ^ (2 * s - d) + 2 ^ (2 * s - 2 * d) := by rw [hexp]; ring

/-- The terminal rank of row `s` carries weight exactly `2 ^ (s + 1) + 4`. -/
theorem truncatedMersenneWeight_terminal {s : ℕ} (hs : 4 ≤ s) :
    truncatedMersenneWeight s (s - 1) = 2 ^ (s + 1) + 4 := by
  have h := truncatedMersenneWeight_late (s := s) (d := s - 1)
    (by omega) (by omega) (by omega)
  have e1 : 2 * s - (s - 1) = s + 1 := by omega
  have e2 : 2 * s - 2 * (s - 1) = 2 := by omega
  rw [h, e1, e2]
  norm_num

/-! ## 4. A late declined rank beats the trivial bound exponentially -/

/-- A declined rank past two thirds of the row pins the remainder below
`2 ^ (2 * s - d + 1)`. -/
theorem seamIntegerGreedyRemainder_lt_of_late_skip {s d : ℕ}
    (hd : 2 ≤ d) (hds : d < s) (hlate : 2 * s < 3 * d) (h : SeamSkipsAt s d) :
    seamIntegerGreedyRemainder s < 2 ^ (2 * s - d + 1) := by
  have hbound := seamIntegerGreedyRemainder_lt_of_skip hds h
  rw [truncatedMersenneWeight_late hd hds hlate] at hbound
  have hmono : (2 : ℕ) ^ (2 * s - 2 * d) ≤ 2 ^ (2 * s - d) :=
    Nat.pow_le_pow_right (by norm_num) (by omega)
  have hsum : (2 : ℕ) ^ (2 * s - d) + 2 ^ (2 * s - d) = 2 ^ (2 * s - d + 1) := by
    rw [pow_succ]; ring
  omega

/-- The corpus's trivial unconditional bound is `ρ s ≤ 2 ^ (2 * s - 1) - 2 ^ s`.
A declined rank `d` improves it by the factor `2 ^ (d - 2)`. -/
theorem late_skip_beats_trivial {s d : ℕ}
    (hd : 2 ≤ d) (hds : d < s) (hlate : 2 * s < 3 * d) (h : SeamSkipsAt s d) :
    2 ^ (d - 2) * seamIntegerGreedyRemainder s < 2 ^ (2 * s - 1) := by
  have hbound := seamIntegerGreedyRemainder_lt_of_late_skip hd hds hlate h
  have hpos : 0 < (2 : ℕ) ^ (d - 2) := pow_pos (by norm_num) _
  calc
    2 ^ (d - 2) * seamIntegerGreedyRemainder s
        < 2 ^ (d - 2) * 2 ^ (2 * s - d + 1) :=
          mul_lt_mul_of_pos_left hbound hpos
    _ = 2 ^ (d - 2 + (2 * s - d + 1)) := (pow_add 2 _ _).symm
    _ = 2 ^ (2 * s - 1) := by
          congr 1
          omega

/-! ## 5. The largest declined rank: a bound of order `2 ^ (s+1)`

Knowing merely that rank `d` is declined gives `ρ s < w d ≈ 2 ^ (2*s-d)`.  Knowing
that `d` is the *largest* declined rank gives far more: everything above `d` is
then taken, and the weights above `d` already sum to `2 ^ (2*s-d) - 2 ^ (s+1)`,
which cancels the leading term of `w d` outright. -/

/-- If the remaining weights fit inside the capacity, the greedy takes all of
them. -/
theorem integerGreedyRemainder_eq_of_sum_le (ws : List ℕ) (C : ℕ) (h : ws.sum ≤ C) :
    integerGreedyRemainder ws C = C - ws.sum := by
  induction ws generalizing C with
  | nil => simp [integerGreedyRemainder_nil]
  | cons w ws ih =>
      rw [List.sum_cons] at h ⊢
      have hw : w ≤ C := by omega
      rw [integerGreedyRemainder_cons, if_pos hw, ih (C - w) (by omega)]
      omega

/-- Every truncated Mersenne weight dominates the power of two carrying its
top bit. -/
theorem two_pow_le_truncatedMersenneWeight {s d : ℕ} (hd : 1 ≤ d) (hds : d ≤ 2 * s) :
    2 ^ (2 * s - d) ≤ truncatedMersenneWeight s d := by
  have hpos : 0 < 2 ^ d - 1 := by
    have : (2 : ℕ) ^ 1 ≤ 2 ^ d := Nat.pow_le_pow_right (by norm_num) hd
    simp only [pow_one] at this
    omega
  show 2 ^ (2 * s - d) ≤ 4 ^ s / (2 ^ d - 1)
  rw [Nat.le_div_iff_mul_le hpos]
  calc
    2 ^ (2 * s - d) * (2 ^ d - 1) ≤ 2 ^ (2 * s - d) * 2 ^ d :=
      Nat.mul_le_mul_left _ (by omega)
    _ = 2 ^ (2 * s) := by rw [← pow_add]; congr 1; omega
    _ = 4 ^ s := by rw [pow_mul]; norm_num

/-- Companion upper bound: the weight exceeds its top bit by less than
`2 ^ (2*s-2*d+1)`.  (Valid at every rank, not only the late ones.) -/
theorem truncatedMersenneWeight_le {s d : ℕ} (hd : 1 ≤ d) (hds : d ≤ s) :
    truncatedMersenneWeight s d ≤ 2 ^ (2 * s - d) + 2 ^ (2 * s - 2 * d + 1) := by
  set X : ℕ := 2 ^ (2 * s - d) + 2 ^ (2 * s - 2 * d + 1) with hX
  have hP : (1 : ℕ) ≤ 2 ^ d := Nat.one_le_two_pow
  have hP2 : (2 : ℕ) ≤ 2 ^ d := by
    have : (2 : ℕ) ^ 1 ≤ 2 ^ d := Nat.pow_le_pow_right (by norm_num) hd
    simpa using this
  have hpos : 0 < 2 ^ d - 1 := by omega
  have hmul : (X + 1) * (2 ^ d - 1) + (X + 1) = (X + 1) * 2 ^ d := by
    rw [← Nat.mul_succ, Nat.succ_eq_add_one, Nat.sub_add_cancel hP]
  have hexp : (X + 1) * 2 ^ d = 2 ^ (2 * s) + 2 ^ (2 * s - d + 1) + 2 ^ d := by
    have e1 : (2 : ℕ) ^ (2 * s - d) * 2 ^ d = 2 ^ (2 * s) := by
      rw [← pow_add]; congr 1; omega
    have e2 : (2 : ℕ) ^ (2 * s - 2 * d + 1) * 2 ^ d = 2 ^ (2 * s - d + 1) := by
      rw [← pow_add]; congr 1; omega
    rw [hX]
    calc
      (2 ^ (2 * s - d) + 2 ^ (2 * s - 2 * d + 1) + 1) * 2 ^ d
          = 2 ^ (2 * s - d) * 2 ^ d + 2 ^ (2 * s - 2 * d + 1) * 2 ^ d + 2 ^ d := by ring
      _ = 2 ^ (2 * s) + 2 ^ (2 * s - d + 1) + 2 ^ d := by rw [e1, e2]
  have hdbl : (2 : ℕ) ^ (2 * s - d + 1) = 2 ^ (2 * s - d) + 2 ^ (2 * s - d) := by
    rw [pow_succ]; ring
  have hcmp : (2 : ℕ) ^ (2 * s - 2 * d + 1) ≤ 2 ^ (2 * s - d) :=
    Nat.pow_le_pow_right (by norm_num) (by omega)
  have hkey : 4 ^ s < (X + 1) * (2 ^ d - 1) := by
    have h4 : (4 : ℕ) ^ s = 2 ^ (2 * s) := by rw [pow_mul]; norm_num
    omega
  have hlt : 4 ^ s / (2 ^ d - 1) < X + 1 := (Nat.div_lt_iff_lt_mul hpos).mpr hkey
  show 4 ^ s / (2 ^ d - 1) ≤ X
  omega

/-- The suffix of seam weights from rank `a` onwards already sums to
`2 ^ (2*s-a+1) - 2 ^ (s+1)`. -/
private theorem seamWeightsFrom_sum_lower_aux (s : ℕ) :
    ∀ n : ℕ, n + 2 ≤ s →
      2 ^ (s + n + 1) ≤ (seamWeightsFrom s (s - n)).sum + 2 ^ (s + 1) := by
  intro n
  induction n with
  | zero =>
      intro _
      simp [seamWeightsFrom_eq_nil (le_refl s)]
  | succ n ih =>
      intro hn
      have hlt : s - (n + 1) < s := by omega
      have heq : s - (n + 1) + 1 = s - n := by omega
      have hIH := ih (by omega)
      have hw : 2 ^ (s + n + 1) ≤ truncatedMersenneWeight s (s - (n + 1)) := by
        have h := two_pow_le_truncatedMersenneWeight
          (s := s) (d := s - (n + 1)) (by omega) (by omega)
        rwa [show 2 * s - (s - (n + 1)) = s + n + 1 by omega] at h
      have hdouble : (2 : ℕ) ^ (s + (n + 1) + 1) = 2 ^ (s + n + 1) + 2 ^ (s + n + 1) := by
        rw [show s + (n + 1) + 1 = (s + n + 1) + 1 by omega, pow_succ]
        ring
      rw [seamWeightsFrom_eq_cons hlt, List.sum_cons, heq]
      omega

theorem seamWeightsFrom_sum_lower {s a : ℕ} (ha2 : 2 ≤ a) (ha : a ≤ s) :
    2 ^ (2 * s - a + 1) ≤ (seamWeightsFrom s a).sum + 2 ^ (s + 1) := by
  have h := seamWeightsFrom_sum_lower_aux s (s - a) (by omega)
  rw [show s - (s - a) = a by omega] at h
  rw [show 2 * s - a + 1 = s + (s - a) + 1 by omega]
  exact h

/-- `d` is the **largest** rank declined by the seam greedy at row `s`: the
residual after ranks `2,…,d-1` sits strictly below the rank-`d` weight (so `d`
is declined) and weakly above the total of all higher-rank weights (so every
rank above `d` is taken). -/
def SeamSkipsLast (s d : ℕ) : Prop :=
  ∃ pre : List ℕ,
    seamWeights s = pre ++ seamWeightsFrom s d ∧
      integerGreedyRemainder pre (seamSubsetTarget s) < truncatedMersenneWeight s d ∧
      (seamWeightsFrom s (d + 1)).sum
        ≤ integerGreedyRemainder pre (seamSubsetTarget s)

theorem SeamSkipsLast.toSkipsAt {s d : ℕ} (h : SeamSkipsLast s d) : SeamSkipsAt s d := by
  obtain ⟨pre, hsplit, hlt, _⟩ := h
  exact ⟨pre, hsplit, hlt⟩

/-- Exact evaluation of the remainder from a largest declined rank. -/
theorem seamIntegerGreedyRemainder_eq_of_skipsLast {s d : ℕ} (hds : d < s)
    (h : SeamSkipsLast s d) :
    ∃ R : ℕ,
      R < truncatedMersenneWeight s d ∧
        (seamWeightsFrom s (d + 1)).sum ≤ R ∧
          seamIntegerGreedyRemainder s = R - (seamWeightsFrom s (d + 1)).sum := by
  obtain ⟨pre, hsplit, hlt, hfill⟩ := h
  refine ⟨integerGreedyRemainder pre (seamSubsetTarget s), hlt, hfill, ?_⟩
  have hcons :
      seamWeights s
        = pre ++ truncatedMersenneWeight s d :: seamWeightsFrom s (d + 1) := by
    rw [hsplit, seamWeightsFrom_eq_cons hds]
  show integerGreedyRemainder (seamWeights s) (seamSubsetTarget s) = _
  rw [hcons, integerGreedyRemainder_append, integerGreedyRemainder_cons,
    if_neg (not_le.mpr hlt)]
  exact integerGreedyRemainder_eq_of_sum_le _ _ hfill

/-- **The bound the project was missing.**  If the largest declined rank of row
`s` lies past two thirds of the row, the remainder is below
`2 ^ (s + 1) + 2 ^ (2 * s - 2 * d)` — for late `d` an exponentially sharper
statement than the trivial `ρ s ≤ 2 ^ (2 * s - 1) - 2 ^ s`. -/
theorem seamIntegerGreedyRemainder_lt_of_late_largest_skip {s d : ℕ}
    (hd : 2 ≤ d) (hds : d < s) (hlate : 2 * s < 3 * d) (h : SeamSkipsLast s d) :
    seamIntegerGreedyRemainder s < 2 ^ (s + 1) + 2 ^ (2 * s - 2 * d) := by
  obtain ⟨R, hR1, hR2, hR3⟩ := seamIntegerGreedyRemainder_eq_of_skipsLast hds h
  rw [truncatedMersenneWeight_late hd hds hlate] at hR1
  have hsum := seamWeightsFrom_sum_lower (s := s) (a := d + 1) (by omega) (by omega)
  rw [show 2 * s - (d + 1) + 1 = 2 * s - d by omega] at hsum
  omega

/-- **The bound at an arbitrary row.**  With no lateness hypothesis at all: if
`d` is the largest declined rank of row `s` then
`ρ s < 2 ^ (2 * s - 2 * d + 1) + 2 ^ (s + 1)`.  The whole `4 ^ s` scale of the
trivial bound is gone; what is left is governed by `d` alone. -/
theorem seamIntegerGreedyRemainder_lt_of_largest_skip {s d : ℕ}
    (hd : 2 ≤ d) (hds : d < s) (h : SeamSkipsLast s d) :
    seamIntegerGreedyRemainder s < 2 ^ (2 * s - 2 * d + 1) + 2 ^ (s + 1) := by
  obtain ⟨R, hR1, hR2, hR3⟩ := seamIntegerGreedyRemainder_eq_of_skipsLast hds h
  have hup := truncatedMersenneWeight_le (s := s) (d := d) (by omega) (by omega)
  have hsum := seamWeightsFrom_sum_lower (s := s) (a := d + 1) (by omega) (by omega)
  rw [show 2 * s - (d + 1) + 1 = 2 * s - d by omega] at hsum
  omega

/-- The same, collapsed: a late largest declined rank forces `ρ s < 3 * 2 ^ s`. -/
theorem seamIntegerGreedyRemainder_lt_three_mul_two_pow {s d : ℕ}
    (hd : 2 ≤ d) (hds : d < s) (hlate : 2 * s < 3 * d) (h : SeamSkipsLast s d) :
    seamIntegerGreedyRemainder s < 3 * 2 ^ s := by
  have hb := seamIntegerGreedyRemainder_lt_of_late_largest_skip hd hds hlate h
  have hle : (2 : ℕ) ^ (2 * s - 2 * d) ≤ 2 ^ s :=
    Nat.pow_le_pow_right (by norm_num) (by omega)
  have hsucc : (2 : ℕ) ^ (s + 1) = 2 * 2 ^ s := by rw [pow_succ]; ring
  omega

/-- Comparison with the corpus's trivial unconditional bound
`ρ s ≤ 2 ^ (2 * s - 1) - 2 ^ s`: a late largest declined rank improves it by the
factor `2 ^ (s - 3)`. -/
theorem late_largest_skip_beats_trivial {s d : ℕ}
    (hs : 3 ≤ s) (hd : 2 ≤ d) (hds : d < s) (hlate : 2 * s < 3 * d)
    (h : SeamSkipsLast s d) :
    2 ^ (s - 3) * seamIntegerGreedyRemainder s < 2 ^ (2 * s - 1) := by
  have hb := seamIntegerGreedyRemainder_lt_three_mul_two_pow hd hds hlate h
  have hpos : 0 < (2 : ℕ) ^ (s - 3) := pow_pos (by norm_num) _
  have hb' : seamIntegerGreedyRemainder s < 2 ^ (s + 2) := by
    have : (2 : ℕ) ^ (s + 2) = 4 * 2 ^ s := by rw [pow_add]; ring
    omega
  calc
    2 ^ (s - 3) * seamIntegerGreedyRemainder s < 2 ^ (s - 3) * 2 ^ (s + 2) :=
      mul_lt_mul_of_pos_left hb' hpos
    _ = 2 ^ (s - 3 + (s + 2)) := (pow_add 2 _ _).symm
    _ = 2 ^ (2 * s - 1) := by congr 1; omega

/-! ## 6. An unconditional instance: ranks 4 and 5 are always declined -/

private theorem four_pow_eq (s : ℕ) : (4 : ℕ) ^ s = 2 ^ s * 2 ^ s := by
  rw [show (4 : ℕ) = 2 * 2 by norm_num, mul_pow]

private theorem seamSubsetTarget_two_mul (s : ℕ) (hs : 1 ≤ s) :
    2 * seamSubsetTarget s = 4 ^ s - 2 * 2 ^ s := by
  have h1 : (2 : ℕ) ^ (2 * s - 1) * 2 = 4 ^ s := by
    rw [← pow_succ, show 2 * s - 1 + 1 = 2 * s by omega, pow_mul]
    norm_num
  have h2 : (2 : ℕ) ^ s ≤ 2 ^ (2 * s - 1) :=
    Nat.pow_le_pow_right (by norm_num) (by omega)
  show 2 * (2 ^ (2 * s - 1) - 2 ^ s) = _
  omega

/-- After ranks `2` and `3` the residual of row `s` (`s ≥ 6`) is below
`4 ^ s / 31`, hence ranks `4` and `5` are both declined. -/
theorem seamSkipsAt_five {s : ℕ} (hs : 6 ≤ s) : SeamSkipsAt s 5 := by
  obtain ⟨pre, hpre⟩ := seamWeightsFrom_split s (a := 2) (b := 5) (by norm_num)
  have hpre2 : seamWeightsFrom s 2
      = truncatedMersenneWeight s 2 :: truncatedMersenneWeight s 3
          :: truncatedMersenneWeight s 4 :: seamWeightsFrom s 5 := by
    rw [seamWeightsFrom_eq_cons (by omega : 2 < s),
      seamWeightsFrom_eq_cons (by omega : 3 < s),
      seamWeightsFrom_eq_cons (by omega : 4 < s)]
  -- abbreviations
  set A : ℕ := 4 ^ s with hA
  set B : ℕ := 2 ^ s with hB
  have hAB : A = B * B := four_pow_eq s
  have hB64 : 64 ≤ B := by
    calc (64 : ℕ) = 2 ^ 6 := by norm_num
    _ ≤ 2 ^ s := Nat.pow_le_pow_right (by norm_num) hs
  have hAge : 64 * B ≤ A := by
    rw [hAB]; exact Nat.mul_le_mul_right B hB64
  -- floor facts for the four weights
  have w2 : truncatedMersenneWeight s 2 = A / 3 := by
    simp [truncatedMersenneWeight, hA]
  have w3 : truncatedMersenneWeight s 3 = A / 7 := by
    simp [truncatedMersenneWeight, hA]
  have w4 : truncatedMersenneWeight s 4 = A / 15 := by
    simp [truncatedMersenneWeight, hA]
  have w5 : truncatedMersenneWeight s 5 = A / 31 := by
    simp [truncatedMersenneWeight, hA]
  have d3 := Nat.div_add_mod A 3
  have d3' : A % 3 < 3 := Nat.mod_lt _ (by norm_num)
  have d7 := Nat.div_add_mod A 7
  have d7' : A % 7 < 7 := Nat.mod_lt _ (by norm_num)
  have d15 := Nat.div_add_mod A 15
  have d15' : A % 15 < 15 := Nat.mod_lt _ (by norm_num)
  have d31 := Nat.div_add_mod A 31
  have d31' : A % 31 < 31 := Nat.mod_lt _ (by norm_num)
  have htarget : 2 * seamSubsetTarget s = A - 2 * B :=
    seamSubsetTarget_two_mul s (by omega)
  have hT2 : 2 * seamSubsetTarget s + 2 * B = A := by
    have : 2 * B ≤ A := by omega
    omega
  -- rank 2 is taken
  have htake2 : A / 3 ≤ seamSubsetTarget s := by omega
  -- rank 3 is taken
  have htake3 : A / 7 ≤ seamSubsetTarget s - A / 3 := by omega
  -- the residual after ranks 2 and 3
  have hres : integerGreedyRemainder
      [truncatedMersenneWeight s 2, truncatedMersenneWeight s 3]
        (seamSubsetTarget s) = seamSubsetTarget s - A / 3 - A / 7 := by
    rw [w2, w3, integerGreedyRemainder_cons, if_pos htake2,
      integerGreedyRemainder_cons, if_pos htake3, integerGreedyRemainder_nil]
  refine ⟨[truncatedMersenneWeight s 2, truncatedMersenneWeight s 3,
      truncatedMersenneWeight s 4], ?_, ?_⟩
  · show seamWeightsFrom s 2 = _
    rw [hpre2]; rfl
  · rw [w5, integerGreedyRemainder_cons, integerGreedyRemainder_cons,
      integerGreedyRemainder_cons, integerGreedyRemainder_nil]
    rw [w2, if_pos htake2, w3, if_pos htake3, w4]
    have hskip4 : ¬ (A / 15 ≤ seamSubsetTarget s - A / 3 - A / 7) := by omega
    rw [if_neg hskip4]
    omega

/-- **Unconditional.**  For every row `s ≥ 6` the seam integer-greedy
remainder is strictly below `4 ^ s / 31`. -/
theorem seamIntegerGreedyRemainder_lt_of_rank_five {s : ℕ} (hs : 6 ≤ s) :
    seamIntegerGreedyRemainder s < 4 ^ s / 31 := by
  have h := seamIntegerGreedyRemainder_lt_of_skip (d := 5) (by omega)
    (seamSkipsAt_five hs)
  simpa [truncatedMersenneWeight] using h

/-- The same statement in the shape that compares directly with the corpus's
trivial bound `ρ s ≤ 2 ^ (2 * s - 1) - 2 ^ s`. -/
theorem eight_mul_remainder_lt {s : ℕ} (hs : 6 ≤ s) :
    8 * seamIntegerGreedyRemainder s < 2 ^ (2 * s - 1) := by
  have h := seamIntegerGreedyRemainder_lt_of_rank_five hs
  have hd := Nat.div_add_mod (4 ^ s) 31
  have hd' : 4 ^ s % 31 < 31 := Nat.mod_lt _ (by norm_num)
  have hpow : (2 : ℕ) ^ (2 * s - 1) * 2 = 4 ^ s := by
    rw [← pow_succ, show 2 * s - 1 + 1 = 2 * s by omega, pow_mul]
    norm_num
  omega

/-! ## 7. Anti-vacuity: concrete late largest-skips -/

private theorem seamWeightsFrom_fourteen_two :
    seamWeightsFrom 14 2
      = [89478485, 38347922, 17895697, 8659208, 4260880, 2113665,
          1052688, 525314, 262400, 131136, 65552] ++ seamWeightsFrom 14 13 := by
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
    seamWeightsFrom_eq_cons (by norm_num : 12 < 14)]
  norm_num [truncatedMersenneWeight]

/-- Row 14 declines its terminal rank 13, and `2 * 14 < 3 * 13`, so this is a
*late* skip.  The hypothesis of every theorem in §4 is therefore satisfiable. -/
theorem seamSkipsAt_fourteen_thirteen : SeamSkipsAt 14 13 := by
  refine ⟨[89478485, 38347922, 17895697, 8659208, 4260880, 2113665,
      1052688, 525314, 262400, 131136, 65552], ?_, ?_⟩
  · show seamWeightsFrom 14 2 = _
    exact seamWeightsFrom_fourteen_two
  · have hw : truncatedMersenneWeight 14 13 = 32772 := by
      norm_num [truncatedMersenneWeight]
    rw [hw]
    norm_num [seamSubsetTarget, integerGreedyRemainder_cons,
      integerGreedyRemainder_nil]

/-- The row-14 instance of §4, with the exact numbers. -/
theorem seamIntegerGreedyRemainder_fourteen_lt :
    seamIntegerGreedyRemainder 14 < 2 ^ (14 + 1) + 4 := by
  have h := seamIntegerGreedyRemainder_lt_of_skip
    (s := 14) (d := 13) (by norm_num) seamSkipsAt_fourteen_thirteen
  rwa [show truncatedMersenneWeight 14 13 = 2 ^ (14 + 1) + 4 by
    norm_num [truncatedMersenneWeight]] at h

/-- Row 14 is an explicit *hit* for the target inequality `ρ s ≤ 2 ^ s`:
`seamIntegerGreedyRemainder 14 = 392 ≤ 16384`.  Recorded so that no statement
above is vacuous about the target itself. -/
theorem seamIntegerGreedyRemainder_fourteen : seamIntegerGreedyRemainder 14 = 392 := by
  show integerGreedyRemainder (seamWeights 14) (seamSubsetTarget 14) = 392
  have hw : seamWeights 14
      = [89478485, 38347922, 17895697, 8659208, 4260880, 2113665,
          1052688, 525314, 262400, 131136, 65552, 32772] := by
    show seamWeightsFrom 14 2 = _
    rw [seamWeightsFrom_fourteen_two,
      seamWeightsFrom_eq_cons (by norm_num : 13 < 14),
      seamWeightsFrom_eq_nil (by norm_num : 14 ≤ 14)]
    norm_num [truncatedMersenneWeight]
  rw [hw]
  norm_num [seamSubsetTarget, integerGreedyRemainder_cons,
    integerGreedyRemainder_nil]

theorem seamIntegerGreedyRemainder_fourteen_le_two_pow :
    seamIntegerGreedyRemainder 14 ≤ 2 ^ 14 := by
  rw [seamIntegerGreedyRemainder_fourteen]; norm_num

/-- Rank `13` is also the *largest* declined rank of row `14` (there is nothing
above it), so `SeamSkipsLast` is inhabited. -/
theorem seamSkipsLast_fourteen_thirteen : SeamSkipsLast 14 13 := by
  obtain ⟨pre, hsplit, hlt⟩ := seamSkipsAt_fourteen_thirteen
  refine ⟨pre, hsplit, hlt, ?_⟩
  rw [seamWeightsFrom_eq_nil (by norm_num : (14 : ℕ) ≤ 13 + 1)]
  simp

/-- Row `16` has largest declined rank `14`, with rank `15` genuinely taken —
so the higher-rank sum in `SeamSkipsLast` is not degenerate. -/
private theorem seamWeightsFrom_sixteen_two :
    seamWeightsFrom 16 2
      = [1431655765, 613566756, 286331153, 138547332, 68174084, 33818640,
          16843009, 8405024, 4198404, 2098176, 1048832, 524352]
        ++ seamWeightsFrom 16 14 := by
  rw [seamWeightsFrom_eq_cons (by norm_num : 2 < 16),
    seamWeightsFrom_eq_cons (by norm_num : 3 < 16),
    seamWeightsFrom_eq_cons (by norm_num : 4 < 16),
    seamWeightsFrom_eq_cons (by norm_num : 5 < 16),
    seamWeightsFrom_eq_cons (by norm_num : 6 < 16),
    seamWeightsFrom_eq_cons (by norm_num : 7 < 16),
    seamWeightsFrom_eq_cons (by norm_num : 8 < 16),
    seamWeightsFrom_eq_cons (by norm_num : 9 < 16),
    seamWeightsFrom_eq_cons (by norm_num : 10 < 16),
    seamWeightsFrom_eq_cons (by norm_num : 11 < 16),
    seamWeightsFrom_eq_cons (by norm_num : 12 < 16),
    seamWeightsFrom_eq_cons (by norm_num : 13 < 16)]
  norm_num [truncatedMersenneWeight]

theorem seamSkipsLast_sixteen_fourteen : SeamSkipsLast 16 14 := by
  have hsuffix : seamWeightsFrom 16 15 = [131076] := by
    rw [seamWeightsFrom_eq_cons (by norm_num : 15 < 16),
      seamWeightsFrom_eq_nil (by norm_num : (16 : ℕ) ≤ 16)]
    norm_num [truncatedMersenneWeight]
  have hres :
      integerGreedyRemainder
        [1431655765, 613566756, 286331153, 138547332, 68174084, 33818640,
          16843009, 8405024, 4198404, 2098176, 1048832, 524352]
        (seamSubsetTarget 16) = 202867 := by
    norm_num [seamSubsetTarget, integerGreedyRemainder_cons,
      integerGreedyRemainder_nil]
  refine ⟨[1431655765, 613566756, 286331153, 138547332, 68174084, 33818640,
      16843009, 8405024, 4198404, 2098176, 1048832, 524352], ?_, ?_, ?_⟩
  · show seamWeightsFrom 16 2 = _
    exact seamWeightsFrom_sixteen_two
  · rw [hres, show truncatedMersenneWeight 16 14 = 262160 by
      norm_num [truncatedMersenneWeight]]
    norm_num
  · rw [hres, hsuffix]
    norm_num

/-- The headline bound of §5, instantiated at row `16`:
`ρ 16 < 2 ^ 17 + 2 ^ 4 = 131088`, against the trivial bound
`ρ 16 ≤ 2 ^ 31 - 2 ^ 16 = 2147418112`.  (The true value is `71791`.) -/
theorem seamIntegerGreedyRemainder_sixteen_lt :
    seamIntegerGreedyRemainder 16 < 2 ^ (16 + 1) + 2 ^ (2 * 16 - 2 * 14) :=
  seamIntegerGreedyRemainder_lt_of_late_largest_skip
    (by norm_num) (by norm_num) (by norm_num) seamSkipsLast_sixteen_fourteen

theorem seamIntegerGreedyRemainder_sixteen_lt_three_mul :
    seamIntegerGreedyRemainder 16 < 3 * 2 ^ 16 :=
  seamIntegerGreedyRemainder_lt_three_mul_two_pow
    (by norm_num) (by norm_num) (by norm_num) seamSkipsLast_sixteen_fourteen

/-!
## Measurement note (not a theorem — recorded for the record)

The refutation target was: does `ρ s ≤ 2 ^ s` fail for all large `s`?  Using
the corpus definitions verbatim (`seamWeights`, `seamSubsetTarget`,
`integerGreedyRemainder`), reproduced exactly on the ranges already known to
the project, the hit density in successive windows is

  `[5,99] 44/95`, `[100,199] 42/100`, `[200,299] 43/100`, `[300,399] 53/100`,
  `[400,499] 48/100`, `[500,999] 257/500`, `[1000,1499] 243/500`,
  `[1500,1999] 247/500`, `[2000,2499] 267/500`, `[2500,2999] 251/500`,
  `[3000,3499] 255/500`, `[3500,3999] 255/500`, `[4000,4499] 260/500`,
  `[4500,4999] 243/500`, `[5000,5499] 219/500`, `[5500,5999] 269/500`.

Cumulatively `2996/5996 = 0.49967`.  This is **MEASURED**, not proved.  The
gaps between consecutive hits are
geometric — `1:1524, 2:706, 3:384, 4:189, 5:94, 6:48, 7:29, 8:10, 9:7, 10:2,
12:1, 13:1` — with maximum gap `13`, first attained at `s = 5372`.  There is
no observed decay on this range.  Later computation recorded in
`ErdosProblems/Hlow/W1.lean` identifies this hit event with the greedy
support bit for `1/2` on `s ∈ [5,900]`; thus the near-`1/2` density is not, by
itself, evidence toward cofinality.

The proposed rank-by-rank explanation for the measured end-row bound was
**FALSE**.  `ErdosProblems/Three/T1.lean` proves
`Three.T1.not_residualInvariant`, with the counterexample `(s,d) = (13,7)`:
the residual is `524419`, exceeding `2 ^ 19 = 524288` by `131`.  This lies
inside the range claimed above.  An independent rescan found exactly this one
failure over `s ∈ [6,3000]`, `d ∈ [2,s-1]`; the maximal ratio among the
non-failures was `0.9999807` at `(606,602)`, not `0.99989`.
`Three.T1.seamResidualUpto_last` identifies the terminal residual with `ρ s`,
and `Three/T1` separately proves `ρ 13 = 15147 < 2 ^ 14`, so the measured
end-row inequality survives at the row where the proposed invariant fails.
The universal residual invariant cannot be used to explain or prove it.

The `SeamSkipsLast` hypothesis of §5 is close to universal: the largest declined
rank `d` of row `s` satisfies `2 * s < 3 * d` at `391` of the `394` rows in
`[6, 399]`, and `d = s - 1` at most of them.  So the theorems of §5 are
statements about almost every row, not about a thin set.

Where the remaining gap sits, stated precisely.  §5 gives `ρ s < 3 * 2 ^ s` at a
late row, i.e. `a s < 2 * 2 ^ s` for `a s := ρ s - 2 ^ s`.  The descent law
`a (s+1) ≤ 4 * a s - 4` has its fixed point at `a = 4/3`, so what has to be
excluded is `a s` hovering in `[2, O(s)]` — and `ρ s < 3 * 2 ^ s` does not
exclude it.  The `4 ^ s` scale is gone; a factor of `3` remains.
-/

end ErdosProblems.RemC6
