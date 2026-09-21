import Mathlib
import Erdos249257.CertificateKernel

/-!
# The square-block binary number: an irrational whose base-two dilations avoid ℤ

This module supplies the one construction shared by two long-#249 environments.

* `catalogue:cert:d2` (*An irrationality criterion from near integers*) states the
  near-integer criterion, records that restricting the multiplier to the powers of a
  fixed base `b₀ ≥ 2` is a sufficient special case **and not a hypothesis satisfied by
  every irrational number**, and then exhibits the witness: concatenate the block `10`
  at square indices `k ≥ 1` and `01` at the other indices.  The paper asserts four
  things about that number — its binary expansion is not eventually periodic, so the
  number is irrational; there are no three consecutive equal digits; every fractional
  part after a binary shift therefore lies in `[1/8, 7/8]`; and the multiples `2ⁿ ξ`
  do not approach the integers.
* `prop:D1D2-inv` (*Two general irrationality criteria*) reuses exactly that witness
  for its clause "requiring `m = b₀ⁿ` for a fixed integer base `b₀ ≥ 2` is a stronger
  sufficient condition, not a reformulation valid for every irrational number".

Everything is proved for a general binary digit sequence first, since the paper's own
argument is general: *no three consecutive equal digits* forces every shifted
fractional part into `[1/8, 7/8]`, and *no eventual period* forces irrationality.
The square-block sequence is then checked against both hypotheses.

The two criteria themselves, and the two rational-error lower bounds behind them, are
already in the tree; their `#print axioms` lines are repeated at the end of this file
so that the two environments have a single home.
-/

noncomputable section

namespace ErdosProblems.Erdos249.PaperCompleteR21

namespace SquareBlockBinary

/-! ## Binary expansions -/

/-- The real number whose binary digits, read from position `n` on, are
`d n, d (n+1), d (n+2), …`.  For `n = 0` this is the number itself; for general `n`
it is the tail left after `n` binary shifts. -/
def tail (d : ℕ → ℕ) (n : ℕ) : ℝ := ∑' k : ℕ, (d (n + k) : ℝ) / 2 ^ (k + 1)

theorem tail_def (d : ℕ → ℕ) (n : ℕ) :
    tail d n = ∑' k : ℕ, (d (n + k) : ℝ) / 2 ^ (k + 1) := rfl

theorem summable_one_div_two_pow_succ :
    Summable (fun k : ℕ => (1 : ℝ) / 2 ^ (k + 1)) := by
  have hgeo : Summable (fun k : ℕ => ((1 : ℝ) / 2) ^ k) :=
    summable_geometric_of_lt_one (by norm_num) (by norm_num)
  have h := (summable_nat_add_iff 1).mpr hgeo
  refine h.congr fun k => ?_
  rw [div_pow, one_pow]

theorem tsum_one_div_two_pow_succ : (∑' k : ℕ, (1 : ℝ) / 2 ^ (k + 1)) = 1 := by
  have hgeo : Summable (fun k : ℕ => ((1 : ℝ) / 2) ^ k) :=
    summable_geometric_of_lt_one (by norm_num) (by norm_num)
  have h := hgeo.sum_add_tsum_nat_add 1
  rw [tsum_geometric_two] at h
  have h1 : (∑ i ∈ Finset.range 1, ((1 : ℝ) / 2) ^ i) = 1 := by simp
  rw [h1] at h
  have h2 : (∑' i : ℕ, ((1 : ℝ) / 2) ^ (i + 1)) = ∑' k : ℕ, (1 : ℝ) / 2 ^ (k + 1) :=
    tsum_congr fun i => by rw [div_pow, one_pow]
  rw [h2] at h
  linarith

theorem tailTerm_le {d : ℕ → ℕ} (hd : ∀ n, d n ≤ 1) (n k : ℕ) :
    (d (n + k) : ℝ) / 2 ^ (k + 1) ≤ (1 : ℝ) / 2 ^ (k + 1) := by
  have hdk : ((d (n + k) : ℕ) : ℝ) ≤ 1 := by exact_mod_cast hd (n + k)
  simp only [div_eq_mul_inv]
  exact mul_le_mul_of_nonneg_right hdk (by positivity)

theorem summable_tailTerm {d : ℕ → ℕ} (hd : ∀ n, d n ≤ 1) (n : ℕ) :
    Summable (fun k : ℕ => (d (n + k) : ℝ) / 2 ^ (k + 1)) :=
  Summable.of_nonneg_of_le (fun k => by positivity) (fun k => tailTerm_le hd n k)
    summable_one_div_two_pow_succ

theorem tail_nonneg (d : ℕ → ℕ) (n : ℕ) : 0 ≤ tail d n := by
  rw [tail_def]
  exact tsum_nonneg fun k => by positivity

theorem tail_le_one {d : ℕ → ℕ} (hd : ∀ n, d n ≤ 1) (n : ℕ) : tail d n ≤ 1 := by
  rw [tail_def, ← tsum_one_div_two_pow_succ]
  exact Summable.tsum_le_tsum (fun k => tailTerm_le hd n k) (summable_tailTerm hd n)
    summable_one_div_two_pow_succ

/-- One binary shift: `tail d n = (d n + tail d (n+1)) / 2`. -/
theorem tail_succ {d : ℕ → ℕ} (hd : ∀ n, d n ≤ 1) (n : ℕ) :
    tail d n = ((d n : ℝ) + tail d (n + 1)) / 2 := by
  have hsum := summable_tailTerm hd n
  have hsplit := hsum.sum_add_tsum_nat_add 1
  have hhead : (∑ j ∈ Finset.range 1, (d (n + j) : ℝ) / 2 ^ (j + 1)) = (d n : ℝ) / 2 := by
    rw [Finset.sum_range_one]
    norm_num
  have htail : (∑' j : ℕ, (d (n + (j + 1)) : ℝ) / 2 ^ (j + 1 + 1))
      = tail d (n + 1) / 2 := by
    rw [tail_def, ← tsum_div_const]
    exact tsum_congr fun j => by
      rw [show n + (j + 1) = n + 1 + j from by omega, div_div, ← pow_succ]
  have hkey : (d n : ℝ) / 2 + tail d (n + 1) / 2 = tail d n := by
    calc (d n : ℝ) / 2 + tail d (n + 1) / 2
        = (∑ j ∈ Finset.range 1, (d (n + j) : ℝ) / 2 ^ (j + 1))
          + ∑' j : ℕ, (d (n + (j + 1)) : ℝ) / 2 ^ (j + 1 + 1) := by rw [hhead, htail]
      _ = tail d n := hsplit
  linarith

/-- Three binary shifts at once. -/
theorem tail_eq_three {d : ℕ → ℕ} (hd : ∀ n, d n ≤ 1) (n : ℕ) :
    tail d n = (d n : ℝ) / 2 + (d (n + 1) : ℝ) / 4 + (d (n + 2) : ℝ) / 8
      + tail d (n + 3) / 8 := by
  have h0 := tail_succ hd n
  have h1 := tail_succ hd (n + 1)
  have h2 := tail_succ hd (n + 2)
  rw [show n + 1 + 1 = n + 2 from by omega] at h1
  rw [show n + 2 + 1 = n + 3 from by omega] at h2
  rw [h0, h1, h2]
  ring

/-- **No three consecutive equal digits pins every shifted tail into `[1/8, 7/8]`.**
This is the paper's implication, stated for an arbitrary binary digit sequence: a
tail below `1/8` would start with three zeros, one above `7/8` with three ones. -/
theorem tail_mem_Icc {d : ℕ → ℕ} (hd : ∀ n, d n ≤ 1)
    (hrun : ∀ n, ¬ (d n = d (n + 1) ∧ d (n + 1) = d (n + 2))) (n : ℕ) :
    1 / 8 ≤ tail d n ∧ tail d n ≤ 7 / 8 := by
  have hexp := tail_eq_three hd n
  have hlo : (0 : ℝ) ≤ tail d (n + 3) := tail_nonneg d (n + 3)
  have hhi : tail d (n + 3) ≤ 1 := tail_le_one hd (n + 3)
  have hn := hrun n
  have hb0 := hd n
  have hb1 := hd (n + 1)
  have hb2 := hd (n + 2)
  have e0 : d n = 0 ∨ d n = 1 := by omega
  have e1 : d (n + 1) = 0 ∨ d (n + 1) = 1 := by omega
  have e2 : d (n + 2) = 0 ∨ d (n + 2) = 1 := by omega
  rcases e0 with h0 | h0 <;> rcases e1 with h1 | h1 <;> rcases e2 with h2 | h2 <;>
    rw [h0, h1, h2] at hexp <;> push_cast at hexp <;>
    first
      | exact absurd ⟨by omega, by omega⟩ hn
      | exact ⟨by linarith, by linarith⟩

theorem tail_lt_half {d : ℕ → ℕ} (hd : ∀ n, d n ≤ 1)
    (hrun : ∀ n, ¬ (d n = d (n + 1) ∧ d (n + 1) = d (n + 2))) {n : ℕ}
    (h : d n = 0) : tail d n < 1 / 2 := by
  have h1 := tail_succ hd n
  have h2 := (tail_mem_Icc hd hrun (n + 1)).2
  rw [h] at h1
  push_cast at h1
  linarith

theorem half_lt_tail {d : ℕ → ℕ} (hd : ∀ n, d n ≤ 1)
    (hrun : ∀ n, ¬ (d n = d (n + 1) ∧ d (n + 1) = d (n + 2))) {n : ℕ}
    (h : d n = 1) : 1 / 2 < tail d n := by
  have h1 := tail_succ hd n
  have h2 := (tail_mem_Icc hd hrun (n + 1)).1
  rw [h] at h1
  push_cast at h1
  linarith

/-- Under the run bound a tail value determines its own leading digit. -/
theorem digit_eq_of_tail_eq {d : ℕ → ℕ} (hd : ∀ n, d n ≤ 1)
    (hrun : ∀ n, ¬ (d n = d (n + 1) ∧ d (n + 1) = d (n + 2))) {n m : ℕ}
    (h : tail d n = tail d m) : d n = d m := by
  have hbn := hd n
  have hbm := hd m
  have en : d n = 0 ∨ d n = 1 := by omega
  have em : d m = 0 ∨ d m = 1 := by omega
  rcases en with hn | hn <;> rcases em with hm | hm
  · rw [hn, hm]
  · exfalso
    have p1 := tail_lt_half hd hrun hn
    have p2 := half_lt_tail hd hrun hm
    rw [h] at p1
    linarith
  · exfalso
    have p1 := half_lt_tail hd hrun hn
    have p2 := tail_lt_half hd hrun hm
    rw [h] at p1
    linarith
  · rw [hn, hm]

theorem tail_add_eq_of_tail_eq {d : ℕ → ℕ} (hd : ∀ n, d n ≤ 1)
    (hrun : ∀ n, ¬ (d n = d (n + 1) ∧ d (n + 1) = d (n + 2))) {n m : ℕ}
    (h : tail d n = tail d m) : ∀ k, tail d (n + k) = tail d (m + k) := by
  intro k
  induction k with
  | zero => simpa using h
  | succ j ih =>
      have h1 := tail_succ hd (n + j)
      have h2 := tail_succ hd (m + j)
      have hdig : d (n + j) = d (m + j) := digit_eq_of_tail_eq hd hrun ih
      rw [hdig, ih] at h1
      have h3 : tail d (n + j + 1) = tail d (m + j + 1) := by linarith
      exact h3

theorem digit_add_eq_of_tail_eq {d : ℕ → ℕ} (hd : ∀ n, d n ≤ 1)
    (hrun : ∀ n, ¬ (d n = d (n + 1) ∧ d (n + 1) = d (n + 2))) {n m : ℕ}
    (h : tail d n = tail d m) (k : ℕ) : d (n + k) = d (m + k) :=
  digit_eq_of_tail_eq hd hrun (tail_add_eq_of_tail_eq hd hrun h k)

/-! ## Binary shifts -/

/-- The integer discarded by `n` binary shifts: the integer with binary digits
`d 0, …, d (n-1)`. -/
def shiftInt (d : ℕ → ℕ) : ℕ → ℤ
  | 0 => 0
  | n + 1 => 2 * shiftInt d n + (d n : ℤ)

theorem shiftInt_zero (d : ℕ → ℕ) : shiftInt d 0 = 0 := rfl

theorem shiftInt_succ (d : ℕ → ℕ) (n : ℕ) :
    shiftInt d (n + 1) = 2 * shiftInt d n + (d n : ℤ) := rfl

theorem two_pow_mul_tail_zero {d : ℕ → ℕ} (hd : ∀ n, d n ≤ 1) (n : ℕ) :
    (2 : ℝ) ^ n * tail d 0 = (shiftInt d n : ℝ) + tail d n := by
  induction n with
  | zero => simp [shiftInt_zero]
  | succ m ih =>
      have hs := tail_succ hd m
      have hpow : (2 : ℝ) ^ (m + 1) * tail d 0 = 2 * ((2 : ℝ) ^ m * tail d 0) := by ring
      rw [hpow, ih, shiftInt_succ, hs]
      push_cast
      ring

theorem fract_two_pow_mul_tail_zero {d : ℕ → ℕ} (hd : ∀ n, d n ≤ 1)
    (hrun : ∀ n, ¬ (d n = d (n + 1) ∧ d (n + 1) = d (n + 2))) (n : ℕ) :
    Int.fract ((2 : ℝ) ^ n * tail d 0) = tail d n := by
  have h := two_pow_mul_tail_zero hd n
  have hb := tail_mem_Icc hd hrun n
  rw [h, Int.fract_intCast_add]
  exact Int.fract_eq_self.mpr ⟨by linarith [hb.1], by linarith [hb.2]⟩

/-- **The paper's implication, in full.**  A binary expansion with no three
consecutive equal digits has every shifted fractional part in `[1/8, 7/8]`. -/
theorem fract_mem_Icc_of_no_three_equal {d : ℕ → ℕ} (hd : ∀ n, d n ≤ 1)
    (hrun : ∀ n, ¬ (d n = d (n + 1) ∧ d (n + 1) = d (n + 2))) (n : ℕ) :
    Int.fract ((2 : ℝ) ^ n * tail d 0) ∈ Set.Icc (1 / 8 : ℝ) (7 / 8) := by
  rw [fract_two_pow_mul_tail_zero hd hrun n]
  exact ⟨(tail_mem_Icc hd hrun n).1, (tail_mem_Icc hd hrun n).2⟩

/-- **Hence the dilations stay away from ℤ.**  Every `2ⁿ x` is at distance at least
`1/8` from every integer. -/
theorem one_div_eight_le_abs_sub_int {d : ℕ → ℕ} (hd : ∀ n, d n ≤ 1)
    (hrun : ∀ n, ¬ (d n = d (n + 1) ∧ d (n + 1) = d (n + 2))) (n : ℕ) (z : ℤ) :
    (1 : ℝ) / 8 ≤ |(2 : ℝ) ^ n * tail d 0 - (z : ℝ)| := by
  have h := two_pow_mul_tail_zero hd n
  have hb := tail_mem_Icc hd hrun n
  have hrw : (2 : ℝ) ^ n * tail d 0 - (z : ℝ)
      = tail d n - ((z - shiftInt d n : ℤ) : ℝ) := by
    rw [h]
    push_cast
    ring
  rw [hrw]
  by_cases hc : z - shiftInt d n ≤ 0
  · have hc' : ((z - shiftInt d n : ℤ) : ℝ) ≤ 0 := by exact_mod_cast hc
    rw [abs_of_nonneg (by linarith [hb.1])]
    linarith [hb.1]
  · have h1 : (1 : ℤ) ≤ z - shiftInt d n := by omega
    have hc' : (1 : ℝ) ≤ ((z - shiftInt d n : ℤ) : ℝ) := by exact_mod_cast h1
    rw [abs_of_nonpos (by linarith [hb.2])]
    linarith [hb.2]

/-! ## No eventual period forces irrationality -/

/-- **A binary expansion that is not eventually periodic defines an irrational
number.**  The proof is the paper's: a rational value makes the shifted tails take
finitely many values, so two of them coincide, and under the run bound a tail value
determines the whole digit sequence from that point on. -/
theorem irrational_tail_zero {d : ℕ → ℕ} (hd : ∀ n, d n ≤ 1)
    (hrun : ∀ n, ¬ (d n = d (n + 1) ∧ d (n + 1) = d (n + 2)))
    (hper : ∀ N P : ℕ, 0 < P → ¬ ∀ k, N ≤ k → d k = d (k + P)) :
    Irrational (tail d 0) := by
  rintro ⟨r, hr⟩
  have key : ∀ n m : ℕ, n < m → tail d n = tail d m → False := by
    intro n m hlt heq
    obtain ⟨P, hP, hmP⟩ : ∃ P, 0 < P ∧ m = n + P := ⟨m - n, by omega, by omega⟩
    subst hmP
    refine hper n P hP ?_
    intro k hk
    have h1 := digit_add_eq_of_tail_eq hd hrun heq (k - n)
    have g1 : n + (k - n) = k := by omega
    have g2 : n + P + (k - n) = k + P := by omega
    rw [g1, g2] at h1
    exact h1
  have hbpos : 0 < r.den := r.den_pos
  have hbR : (0 : ℝ) < (r.den : ℝ) := by exact_mod_cast hbpos
  have hbne : ((r.den : ℕ) : ℝ) ≠ 0 := ne_of_gt hbR
  have hnum : ((r.num : ℤ) : ℝ) = (r : ℝ) * (r.den : ℝ) := by
    rw [Rat.cast_def]
    field_simp
  obtain ⟨A, hA⟩ : ∃ A : ℕ → ℤ, ∀ n, (A n : ℝ) = (r.den : ℝ) * tail d n := by
    refine ⟨fun n => 2 ^ n * r.num - (r.den : ℤ) * shiftInt d n, fun n => ?_⟩
    have h := two_pow_mul_tail_zero hd n
    rw [← hr] at h
    push_cast
    rw [hnum]
    have e : (2 : ℝ) ^ n * ((r : ℝ) * (r.den : ℝ))
        = ((2 : ℝ) ^ n * (r : ℝ)) * (r.den : ℝ) := by ring
    rw [e, h]
    ring
  have hA0 : ∀ n, 0 ≤ A n := by
    intro n
    have h1 := hA n
    have h2 : (0 : ℝ) ≤ tail d n := tail_nonneg d n
    have h3 : (0 : ℝ) ≤ (A n : ℝ) := by rw [h1]; positivity
    exact_mod_cast h3
  have hAb : ∀ n, A n ≤ (r.den : ℤ) := by
    intro n
    have h1 := hA n
    have h2 : tail d n ≤ 1 := tail_le_one hd n
    have h3 : (A n : ℝ) ≤ ((r.den : ℤ) : ℝ) := by
      rw [h1]
      push_cast
      nlinarith
    exact_mod_cast h3
  have hmaps : ∀ n ∈ Finset.range (r.den + 2),
      (A n).toNat ∈ Finset.range (r.den + 1) := by
    intro n _
    simp only [Finset.mem_range]
    have h1 := hA0 n
    have h2 := hAb n
    omega
  have hcard : (Finset.range (r.den + 1)).card < (Finset.range (r.den + 2)).card := by
    rw [Finset.card_range, Finset.card_range]
    omega
  obtain ⟨n, hn, m, hm, hnm, heq⟩ :=
    Finset.exists_ne_map_eq_of_card_lt_of_maps_to hcard hmaps
  have hAeq : A n = A m := by
    have h1 := hA0 n
    have h2 := hA0 m
    omega
  have htail : tail d n = tail d m := by
    have e1 := hA n
    have e2 := hA m
    rw [hAeq] at e1
    have e3 : (r.den : ℝ) * tail d n = (r.den : ℝ) * tail d m := by rw [← e1, e2]
    exact mul_left_cancel₀ hbne e3
  rcases lt_or_gt_of_ne hnm with hlt | hgt
  · exact key n m hlt htail
  · exact key m n hgt htail.symm

/-! ## The square-block sequence -/

open Classical in
/-- **The paper's binary example.**  Reading the expansion two digits at a time, the
block with index `k ≥ 1` is `10` when `k` is a perfect square and `01` otherwise.
Position `n` sits inside the block with index `n / 2 + 1`, and is that block's first
digit exactly when `n` is even. -/
noncomputable def digit (n : ℕ) : ℕ :=
  if IsSquare (n / 2 + 1) ↔ n % 2 = 0 then 1 else 0

theorem digit_le_one (n : ℕ) : digit n ≤ 1 := by
  simp only [digit]
  split <;> omega

theorem digit_even_of_isSquare {j : ℕ} (h : IsSquare (j + 1)) : digit (2 * j) = 1 := by
  have h1 : 2 * j / 2 = j := by omega
  have h2 : 2 * j % 2 = 0 := by omega
  simp only [digit, h1, h2]
  exact if_pos ⟨fun _ => trivial, fun _ => h⟩

theorem digit_even_of_not_isSquare {j : ℕ} (h : ¬ IsSquare (j + 1)) :
    digit (2 * j) = 0 := by
  have h1 : 2 * j / 2 = j := by omega
  have h2 : 2 * j % 2 = 0 := by omega
  simp only [digit, h1, h2]
  exact if_neg fun hiff => h (hiff.mpr trivial)

theorem digit_odd_of_isSquare {j : ℕ} (h : IsSquare (j + 1)) :
    digit (2 * j + 1) = 0 := by
  have h1 : (2 * j + 1) / 2 = j := by omega
  have h2 : (2 * j + 1) % 2 = 1 := by omega
  simp only [digit, h1, h2]
  refine if_neg ?_
  intro hiff
  have hc := hiff.mp h
  omega

theorem digit_odd_of_not_isSquare {j : ℕ} (h : ¬ IsSquare (j + 1)) :
    digit (2 * j + 1) = 1 := by
  have h1 : (2 * j + 1) / 2 = j := by omega
  have h2 : (2 * j + 1) % 2 = 1 := by omega
  simp only [digit, h1, h2]
  refine if_pos ?_
  constructor
  · intro hs
    exact absurd hs h
  · intro h10
    exact absurd h10 (by decide)

/-- **The construction, as the paper describes it.**  The block with index `k = j+1`
occupies positions `2j` and `2j+1`; it is `10` at square indices and `01` elsewhere. -/
theorem digit_block (j : ℕ) :
    (IsSquare (j + 1) → digit (2 * j) = 1 ∧ digit (2 * j + 1) = 0) ∧
      (¬ IsSquare (j + 1) → digit (2 * j) = 0 ∧ digit (2 * j + 1) = 1) :=
  ⟨fun h => ⟨digit_even_of_isSquare h, digit_odd_of_isSquare h⟩,
    fun h => ⟨digit_even_of_not_isSquare h, digit_odd_of_not_isSquare h⟩⟩

theorem digit_even_ne (j : ℕ) : digit (2 * j) ≠ digit (2 * j + 1) := by
  by_cases h : IsSquare (j + 1)
  · rw [digit_even_of_isSquare h, digit_odd_of_isSquare h]
    omega
  · rw [digit_even_of_not_isSquare h, digit_odd_of_not_isSquare h]
    omega

/-- **There are no three consecutive equal digits.**  Any three consecutive positions
contain both digits of some block, and the two digits of a block differ. -/
theorem no_three_consecutive_equal (n : ℕ) :
    ¬ (digit n = digit (n + 1) ∧ digit (n + 1) = digit (n + 2)) := by
  rintro ⟨h1, h2⟩
  obtain ⟨j, hj | hj⟩ := Nat.even_or_odd' n
  · subst hj
    exact digit_even_ne j h1
  · subst hj
    rw [show 2 * j + 1 + 1 = 2 * (j + 1) from by ring,
      show 2 * j + 1 + 2 = 2 * (j + 1) + 1 from by ring] at h2
    exact digit_even_ne (j + 1) h2

/-- **The binary expansion is not eventually periodic.**  A period `P` from position
`N` on would force `k` and `k + P` to be simultaneously square for every large `k`;
but above `s²` the next square is `(s+1)² = s² + 2s + 1`, and `2s + 1` outgrows `P`.
This is the paper's "the block sequence has increasingly long gaps between the square
indices". -/
theorem not_eventually_periodic (N P : ℕ) (hP : 0 < P) :
    ¬ ∀ k, N ≤ k → digit k = digit (k + P) := by
  intro h
  obtain ⟨s, hsN, hsP⟩ : ∃ s : ℕ, N + 1 ≤ s ∧ P + 1 ≤ s :=
    ⟨max (N + 1) (P + 1), le_max_left _ _, le_max_right _ _⟩
  have hs1 : 1 ≤ s := by omega
  have hss : s ≤ s * s := by
    calc s = 1 * s := (one_mul s).symm
      _ ≤ s * s := Nat.mul_le_mul_right s hs1
  have hpos : 1 ≤ s * s := le_trans hs1 hss
  obtain ⟨j, hj⟩ : ∃ j : ℕ, j + 1 = s * s := ⟨s * s - 1, Nat.sub_add_cancel hpos⟩
  have hsle : s ≤ j + 1 := by rw [hj]; exact hss
  have hNj : N ≤ 2 * j := by omega
  have e1 : digit (2 * j) = digit (2 * j + P) := h (2 * j) hNj
  have e2 : digit (2 * j + P) = digit (2 * j + P + P) := h (2 * j + P) (by omega)
  have e3 : digit (2 * j) = digit (2 * (j + P)) := by
    rw [e1, e2]
    congr 1
    ring
  have hsq : IsSquare (j + 1) := by rw [hj]; exact ⟨s, rfl⟩
  have hd1 : digit (2 * j) = 1 := digit_even_of_isSquare hsq
  have hd2 : digit (2 * (j + P)) = 1 := by rw [← e3]; exact hd1
  have hsq2 : IsSquare (j + P + 1) := by
    by_contra hc
    rw [digit_even_of_not_isSquare hc] at hd2
    omega
  obtain ⟨t, ht⟩ := hsq2
  have hts : s * s + P = t * t := by
    rw [← ht, ← hj]
    ring
  have hst : s < t := by
    rcases Nat.lt_or_ge s t with hlt | hge
    · exact hlt
    · exfalso
      have h5 : t * t ≤ s * s := Nat.mul_le_mul hge hge
      have h6 : s * s + P ≤ s * s := le_trans (le_of_eq hts) h5
      linarith
  have h7 : s + 1 ≤ t := hst
  have h8 : (s + 1) * (s + 1) ≤ t * t := Nat.mul_le_mul h7 h7
  have h9 : (s + 1) * (s + 1) = s * s + (2 * s + 1) := by ring
  have h10 : s * s + (2 * s + 1) ≤ s * s + P := by
    rw [← h9, hts]
    exact h8
  have h11 : 2 * s + 1 ≤ P := Nat.le_of_add_le_add_left h10
  omega

/-! ## The witness -/

/-- **ξ**, the number of the paper's binary example. -/
noncomputable def xi : ℝ := tail digit 0

/-- **ξ is irrational**, because its binary expansion is not eventually periodic. -/
theorem irrational_xi : Irrational xi :=
  irrational_tail_zero digit_le_one no_three_consecutive_equal not_eventually_periodic

/-- **Every fractional part after a binary shift lies in `[1/8, 7/8]`.** -/
theorem fract_two_pow_mul_xi_mem_Icc (n : ℕ) :
    Int.fract ((2 : ℝ) ^ n * xi) ∈ Set.Icc (1 / 8 : ℝ) (7 / 8) :=
  fract_mem_Icc_of_no_three_equal digit_le_one no_three_consecutive_equal n

/-- **The multiples `2ⁿ ξ` do not approach the integers**: each of them is at distance
at least `1/8` from every integer. -/
theorem one_div_eight_le_dist_xi (n : ℕ) (z : ℤ) :
    (1 : ℝ) / 8 ≤ |(2 : ℝ) ^ n * xi - (z : ℝ)| :=
  one_div_eight_le_abs_sub_int digit_le_one no_three_consecutive_equal n z

/-- The same statement in approach form: no dilation `2ⁿ ξ` ever comes within `1/8`
of an integer, so `2ⁿ ξ` does not approach `ℤ` even along a subsequence. -/
theorem not_approaches_int {ε : ℝ} (hε : ε ≤ 1 / 8) :
    ¬ ∃ (n : ℕ) (z : ℤ), |(2 : ℝ) ^ n * xi - (z : ℝ)| < ε := by
  rintro ⟨n, z, hlt⟩
  have h := one_div_eight_le_dist_xi n z
  linarith

/-- **ξ fails the base-power hypothesis at `b₀ = 2`.**  This is the sentence
"restricting the multiplier to powers `m = b₀ⁿ` of a fixed integer base `b₀ ≥ 2`
gives a sufficient special case, not a hypothesis satisfied by every irrational
number" (`catalogue:cert:d2`). -/
theorem not_near_integer_along_powers_of_two :
    ¬ ∀ q : ℕ, 0 < q → ∃ (n : ℕ) (z : ℤ),
        0 < |(2 : ℝ) ^ n * xi - (z : ℝ)| ∧
          |(2 : ℝ) ^ n * xi - (z : ℝ)| < 1 / (q : ℝ) := by
  intro h
  obtain ⟨n, z, -, hlt⟩ := h 8 (by norm_num)
  have hc8 : ((8 : ℕ) : ℝ) = 8 := by norm_num
  rw [hc8] at hlt
  have hb := one_div_eight_le_dist_xi n z
  linarith

/-- **The witness, packaged.**  There is an irrational number and a base `b₀ ≥ 2`
whose dilations `b₀ⁿ x` all stay at distance at least `1/8` from `ℤ`. -/
theorem exists_irrational_basePower_bounded_away :
    ∃ x : ℝ, Irrational x ∧ ∃ b₀ : ℕ, 2 ≤ b₀ ∧
      ∀ (n : ℕ) (z : ℤ), (1 : ℝ) / 8 ≤ |((b₀ ^ n : ℕ) : ℝ) * x - (z : ℝ)| := by
  refine ⟨xi, irrational_xi, 2, le_refl 2, fun n z => ?_⟩
  have hcast : (((2 : ℕ) ^ n : ℕ) : ℝ) = (2 : ℝ) ^ n := by
    push_cast
    try ring
  rw [hcast]
  exact one_div_eight_le_dist_xi n z

/-- **The base-power dilation condition is not a reformulation valid for every
irrational number** (`prop:D1D2-inv`, fourth sentence).  `ξ` is irrational, yet no
power `2ⁿ ξ` is within `1/8` of an integer, so the condition already fails at
`Q = 8`. -/
theorem basePower_dilation_not_universal :
    ∃ x : ℝ, Irrational x ∧ ∃ b₀ : ℕ, 2 ≤ b₀ ∧
      ¬ ∀ Q : ℤ, 1 ≤ Q → ∃ (n : ℕ) (z : ℤ),
          0 < |((b₀ ^ n : ℕ) : ℝ) * x - (z : ℝ)| ∧
            |((b₀ ^ n : ℕ) : ℝ) * x - (z : ℝ)| < 1 / (Q : ℝ) := by
  refine ⟨xi, irrational_xi, 2, le_refl 2, ?_⟩
  intro h
  obtain ⟨n, z, -, hlt⟩ := h 8 (by norm_num)
  have hcast : (((2 : ℕ) ^ n : ℕ) : ℝ) = (2 : ℝ) ^ n := by
    push_cast
    try ring
  have hc8 : (((8 : ℤ)) : ℝ) = 8 := by norm_num
  rw [hcast, hc8] at hlt
  have hb := one_div_eight_le_dist_xi n z
  linarith

/-! ## The two hypothesis glosses of `catalogue:cert:d2` -/

/-- **"The strict lower bound excludes exact integer hits."**  Drop `0 < |mξ - z|`
and the criterion becomes false: `ξ = 0` satisfies the remaining bound for every `q`
with `m = z = 0`. -/
theorem strict_lower_bound_needed :
    ¬ ∀ ξ : ℝ, (∀ q : ℕ, 0 < q → ∃ m z : ℤ,
        |(m : ℝ) * ξ - (z : ℝ)| < 1 / (q : ℝ)) → Irrational ξ := by
  intro h
  have hzero : Irrational (0 : ℝ) := by
    refine h 0 fun q hq => ⟨0, 0, ?_⟩
    have hq' : (0 : ℝ) < (q : ℝ) := by exact_mod_cast hq
    have he : |((0 : ℤ) : ℝ) * (0 : ℝ) - ((0 : ℤ) : ℝ)| = 0 := by norm_num
    rw [he]
    positivity
  exact hzero ⟨0, by norm_num⟩

/-- **"The upper bound must be available for arbitrarily large `q`."**  At any single
`q` the two-sided bound is met by a *rational* number, namely `1 / (2q)` with
`m = 1`, `z = 0`; so no fixed `q`, and no finite range of `q`, can carry the
criterion. -/
theorem upper_bound_needed_for_every_q (q : ℕ) (hq : 0 < q) :
    ∃ ξ : ℝ, ¬ Irrational ξ ∧ ∃ m z : ℤ,
      0 < |(m : ℝ) * ξ - (z : ℝ)| ∧ |(m : ℝ) * ξ - (z : ℝ)| < 1 / (q : ℝ) := by
  have hqR : (0 : ℝ) < (q : ℝ) := by exact_mod_cast hq
  have hval : ((1 : ℤ) : ℝ) * (1 / (2 * (q : ℝ))) - ((0 : ℤ) : ℝ)
      = 1 / (2 * (q : ℝ)) := by
    push_cast
    ring
  have hpos : (0 : ℝ) < 1 / (2 * (q : ℝ)) := by positivity
  refine ⟨1 / (2 * (q : ℝ)), ?_, 1, 0, ?_, ?_⟩
  · intro hirr
    refine hirr ⟨1 / (2 * (q : ℚ)), ?_⟩
    push_cast
    try ring
  · rw [hval, abs_of_pos hpos]
    exact hpos
  · rw [hval, abs_of_pos hpos]
    have e1 : 1 / (2 * (q : ℝ)) = (1 / (q : ℝ)) / 2 := by
      rw [div_div, mul_comm (q : ℝ) 2]
    have e2 : (0 : ℝ) < 1 / (q : ℝ) := by positivity
    rw [e1]
    linarith

end SquareBlockBinary

end ErdosProblems.Erdos249.PaperCompleteR21

#print axioms ErdosProblems.Erdos249.PaperCompleteR21.SquareBlockBinary.tail_mem_Icc
#print axioms ErdosProblems.Erdos249.PaperCompleteR21.SquareBlockBinary.fract_mem_Icc_of_no_three_equal
#print axioms ErdosProblems.Erdos249.PaperCompleteR21.SquareBlockBinary.one_div_eight_le_abs_sub_int
#print axioms ErdosProblems.Erdos249.PaperCompleteR21.SquareBlockBinary.irrational_tail_zero
#print axioms ErdosProblems.Erdos249.PaperCompleteR21.SquareBlockBinary.digit_block
#print axioms ErdosProblems.Erdos249.PaperCompleteR21.SquareBlockBinary.no_three_consecutive_equal
#print axioms ErdosProblems.Erdos249.PaperCompleteR21.SquareBlockBinary.not_eventually_periodic
#print axioms ErdosProblems.Erdos249.PaperCompleteR21.SquareBlockBinary.irrational_xi
#print axioms ErdosProblems.Erdos249.PaperCompleteR21.SquareBlockBinary.fract_two_pow_mul_xi_mem_Icc
#print axioms ErdosProblems.Erdos249.PaperCompleteR21.SquareBlockBinary.one_div_eight_le_dist_xi
#print axioms ErdosProblems.Erdos249.PaperCompleteR21.SquareBlockBinary.not_approaches_int
#print axioms ErdosProblems.Erdos249.PaperCompleteR21.SquareBlockBinary.not_near_integer_along_powers_of_two
#print axioms ErdosProblems.Erdos249.PaperCompleteR21.SquareBlockBinary.exists_irrational_basePower_bounded_away
#print axioms ErdosProblems.Erdos249.PaperCompleteR21.SquareBlockBinary.basePower_dilation_not_universal
#print axioms ErdosProblems.Erdos249.PaperCompleteR21.SquareBlockBinary.strict_lower_bound_needed
#print axioms ErdosProblems.Erdos249.PaperCompleteR21.SquareBlockBinary.upper_bound_needed_for_every_q
#print axioms Erdos249257.irrational_of_int_mul_near_int
#print axioms Erdos249257.irrational_of_pow_mul_near_int
#print axioms Erdos249257.irrational_of_den_mul_abs_sub_tendsto_zero
#print axioms Erdos249257.one_div_den_mul_den_le_abs_sub
