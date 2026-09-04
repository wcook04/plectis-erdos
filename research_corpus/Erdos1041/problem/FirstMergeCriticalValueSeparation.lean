import Mathlib

/-!
# Erdős #1041: exact threshold kernel for first-merge critical-value separation

The companion paper proves an ordinary analytic theorem: if the square-resolved
inverse branch at a simple saddle has every other critical value at normalized
distance at least `S > 1`, then its canonical connector has length at most

`2 * (1 + S)^(1/n) * sqrt (log (S / (S - 1)))`.

This file kernel-checks the complete numerical conclusion of that argument.
It proves:

* the squared coefficient is antitone in the degree;
* a squared connector bound below four forces length below two;
* the exact convenient regimes `S = 4, n >= 3`, `S = 3, n >= 4`, and
  `S = 2, n >= 6` all lie strictly below the threshold.

Each degree cutoff is the first degree at which its inequality holds: the
squared coefficient at `(2, 4)`, `(3, 3)` and `(5, 2)` exceeds one.

The analytic continuation, univalence, area formula, and Pólya area-capacity
inequality which produce the squared connector bound remain ordinary
mathematics.  Consequently nothing here asserts the unrestricted Erdős #1041
conjecture or the complementary near-tie/multiple-saddle regime.
-/

namespace ErdosProblems.Erdos1041

/-- The square of the nonconstant factor in the first-merge connector bound. -/
noncomputable def firstMergeSquaredCoefficient (n : ℕ) (S : ℝ) : ℝ :=
  (1 + S) ^ ((2 : ℝ) / (n : ℝ)) * Real.log (S / (S - 1))

private theorem two_div_natCast_antitone {m n : ℕ}
    (hm : 0 < m) (hmn : m ≤ n) :
    (2 : ℝ) / (n : ℝ) ≤ (2 : ℝ) / (m : ℝ) := by
  have hmR : (0 : ℝ) < (m : ℝ) := by exact_mod_cast hm
  have hnR : (0 : ℝ) < (n : ℝ) := by
    exact_mod_cast lt_of_lt_of_le hm hmn
  have hmnR : (m : ℝ) ≤ (n : ℝ) := by exact_mod_cast hmn
  rw [div_le_div_iff₀ hnR hmR]
  nlinarith

/-- For fixed separation `S > 1`, increasing the degree only improves the
first-merge squared coefficient. -/
theorem firstMergeSquaredCoefficient_antitone_degree {m n : ℕ} {S : ℝ}
    (hm : 0 < m) (hmn : m ≤ n) (hS : 1 < S) :
    firstMergeSquaredCoefficient n S ≤ firstMergeSquaredCoefficient m S := by
  have hbase : (1 : ℝ) ≤ 1 + S := by linarith
  have hexp := two_div_natCast_antitone hm hmn
  have hrpow :
      (1 + S) ^ ((2 : ℝ) / (n : ℝ)) ≤
        (1 + S) ^ ((2 : ℝ) / (m : ℝ)) :=
    Real.rpow_le_rpow_of_exponent_le hbase hexp
  have hratio : (1 : ℝ) < S / (S - 1) := by
    have hden : 0 < S - 1 := by linarith
    rw [lt_div_iff₀ hden]
    linarith
  have hlog : 0 ≤ Real.log (S / (S - 1)) :=
    (Real.log_pos hratio).le
  exact mul_le_mul_of_nonneg_right hrpow hlog

/-- Abstract numerical consumer for the ordinary analytic estimate.  Once the
square of a connector length is bounded by four times a coefficient strictly
below one, the connector is strictly shorter than two.  No sign hypothesis on
the connector is needed. -/
theorem firstMerge_length_lt_two_of_squared_bound
    {n : ℕ} {S length : ℝ}
    (hbound : length ^ 2 ≤ 4 * firstMergeSquaredCoefficient n S)
    (hthreshold : firstMergeSquaredCoefficient n S < 1) :
    length < 2 := by
  have hsq : length ^ 2 < 4 := lt_of_le_of_lt hbound (by nlinarith)
  nlinarith [sq_nonneg (length - 2)]

private theorem five_rpow_two_thirds_lt_three :
    (5 : ℝ) ^ ((2 : ℝ) / 3) < 3 := by
  let y : ℝ := (5 : ℝ) ^ ((2 : ℝ) / 3)
  have hy3 : y ^ 3 = 25 := by
    dsimp [y]
    rw [← Real.rpow_mul_natCast (by norm_num : (0 : ℝ) ≤ 5)]
    norm_num [Real.rpow_natCast]
  apply lt_of_pow_lt_pow_left₀ 3 (by norm_num : (0 : ℝ) ≤ 3)
  rw [hy3]
  norm_num

/-- The radius-two base case is a cube, not a seventh power: `(3 ^ (2 / 6)) ^ 3`
collapses to `3` exactly, so the nine-digit rational upper bound on `log 2`
closes the degree-six threshold with `3 * 0.6931471808 ^ 3 < 1`. -/
private theorem three_rpow_two_sixths_mul_log_two_bound_lt_one :
    (3 : ℝ) ^ ((2 : ℝ) / 6) * (0.6931471808 : ℝ) < 1 := by
  let y : ℝ := (3 : ℝ) ^ ((2 : ℝ) / 6)
  let z : ℝ := y * (0.6931471808 : ℝ)
  have hy3 : y ^ 3 = 3 := by
    dsimp [y]
    rw [← Real.rpow_mul_natCast (by norm_num : (0 : ℝ) ≤ 3)]
    norm_num [Real.rpow_natCast]
  have hz3 : z ^ 3 = (3 : ℝ) * (0.6931471808 : ℝ) ^ 3 := by
    dsimp [z]
    rw [mul_pow, hy3]
  have hzpow : z ^ 3 < (1 : ℝ) ^ 3 := by
    rw [hz3]
    norm_num
  have hz : z < 1 :=
    lt_of_pow_lt_pow_left₀ 3 (by norm_num : (0 : ℝ) ≤ 1) hzpow
  simpa [z, y] using hz

/-- Exact radius-four threshold: every degree `n >= 3` satisfies
`5^(2/n) log(4/3) < 1`. -/
theorem firstMergeSquaredCoefficient_lt_one_of_three_le_degree
    {n : ℕ} (hn : 3 ≤ n) :
    firstMergeSquaredCoefficient n 4 < 1 := by
  have hmono :
      firstMergeSquaredCoefficient n 4 ≤
        firstMergeSquaredCoefficient 3 4 :=
    firstMergeSquaredCoefficient_antitone_degree (by norm_num) hn (by norm_num)
  have hlog : Real.log (4 / 3 : ℝ) < 1 / 3 := by
    have := Real.log_lt_sub_one_of_pos
      (by norm_num : (0 : ℝ) < 4 / 3)
      (by norm_num : (4 / 3 : ℝ) ≠ 1)
    norm_num at this ⊢
    exact this
  have hpos : 0 < (5 : ℝ) ^ ((2 : ℝ) / 3) :=
    Real.rpow_pos_of_pos (by norm_num) _
  have hbase :
      firstMergeSquaredCoefficient 3 4 < 1 := by
    rw [firstMergeSquaredCoefficient]
    norm_num only [Nat.cast_ofNat]
    calc
      (5 : ℝ) ^ ((2 : ℝ) / 3) * Real.log (4 / 3 : ℝ)
          < (5 : ℝ) ^ ((2 : ℝ) / 3) * (1 / 3 : ℝ) :=
        mul_lt_mul_of_pos_left hlog hpos
      _ < 3 * (1 / 3 : ℝ) :=
        mul_lt_mul_of_pos_right five_rpow_two_thirds_lt_three (by norm_num)
      _ = 1 := by norm_num
  exact lt_of_le_of_lt hmono hbase

/-- Exact radius-three threshold: every degree `n >= 4` satisfies
`4^(2/n) log(3/2) < 1`. -/
theorem firstMergeSquaredCoefficient_lt_one_of_four_le_degree
    {n : ℕ} (hn : 4 ≤ n) :
    firstMergeSquaredCoefficient n 3 < 1 := by
  have hmono :
      firstMergeSquaredCoefficient n 3 ≤
        firstMergeSquaredCoefficient 4 3 :=
    firstMergeSquaredCoefficient_antitone_degree (by norm_num) hn (by norm_num)
  have hlog : Real.log (3 / 2 : ℝ) < 1 / 2 := by
    have := Real.log_lt_sub_one_of_pos
      (by norm_num : (0 : ℝ) < 3 / 2)
      (by norm_num : (3 / 2 : ℝ) ≠ 1)
    norm_num at this ⊢
    exact this
  have hhalf : (4 : ℝ) ^ ((2 : ℝ) / 4) = 2 := by
    calc
      (4 : ℝ) ^ ((2 : ℝ) / 4) = (4 : ℝ) ^ ((1 : ℝ) / 2) := by norm_num
      _ = Real.sqrt 4 := (Real.sqrt_eq_rpow 4).symm
      _ = 2 := by norm_num
  have hbase :
      firstMergeSquaredCoefficient 4 3 < 1 := by
    rw [firstMergeSquaredCoefficient]
    norm_num only [Nat.cast_ofNat]
    nlinarith
  exact lt_of_le_of_lt hmono hbase

/-- Exact radius-two threshold: every degree `n >= 6` satisfies
`3^(2/n) log 2 < 1`.  Six is sharp, since `3^(2/5) log 2` exceeds one. -/
theorem firstMergeSquaredCoefficient_lt_one_of_six_le_degree
    {n : ℕ} (hn : 6 ≤ n) :
    firstMergeSquaredCoefficient n 2 < 1 := by
  have hmono :
      firstMergeSquaredCoefficient n 2 ≤
        firstMergeSquaredCoefficient 6 2 :=
    firstMergeSquaredCoefficient_antitone_degree (by norm_num) hn (by norm_num)
  have hlog : Real.log 2 < (0.6931471808 : ℝ) := Real.log_two_lt_d9
  have hpos : 0 < (3 : ℝ) ^ ((2 : ℝ) / 6) :=
    Real.rpow_pos_of_pos (by norm_num) _
  have hbase :
      firstMergeSquaredCoefficient 6 2 < 1 := by
    have hval :
        firstMergeSquaredCoefficient 6 2
          = (3 : ℝ) ^ ((2 : ℝ) / 6) * Real.log 2 := by
      rw [firstMergeSquaredCoefficient]
      norm_num
    rw [hval]
    exact lt_trans (mul_lt_mul_of_pos_left hlog hpos)
      three_rpow_two_sixths_mul_log_two_bound_lt_one
  exact lt_of_le_of_lt hmono hbase

/-- The three exact convenient separation regimes, exposed as one coherent
endpoint rather than three disconnected numerical lemmas. -/
theorem firstMerge_exact_convenient_thresholds :
    (∀ n : ℕ, 3 ≤ n → firstMergeSquaredCoefficient n 4 < 1) ∧
    (∀ n : ℕ, 4 ≤ n → firstMergeSquaredCoefficient n 3 < 1) ∧
    (∀ n : ℕ, 6 ≤ n → firstMergeSquaredCoefficient n 2 < 1) := by
  exact ⟨fun _ hn => firstMergeSquaredCoefficient_lt_one_of_three_le_degree hn,
    fun _ hn => firstMergeSquaredCoefficient_lt_one_of_four_le_degree hn,
    fun _ hn => firstMergeSquaredCoefficient_lt_one_of_six_le_degree hn⟩

end ErdosProblems.Erdos1041
