import Mathlib

/-!
# Erdős #1041: exact threshold kernel for the disk-family critical-value separation

The companion note `DiskFamilyCriticalValueSeparation.md` proves an ordinary
analytic theorem.  Normalise a monic `f` at a simple critical point `c` by
`P(w) = f(c + |f(c)|^(1/n) w)/f(c)`, so that `P(0) = 1`, `P'(0) = 0`, and the
other critical values are `v_j = f(d_j)/f(c)`.  Fix a real centre `w0 ∈ [0,1]`
and a radius `S > max(w0, 1 - w0)` with `|v_j - w0| ≥ S` for every `j`.  Put
`p = w0 (1 - w0)`.  Then the canonical connector `Z([-1,1])`,
`P(Z(ξ)) = 1 - ξ^2`, satisfies

`length^2 ≤ 2 * (S/(n-1))^(2/n) * log((S^2 + S + p)/(S^2 - S + p))`.

This file kernel-checks the numerical conclusion of that argument:

* the coefficient is strictly below `2` for every degree `n ≥ 3`, every
  radius `4/3 ≤ S ≤ 2`, and every centre parameter `0 ≤ p ≤ 1/4`;
* a squared connector bound `length^2 ≤ 2 C` with `C < 2` forces
  `length < 2`, with no sign hypothesis on `length`;
* the branch-centred radius-two regime `(2/(n-1))^(2/n) log 3 < 2` for every
  `n ≥ 3`, and the degree-three radius `6/5` regime.

The analytic continuation, univalence, the Bergman segment inequality, Pólya's
area–capacity inequality, and the exterior-fibre capacity gap which produce the
squared connector bound remain ordinary mathematics in the note.  Nothing here
asserts the unrestricted Erdős #1041 conjecture.
-/

namespace ErdosProblems.Erdos1041

/-- The squared-length coefficient of the disk-family separation bound:
`(S/(n-1))^(2/n) * log((S^2 + S + p)/(S^2 - S + p))`. -/
noncomputable def diskFamilyCoefficient (n : ℕ) (S p : ℝ) : ℝ :=
  (S / ((n : ℝ) - 1)) ^ ((2 : ℝ) / (n : ℝ)) *
    Real.log ((S ^ 2 + S + p) / (S ^ 2 - S + p))

/-- `exp 2 > 7`, from the nine-digit lower bound on `e`. -/
private theorem seven_lt_exp_two : (7 : ℝ) < Real.exp 2 := by
  have h := Real.exp_one_gt_d9
  have h2 : Real.exp 2 = Real.exp 1 * Real.exp 1 := by
    rw [← Real.exp_add]; norm_num
  rw [h2]
  nlinarith [h, Real.exp_pos 1]

/-- `log 7 < 2`. -/
private theorem log_seven_lt_two : Real.log 7 < 2 := by
  rw [Real.log_lt_iff_lt_exp (by norm_num)]
  exact seven_lt_exp_two

/-- For `S > 1` and `p ≥ 0` the centre parameter only lowers the logarithmic
ratio: `(S^2+S+p)/(S^2-S+p) ≤ (S+1)/(S-1)`. -/
theorem diskFamily_ratio_le_branch_ratio {S p : ℝ} (hS : 1 < S) (hp : 0 ≤ p) :
    (S ^ 2 + S + p) / (S ^ 2 - S + p) ≤ (S + 1) / (S - 1) := by
  have hden1 : 0 < S ^ 2 - S + p := by nlinarith
  have hden2 : 0 < S - 1 := by linarith
  rw [div_le_div_iff₀ hden1 hden2]
  nlinarith

/-- The branch-centred ratio is at most `7` once `S ≥ 4/3`. -/
theorem branch_ratio_le_seven {S : ℝ} (hS : 4 / 3 ≤ S) :
    (S + 1) / (S - 1) ≤ 7 := by
  have hden : 0 < S - 1 := by linarith
  rw [div_le_iff₀ hden]
  linarith

/-- The logarithmic factor is nonnegative in the admissible range. -/
theorem diskFamily_log_nonneg {S p : ℝ} (hS : 1 < S) (hp : 0 ≤ p) :
    0 ≤ Real.log ((S ^ 2 + S + p) / (S ^ 2 - S + p)) := by
  apply Real.log_nonneg
  have hden : 0 < S ^ 2 - S + p := by nlinarith
  rw [le_div_iff₀ hden]
  linarith

/-- The radial factor `(S/(n-1))^(2/n)` lies in `(0, 1]` whenever
`0 < S ≤ n - 1`. -/
theorem diskFamily_rpow_mem {n : ℕ} {S : ℝ} (hS0 : 0 < S)
    (hSn : S ≤ (n : ℝ) - 1) :
    0 < (S / ((n : ℝ) - 1)) ^ ((2 : ℝ) / (n : ℝ)) ∧
      (S / ((n : ℝ) - 1)) ^ ((2 : ℝ) / (n : ℝ)) ≤ 1 := by
  have hn1 : 0 < (n : ℝ) - 1 := lt_of_lt_of_le hS0 hSn
  have hbase0 : 0 < S / ((n : ℝ) - 1) := div_pos hS0 hn1
  have hbase1 : S / ((n : ℝ) - 1) ≤ 1 := by
    rw [div_le_one hn1]; exact hSn
  have hexp : (0 : ℝ) ≤ (2 : ℝ) / (n : ℝ) := by positivity
  exact ⟨Real.rpow_pos_of_pos hbase0 _, Real.rpow_le_one hbase0.le hbase1 hexp⟩

/-- **Uniform threshold.**  For every degree `n ≥ 3`, every radius
`4/3 ≤ S ≤ 2`, and every centre parameter `0 ≤ p ≤ 1/4`, the disk-family
coefficient is strictly below `2`.  In particular separation `S = 4/3` from
any real centre of the unit value segment closes the connector in every
degree at once. -/
theorem diskFamilyCoefficient_lt_two_of_uniform_separation {n : ℕ}
    (hn : 3 ≤ n) {S p : ℝ} (hS : 4 / 3 ≤ S) (hS2 : S ≤ 2)
    (hp0 : 0 ≤ p) :
    diskFamilyCoefficient n S p < 2 := by
  have hS1 : 1 < S := by linarith
  have hnR : (3 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  have hSn : S ≤ (n : ℝ) - 1 := by linarith
  obtain ⟨hr0, hr1⟩ := diskFamily_rpow_mem (by linarith) hSn
  have hlog0 := diskFamily_log_nonneg hS1 hp0
  have hratio_pos : 0 < (S ^ 2 + S + p) / (S ^ 2 - S + p) := by
    have hden : 0 < S ^ 2 - S + p := by nlinarith
    exact div_pos (by nlinarith) hden
  have hlog7 : Real.log ((S ^ 2 + S + p) / (S ^ 2 - S + p)) ≤ Real.log 7 :=
    Real.log_le_log hratio_pos
      (le_trans (diskFamily_ratio_le_branch_ratio hS1 hp0) (branch_ratio_le_seven hS))
  unfold diskFamilyCoefficient
  calc
    (S / ((n : ℝ) - 1)) ^ ((2 : ℝ) / (n : ℝ)) *
        Real.log ((S ^ 2 + S + p) / (S ^ 2 - S + p))
        ≤ 1 * Real.log ((S ^ 2 + S + p) / (S ^ 2 - S + p)) :=
      mul_le_mul_of_nonneg_right hr1 hlog0
    _ = Real.log ((S ^ 2 + S + p) / (S ^ 2 - S + p)) := one_mul _
    _ ≤ Real.log 7 := hlog7
    _ < 2 := log_seven_lt_two

/-- The branch-centred radius-two regime holds in every degree `n ≥ 3`:
`(2/(n-1))^(2/n) log 3 < 2`.  The former coefficient-series argument needed
`n ≥ 6` at this radius. -/
theorem diskFamilyCoefficient_radius_two_lt_two {n : ℕ} (hn : 3 ≤ n) :
    diskFamilyCoefficient n 2 0 < 2 := by
  have h := diskFamilyCoefficient_lt_two_of_uniform_separation hn
    (S := 2) (p := 0) (by norm_num) (by norm_num) (by norm_num)
  exact h

/-- `exp 5 > 121`, hence `log 11 < 5/2`. -/
private theorem log_eleven_lt_five_halves : Real.log 11 < 5 / 2 := by
  rw [Real.log_lt_iff_lt_exp (by norm_num)]
  have h := Real.exp_one_gt_d9
  have h5 : Real.exp 5 = Real.exp 1 ^ 5 := by
    rw [← Real.exp_nat_mul]; norm_num
  have hsq : Real.exp (5 / 2) ^ 2 = Real.exp 5 := by
    rw [← Real.exp_nat_mul]; norm_num
  have hpos : 0 < Real.exp (5 / 2) := Real.exp_pos _
  have h121 : (121 : ℝ) < Real.exp 5 := by
    rw [h5]
    have : (2.7182818283 : ℝ) ^ 5 < Real.exp 1 ^ 5 :=
      pow_lt_pow_left₀ h (by norm_num) (by norm_num)
    nlinarith [this]
  nlinarith [hsq, hpos, h121]

/-- `(3/5)^(2/3) ≤ 18/25`, by cubing: `(3/5)^2 = 9/25 ≤ (18/25)^3`. -/
private theorem three_fifths_rpow_two_thirds_le :
    (3 / 5 : ℝ) ^ ((2 : ℝ) / 3) ≤ 18 / 25 := by
  let y : ℝ := (3 / 5 : ℝ) ^ ((2 : ℝ) / 3)
  have hy3 : y ^ 3 = 9 / 25 := by
    dsimp [y]
    rw [← Real.rpow_mul_natCast (by norm_num : (0 : ℝ) ≤ 3 / 5)]
    norm_num [Real.rpow_natCast]
  have hy0 : 0 ≤ y := Real.rpow_nonneg (by norm_num) _
  apply le_of_pow_le_pow_left₀ (by norm_num : (3 : ℕ) ≠ 0) (by norm_num : (0 : ℝ) ≤ 18 / 25)
  rw [hy3]; norm_num

/-- **Degree three, radius `6/5`.**  At the branch centre `w0 = 1`, separation
`|1 - v_j| ≥ 6/5` from every other critical value already closes the cubic
connector: `(3/5)^(2/3) log 11 < 2`. -/
theorem diskFamilyCoefficient_three_six_fifths_lt_two :
    diskFamilyCoefficient 3 (6 / 5) 0 < 2 := by
  unfold diskFamilyCoefficient
  have hval : ((6 / 5 : ℝ) ^ 2 + 6 / 5 + 0) / ((6 / 5 : ℝ) ^ 2 - 6 / 5 + 0) = 11 := by
    norm_num
  have hbase : (6 / 5 : ℝ) / ((3 : ℕ) - 1 : ℝ) = 3 / 5 := by norm_num
  have hexp : ((2 : ℝ) / ((3 : ℕ) : ℝ)) = (2 : ℝ) / 3 := by norm_num
  rw [hval, hbase, hexp]
  have hlogpos : 0 ≤ Real.log (11 : ℝ) := Real.log_nonneg (by norm_num)
  have hr0 : 0 ≤ (3 / 5 : ℝ) ^ ((2 : ℝ) / 3) := Real.rpow_nonneg (by norm_num) _
  calc
    (3 / 5 : ℝ) ^ ((2 : ℝ) / 3) * Real.log 11
        ≤ (18 / 25 : ℝ) * Real.log 11 :=
      mul_le_mul_of_nonneg_right three_fifths_rpow_two_thirds_le hlogpos
    _ < (18 / 25 : ℝ) * (5 / 2) :=
      mul_lt_mul_of_pos_left log_eleven_lt_five_halves (by norm_num)
    _ < 2 := by norm_num

/-- Abstract numerical consumer for the ordinary analytic estimate.  Once the
square of a connector length is bounded by twice a coefficient strictly below
two, the connector is strictly shorter than two.  No sign hypothesis on the
connector is needed. -/
theorem diskFamily_length_lt_two_of_squared_bound
    {n : ℕ} {S p length : ℝ}
    (hbound : length ^ 2 ≤ 2 * diskFamilyCoefficient n S p)
    (hthreshold : diskFamilyCoefficient n S p < 2) :
    length < 2 := by
  have hsq : length ^ 2 < 4 := lt_of_le_of_lt hbound (by nlinarith)
  nlinarith [sq_nonneg (length - 2)]

/-- The uniform separation regime, composed with the consumer: in every
degree `n ≥ 3`, a connector obeying the disk-family squared bound at any
radius `4/3 ≤ S ≤ 2` and centre parameter `p ≥ 0` is strictly shorter than
two. -/
theorem diskFamily_length_lt_two_of_uniform_separation {n : ℕ} (hn : 3 ≤ n)
    {S p length : ℝ} (hS : 4 / 3 ≤ S) (hS2 : S ≤ 2) (hp0 : 0 ≤ p)
    (hbound : length ^ 2 ≤ 2 * diskFamilyCoefficient n S p) :
    length < 2 :=
  diskFamily_length_lt_two_of_squared_bound hbound
    (diskFamilyCoefficient_lt_two_of_uniform_separation hn hS hS2 hp0)

end ErdosProblems.Erdos1041
