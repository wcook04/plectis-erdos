import research_corpus.Erdos1041.ReciprocalNewtonExpansion
import Mathlib.Analysis.SpecialFunctions.Complex.LogBounds

/-!
# Actual reciprocal logarithmic series and its zeroth-order remainder

The root list may contain repetitions. A positive lower radius, not a
pre-supplied analytic function or convergent series, is the only supplier.
The term at index zero is zero by Lean's division convention. Consequently
`range (N+1)` represents the terms of positive degrees at most `N`.
The C1/C2 and general Newton-recurrence assertions are not silently credited
to this module; the exact paper correction removes those additional claims.
All compilation and axiom checks are UNRUN.
-/
set_option autoImplicit false
open scoped BigOperators
noncomputable section
namespace ErdosProblems.Erdos1041

def reciprocalPowerSumR11 {n : ℕ} (a : Fin n → ℂ) (k : ℕ) : ℂ :=
  ∑ j, (a j)⁻¹ ^ k

def reciprocalLogR11 {n : ℕ} (a : Fin n → ℂ) (z : ℂ) : ℂ :=
  ∑ j, Complex.log (1 - z / a j)

def reciprocalTaylorR11 {n : ℕ} (a : Fin n → ℂ) (N : ℕ) (z : ℂ) : ℂ :=
  ∑ j, Complex.logTaylor (N + 1) (-(z / a j))

theorem reciprocal_coefficient_sum {n : ℕ} (a : Fin n → ℂ) (z : ℂ) (k : ℕ) :
    (∑ j, (z / a j) ^ k / (k : ℂ)) =
      reciprocalPowerSumR11 a k * z ^ k / (k : ℂ) := by
  simp only [reciprocalPowerSumR11, div_pow, div_eq_mul_inv,
    inv_pow, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro j _
  ring

/-- The norm ratio lies strictly below one at every actual root factor. -/
theorem reciprocal_ratio_lt_one {n : ℕ} (a : Fin n → ℂ) {r : ℝ}
    (hr : 0 < r) (ha : ∀ j, r ≤ ‖a j‖) {z : ℂ} (hz : ‖z‖ < r)
    (j : Fin n) : ‖z / a j‖ < 1 := by
  rw [norm_div, div_lt_one (lt_of_lt_of_le hr (ha j))]
  exact hz.trans_le (ha j)

/-- Each actual logarithm factor lies in the open right half-plane. -/
theorem reciprocal_factor_re_pos {n : ℕ} (a : Fin n → ℂ) {r : ℝ}
    (hr : 0 < r) (ha : ∀ j, r ≤ ‖a j‖) {z : ℂ} (hz : ‖z‖ < r)
    (j : Fin n) : 0 < (1 - z / a j).re := by
  have ht := reciprocal_ratio_lt_one a hr ha hz j
  have hre := Complex.re_le_norm (z / a j)
  simp only [Complex.sub_re, Complex.one_re]
  linarith

/-- Complex `HasSum` for the actual finite sum of principal logarithms. -/
theorem hasSum_reciprocal_log {n : ℕ} (a : Fin n → ℂ) {r : ℝ}
    (hr : 0 < r) (ha : ∀ j, r ≤ ‖a j‖) {z : ℂ} (hz : ‖z‖ < r) :
    HasSum (fun k : ℕ => reciprocalPowerSumR11 a k * z ^ k / (k : ℂ))
      (-reciprocalLogR11 a z) := by
  have h := hasSum_sum (s := (Finset.univ : Finset (Fin n)))
    (fun j _ => Complex.hasSum_taylorSeries_neg_log
      (reciprocal_ratio_lt_one a hr ha hz j))
  simpa only [reciprocal_coefficient_sum, Finset.sum_neg_distrib,
    reciprocalLogR11] using h

private theorem log_norm_prod {ι : Type*} (s : Finset ι) (f : ι → ℂ)
    (hf : ∀ i ∈ s, f i ≠ 0) :
    Real.log ‖∏ i ∈ s, f i‖ = ∑ i ∈ s, Real.log ‖f i‖ := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert i s hi ih =>
    have hfi := hf i (Finset.mem_insert_self i s)
    have hfs : ∀ j ∈ s, f j ≠ 0 := fun j hj => hf j (Finset.mem_insert_of_mem hj)
    have hp : (∏ j ∈ s, f j) ≠ 0 := Finset.prod_ne_zero_iff.mpr hfs
    rw [Finset.prod_insert hi, norm_mul,
      Real.log_mul (norm_ne_zero_iff.mpr hfi) (norm_ne_zero_iff.mpr hp),
      Finset.sum_insert hi, ih hfs]

/-- Factorwise logarithms of norms, with all nonzero conditions discharged. -/
theorem reciprocal_log_modulus_identity {n : ℕ} (a : Fin n → ℂ) {r : ℝ}
    (hr : 0 < r) (ha : ∀ j, r ≤ ‖a j‖) {z : ℂ} (hz : ‖z‖ < r) :
    Real.log ‖∏ j, (z - a j)‖ = Real.log ‖∏ j, (-a j)‖ +
      (reciprocalLogR11 a z).re := by
  have ha0 : ∀ j, a j ≠ 0 :=
    fun j => norm_pos_iff.mp (lt_of_lt_of_le hr (ha j))
  have hf0 : ∀ j, 1 - z / a j ≠ 0 := by
    intro j he
    have hratio := reciprocal_ratio_lt_one a hr ha hz j
    have he' : z / a j = 1 := (sub_eq_zero.mp he).symm
    rw [he', norm_one] at hratio
    exact (lt_irrefl (1 : ℝ)) hratio
  have hfact (j : Fin n) : z - a j = (-a j) * (1 - z / a j) := by
    field_simp [ha0 j]
    <;> ring
  have hza : ∀ j, z - a j ≠ 0 := by
    intro j
    rw [hfact j]
    exact mul_ne_zero (neg_ne_zero.mpr (ha0 j)) (hf0 j)
  rw [log_norm_prod Finset.univ (fun j => z - a j) (fun j _ => hza j),
    log_norm_prod Finset.univ (fun j => -a j) (fun j _ => neg_ne_zero.mpr (ha0 j))]
  have hlog (j : Fin n) : Real.log ‖z - a j‖ =
      Real.log ‖-a j‖ + Real.log ‖1 - z / a j‖ := by
    rw [hfact j, norm_mul,
      Real.log_mul (norm_ne_zero_iff.mpr (neg_ne_zero.mpr (ha0 j)))
        (norm_ne_zero_iff.mpr (hf0 j))]
  simp only [hlog, Finset.sum_add_distrib, reciprocalLogR11,
    Complex.re_sum, Complex.log_re]

/-- The displayed reciprocal logarithmic expansion of the factored polynomial.
There is no holomorphic-log branch assertion for `log f` across a cut. -/
theorem reciprocal_log_modulus_series {n : ℕ} (a : Fin n → ℂ) {r : ℝ}
    (hr : 0 < r) (ha : ∀ j, r ≤ ‖a j‖) {z : ℂ} (hz : ‖z‖ < r) :
    Real.log ‖∏ j, (z - a j)‖ = Real.log ‖∏ j, (-a j)‖ -
      (∑' k : ℕ, reciprocalPowerSumR11 a k * z ^ k / (k : ℂ)).re := by
  rw [(hasSum_reciprocal_log a hr ha hz).tsum_eq, Complex.neg_re, sub_neg_eq_add]
  exact reciprocal_log_modulus_identity a hr ha hz

private theorem logTaylor_neg (N : ℕ) (t : ℂ) :
    Complex.logTaylor N (-t) = -(∑ k ∈ Finset.range N, t ^ k / (k : ℂ)) := by
  unfold Complex.logTaylor
  rw [← Finset.sum_neg_distrib]
  apply Finset.sum_congr rfl
  intro k _
  have hneg : (-t) ^ k = (-1 : ℂ) ^ k * t ^ k := neg_pow t k
  have hp : (-1 : ℂ) ^ k * (-1 : ℂ) ^ k = 1 := by
    rw [← mul_pow]
    norm_num
  rw [hneg, pow_succ]
  calc
    ((-1 : ℂ) ^ k * (-1)) * ((-1) ^ k * t ^ k) / (k : ℂ) =
        -(((-1 : ℂ) ^ k * (-1) ^ k) * t ^ k) / (k : ℂ) := by ring
    _ = -(t ^ k / (k : ℂ)) := by rw [hp]; ring

/-- Identification of Mathlib's log Taylor polynomials with the literal finite
reciprocal-coordinate sum; hence the remainder below is at the stated order. -/
theorem reciprocalTaylor_eq_coefficients {n : ℕ} (a : Fin n → ℂ)
    (N : ℕ) (z : ℂ) :
    reciprocalTaylorR11 a N z =
      -(∑ k ∈ Finset.range (N + 1), reciprocalPowerSumR11 a k * z ^ k / (k : ℂ)) := by
  simp only [reciprocalTaylorR11, logTaylor_neg, Finset.sum_neg_distrib]
  congr 1
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro k _
  exact reciprocal_coefficient_sum a z k

/-- Uniform zeroth-order Taylor remainder, including `z = 0` and `N = 0`. -/
theorem reciprocalTaylor_error_le {n : ℕ} (a : Fin n → ℂ) {r : ℝ}
    (hr : 0 < r) (ha : ∀ j, r ≤ ‖a j‖) {z : ℂ} (hz : ‖z‖ < r) (N : ℕ) :
    ‖reciprocalLogR11 a z - reciprocalTaylorR11 a N z‖ ≤
      (n : ℝ) * (‖z‖ / r) ^ (N + 1) / (((N : ℝ) + 1) * (1 - ‖z‖ / r)) := by
  let q : ℝ := ‖z‖ / r
  have hq0 : 0 ≤ q := div_nonneg (norm_nonneg z) hr.le
  have hq1 : q < 1 := (div_lt_one hr).mpr hz
  let B : ℝ := q ^ (N + 1) * (1 - q)⁻¹ / ((N : ℝ) + 1)
  have hterm (j : Fin n) :
      ‖Complex.log (1 - z / a j) - Complex.logTaylor (N + 1) (-(z / a j))‖ ≤ B := by
    have ht1 := reciprocal_ratio_lt_one a hr ha hz j
    have htq : ‖z / a j‖ ≤ q := by
      rw [norm_div]
      exact div_le_div_of_nonneg_left (norm_nonneg z) hr (ha j)
    have hbase := Complex.norm_log_sub_logTaylor_le N
      (show ‖-(z / a j)‖ < 1 by simpa only [norm_neg] using ht1)
    have hinv : (1 - ‖z / a j‖)⁻¹ ≤ (1 - q)⁻¹ := by
      have h := one_div_le_one_div_of_le (sub_pos.mpr hq1)
        (show 1 - q ≤ 1 - ‖z / a j‖ by linarith)
      simpa only [one_div] using h
    have hp := pow_le_pow_left₀ (norm_nonneg (z / a j)) htq (N + 1)
    have hmul := mul_le_mul hp hinv
      (inv_nonneg.mpr (sub_nonneg.mpr ht1.le)) (pow_nonneg hq0 (N + 1))
    have hdiv := div_le_div_of_nonneg_right hmul
      (show 0 ≤ (N : ℝ) + 1 by positivity)
    have hbase' :
        ‖Complex.log (1 - z / a j) - Complex.logTaylor (N + 1) (-(z / a j))‖ ≤
          ‖z / a j‖ ^ (N + 1) * (1 - ‖z / a j‖)⁻¹ / ((N : ℝ) + 1) := by
      simpa only [norm_neg, sub_eq_add_neg] using hbase
    exact hbase'.trans hdiv
  have he : reciprocalLogR11 a z - reciprocalTaylorR11 a N z =
      ∑ j, (Complex.log (1 - z / a j) -
        Complex.logTaylor (N + 1) (-(z / a j))) := by
    simp only [reciprocalLogR11, reciprocalTaylorR11, Finset.sum_sub_distrib]
  calc
    _ = ‖∑ j, (Complex.log (1 - z / a j) -
        Complex.logTaylor (N + 1) (-(z / a j)))‖ := by rw [he]
    _ ≤ ∑ j, ‖Complex.log (1 - z / a j) -
        Complex.logTaylor (N + 1) (-(z / a j))‖ := norm_sum_le _ _
    _ ≤ ∑ _j : Fin n, B := Finset.sum_le_sum (fun j _ => hterm j)
    _ = (n : ℝ) * B := by simp
    _ = _ := by
      dsimp [B, q]
      simp only [div_eq_mul_inv, mul_inv_rev]
      ring

/-- The literal coefficient-tail estimate in the corrected paper. -/
theorem reciprocal_log_remainder_le {n : ℕ} (a : Fin n → ℂ) {r : ℝ}
    (hr : 0 < r) (ha : ∀ j, r ≤ ‖a j‖) {z : ℂ} (hz : ‖z‖ < r) (N : ℕ) :
    ‖reciprocalLogR11 a z +
      (∑ k ∈ Finset.range (N + 1), reciprocalPowerSumR11 a k * z ^ k / (k : ℂ))‖ ≤
      (n : ℝ) * (‖z‖ / r) ^ (N + 1) / (((N : ℝ) + 1) * (1 - ‖z‖ / r)) := by
  simpa only [reciprocalTaylor_eq_coefficients, sub_neg_eq_add] using
    reciprocalTaylor_error_le a hr ha hz N

end ErdosProblems.Erdos1041
end
