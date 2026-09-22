import ErdosProblems.Erdos1049.SourceBCircleR13
import ErdosProblems.Erdos1049.FiniteFourierCoefficientR13
import Mathlib

/-!
# Cyclotomic complement and actual cancelled-pair coefficient bounds

Bounds every coefficient of the cancelled pair U, V by a circle majorant.
Möbius inversion is applied to the actual nonzero complex evaluations.
Counting all divisor incidences gives the deliberately safe n*log(n)^2
scale; no false O(n*log(n)) cyclotomic estimate is used.
-/
namespace ErdosProblems.Erdos1049.PaperR13
open Polynomial PaperR11 PaperR12 Finset
open scoped BigOperators

noncomputable def divisorIncidence (N : ℕ) : ℕ :=
  ∑ j ∈ Icc 1 N, j.divisors.card

lemma divisors_antidiagonal_card (j : ℕ) : j.divisorsAntidiagonal.card = j.divisors.card := by
  rw [← Nat.map_div_right_divisors, Finset.card_map]

lemma divisorIncidence_eq_sum_div (N : ℕ) :
    divisorIncidence N = ∑ d ∈ Icc 1 N, N / d := by
  have hI : Ioc 0 N = Icc 1 N := by
    ext d
    simp only [mem_Ioc, mem_Icc]
    omega
  simpa only [divisorIncidence, hI, ArithmeticFunction.sigma_zero_apply] using
    ArithmeticFunction.sum_Ioc_sigma0_eq_sum_div N

/-- Quantitative elementary divisor-incidence bound, including N=0. -/
theorem divisorIncidence_le (N : ℕ) :
    (divisorIncidence N : ℝ) ≤ (N : ℝ) * (1 + Real.log N) := by
  rw [divisorIncidence_eq_sum_div, Nat.cast_sum]
  calc
    _ ≤ ∑ d ∈ Icc 1 N, (N : ℝ) * (d : ℝ)⁻¹ := by
      apply sum_le_sum
      intro d hd
      have hd0 : (0 : ℝ) < d := by exact_mod_cast (mem_Icc.mp hd).1
      have hmul : ((N / d : ℕ) : ℝ) * d ≤ N := by
        exact_mod_cast Nat.div_mul_le_self N d
      simpa only [div_eq_mul_inv] using (le_div_iff₀ hd0).mpr hmul
    _ = (N : ℝ) * (harmonic N : ℝ) := by
      rw [← mul_sum, harmonic_eq_sum_Icc]
      push_cast
      rfl
    _ ≤ _ := mul_le_mul_of_nonneg_left (harmonic_le_one_add_log N) (Nat.cast_nonneg _)

/-- The genuine Möbius product at every point strictly outside the unit circle. -/
theorem cyclotomic_complex_moebius (R : ℝ) (z : ℂ) (hR : 1 < R) (hz : ‖z‖ = R)
    (j : ℕ) (hj : 0 < j) :
    (cyclotomic j ℤ).eval₂ (Int.castRingHom ℂ) z =
      ∏ x ∈ j.divisorsAntidiagonal, (z ^ x.2 - 1) ^ ArithmeticFunction.moebius x.1 := by
  apply Eq.symm
  apply (ArithmeticFunction.prod_eq_iff_prod_pow_moebius_eq_of_nonzero
    (f := fun k => (cyclotomic k ℤ).eval₂ (Int.castRingHom ℂ) z)
    (g := fun k => z ^ k - 1)
    (fun k hk => complex_cyclotomic_eval_nonzero R z hR hz k hk)
    (fun k hk => complex_circle_denominator_nonzero R z hR hz k hk)).mp
      (fun k hk => ?_) j hj
  have he := congrArg (Polynomial.eval₂ (Int.castRingHom ℂ) z)
    (Polynomial.prod_cyclotomic_eq_X_pow_sub_one hk ℤ)
  simpa only [eval₂_finset_prod, eval₂_sub, eval₂_pow, eval₂_X, eval₂_one] using he

noncomputable def cyclotomicCircleBase (N : ℕ) (R : ℝ) : ℝ :=
  R ^ N * (2 + (R - 1)⁻¹)

lemma cyclotomicCircleBase_ge_one (N : ℕ) (R : ℝ) (hR : 1 < R) :
    1 ≤ cyclotomicCircleBase N R := by
  have hp : 1 ≤ R ^ N := one_le_pow₀ hR.le
  have hi : 0 ≤ (R - 1)⁻¹ := inv_nonneg.mpr (sub_pos.mpr hR).le
  unfold cyclotomicCircleBase
  nlinarith

lemma cyclotomic_moebius_factor_le (N d a : ℕ) (hd0 : 0 < d) (hd : d ≤ N)
    (R : ℝ) (z : ℂ) (hR : 1 < R) (hz : ‖z‖ = R) :
    ‖(z ^ d - 1) ^ ArithmeticFunction.moebius a‖ ≤ cyclotomicCircleBase N R := by
  have hp : 1 ≤ R ^ N := one_le_pow₀ hR.le
  have hi : 0 ≤ (R - 1)⁻¹ := inv_nonneg.mpr (sub_pos.mpr hR).le
  rcases ArithmeticFunction.moebius_eq_or a with ha | ha | ha
  · rw [ha, zpow_zero, norm_one]
    exact cyclotomicCircleBase_ge_one N R hR
  · rw [ha, zpow_one]
    have hs := norm_sub_le (z ^ d) (1 : ℂ)
    simp only [norm_pow, hz, norm_one] at hs
    have hdp := pow_le_pow_right₀ hR.le hd
    unfold cyclotomicCircleBase
    nlinarith
  · rw [ha, zpow_neg_one]
    have hs := complex_circle_inverse_denominator_le R z hR hz d hd0
    unfold cyclotomicCircleBase
    nlinarith

lemma cyclotomic_complex_circle_le (N j : ℕ) (hj0 : 0 < j) (hj : j ≤ N)
    (R : ℝ) (z : ℂ) (hR : 1 < R) (hz : ‖z‖ = R) :
    ‖(cyclotomic j ℤ).eval₂ (Int.castRingHom ℂ) z‖ ≤
      cyclotomicCircleBase N R ^ j.divisors.card := by
  rw [cyclotomic_complex_moebius R z hR hz j hj0, norm_prod]
  calc
    _ ≤ ∏ x ∈ j.divisorsAntidiagonal, cyclotomicCircleBase N R := by
      apply prod_le_prod (fun x hx => norm_nonneg _)
      intro x hx
      have hd := Nat.snd_mem_divisors_of_mem_antidiagonal hx
      exact cyclotomic_moebius_factor_le N x.2 x.1 (Nat.pos_of_mem_divisors hd)
        ((Nat.divisor_le hd).trans hj) R z hR hz
    _ = _ := by simp only [prod_const, divisors_antidiagonal_card]

/-- Uniform complement bound with every possible cyclotomic factor counted.
Dropping some factors is handled by a majorant >=1, not by assuming their
actual absolute values are >=1. -/
theorem actual_complement_complex_circle_le (n : ℕ) (R : ℝ) (z : ℂ)
    (hR : 1 < R) (hz : ‖z‖ = R) :
    ‖(sourceComplement n).eval₂ (Int.castRingHom ℂ) z‖ ≤
      cyclotomicCircleBase (15 * n) R ^ divisorIncidence (15 * n) := by
  classical
  change ‖(eval₂RingHom (Int.castRingHom ℂ) z) (sourceComplement n)‖ ≤ _
  simp only [sourceComplement, map_prod, norm_prod]
  calc
    _ ≤ ∏ j ∈ Icc 1 (15 * n), cyclotomicCircleBase (15 * n) R ^ j.divisors.card := by
      apply prod_le_prod (fun j hj => norm_nonneg _)
      intro j hj
      split_ifs with hw
      · exact cyclotomic_complex_circle_le (15 * n) j (mem_Icc.mp hj).1
          (mem_Icc.mp hj).2 R z hR hz
      · simp only [map_one, norm_one]
        exact one_le_pow₀ (cyclotomicCircleBase_ge_one (15 * n) R hR)
    _ = _ := by rw [prod_pow_eq_pow_sum]; rfl

noncomputable def sourceHeightMajorant (n : ℕ) (R : ℝ) : ℝ :=
  cyclotomicCircleBase (15 * n) R ^ divisorIncidence (15 * n) *
    sourceACircleMajorant n R * (1 + ((29 * n : ℕ) : ℝ) * (R - 1)⁻¹)

lemma sourceHeightMajorant_nonneg (n : ℕ) (R : ℝ) (hR : 1 < R) :
    0 ≤ sourceHeightMajorant n R := by
  have hR0 : 0 ≤ R := (zero_lt_one.trans hR).le
  have hi : 0 ≤ (R - 1)⁻¹ := inv_nonneg.mpr (sub_pos.mpr hR).le
  unfold sourceHeightMajorant sourceACircleMajorant cyclotomicCircleBase
  positivity

/-- An unconditional explicit coefficient bound for the actual U,V. -/
theorem actual_cancelled_pair_coefficients_le (n k : ℕ) (R : ℝ) (hR : 1 < R) :
    (|(sourceU n).coeff k| : ℝ) ≤ sourceHeightMajorant n R ∧
    (|(sourceV n).coeff k| : ℝ) ≤ sourceHeightMajorant n R := by
  have hC0 : 0 ≤ cyclotomicCircleBase (15 * n) R ^ divisorIncidence (15 * n) :=
    pow_nonneg (zero_le_one.trans (cyclotomicCircleBase_ge_one (15 * n) R hR)) _
  have hA0 : 0 ≤ sourceACircleMajorant n R := by
    unfold sourceACircleMajorant
    have hR0 : 0 ≤ R := (zero_lt_one.trans hR).le
    positivity
  have hB0 : 0 ≤ ((29 * n : ℕ) : ℝ) * (R - 1)⁻¹ := by
    apply mul_nonneg (Nat.cast_nonneg _)
    exact inv_nonneg.mpr (sub_pos.mpr hR).le
  have hbound (z : ℂ) (hz : ‖z‖ = R) :
      ‖(sourceU n).eval₂ (Int.castRingHom ℂ) z‖ ≤ sourceHeightMajorant n R ∧
      ‖(sourceV n).eval₂ (Int.castRingHom ℂ) z‖ ≤ sourceHeightMajorant n R := by
    have hc := actual_complement_complex_circle_le n R z hR hz
    have hp := actual_cancelled_pair_circle_bound n R z hR hz
    have hca := mul_le_mul_of_nonneg_right hc hA0
    have hcab := mul_le_mul_of_nonneg_right hca hB0
    unfold sourceHeightMajorant
    constructor <;> nlinarith [mul_nonneg hC0 hA0]
  exact ⟨integer_coeff_abs_le_circle_bound (sourceU n) R _ hR.le
      (sourceHeightMajorant_nonneg n R hR) (fun z hz => (hbound z hz).1) k,
    integer_coeff_abs_le_circle_bound (sourceV n) R _ hR.le
      (sourceHeightMajorant_nonneg n R hR) (fun z hz => (hbound z hz).2) k⟩

/-- Exact specialisation at 1+1/n. This is a bound for actual integer
coefficients, not merely for values at the positive real point. -/
theorem actual_cancelled_pair_source_radius_coefficients (n k : ℕ) (hn : 1 ≤ n) :
    let R := 1 + (1 : ℝ) / n
    let H := (R ^ (15 * n) * (n + 2)) ^ divisorIncidence (15 * n) *
      (((13 * n + 1 : ℕ) : ℝ) * (2 : ℝ) ^ (40 * n) * R ^ sourceK n) *
      (1 + 29 * (n : ℝ) ^ 2)
    (|(sourceU n).coeff k| : ℝ) ≤ H ∧ (|(sourceV n).coeff k| : ℝ) ≤ H := by
  have hn0 : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  have hR : 1 < 1 + (1 : ℝ) / n := by
    have hi := div_pos (show (0 : ℝ) < 1 by norm_num) hn0
    linarith
  have h := actual_cancelled_pair_coefficients_le n k (1 + (1 : ℝ) / n) hR
  dsimp
  convert h using 1 <;>
    simp [sourceHeightMajorant, sourceACircleMajorant, cyclotomicCircleBase,
      hn0.ne', Nat.cast_mul, mul_assoc, pow_two] <;> ring

end ErdosProblems.Erdos1049.PaperR13
