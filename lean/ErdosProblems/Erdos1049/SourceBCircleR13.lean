import ErdosProblems.Erdos1049.SourceOmegaCancellationR13
import ErdosProblems.Erdos1049.GaussianCircleBoundsR12
import Mathlib

/-!
# Uniform complex bound for literal B and the actual cancelled pair


The deliberately simple bound costs a polynomial factor 29*n^2 at radius
1+1/n, rather than a harmonic factor. Its logarithm is still O(log n).
All cancellation identities use the actual canonical U,V and the universal
Omega theorem, not an assumed polynomial inclusion.
-/
namespace ErdosProblems.Erdos1049.PaperR13
open Polynomial PaperR11 PaperR12 Finset
open scoped BigOperators

lemma complex_circle_denominator_lower (R : ℝ) (z : ℂ) (hR : 1 < R)
    (hz : ‖z‖ = R) (j : ℕ) (hj : 0 < j) :
    R - 1 ≤ ‖z ^ j - 1‖ := by
  have hp : R ≤ R ^ j := by
    simpa only [pow_one] using pow_le_pow_right₀ hR.le (show 1 ≤ j by omega)
  have h := norm_sub_norm_le (z ^ j) (1 : ℂ)
  rw [norm_pow, hz, norm_one] at h
  linarith

lemma complex_circle_denominator_nonzero (R : ℝ) (z : ℂ) (hR : 1 < R)
    (hz : ‖z‖ = R) (j : ℕ) (hj : 0 < j) : z ^ j - 1 ≠ 0 := by
  apply norm_ne_zero_iff.mp
  have h := complex_circle_denominator_lower R z hR hz j hj
  exact ne_of_gt (lt_of_lt_of_le (sub_pos.mpr hR) h)

lemma complex_circle_inverse_denominator_le (R : ℝ) (z : ℂ) (hR : 1 < R)
    (hz : ‖z‖ = R) (j : ℕ) (hj : 0 < j) :
    ‖(z ^ j - 1)⁻¹‖ ≤ (R - 1)⁻¹ := by
  rw [norm_inv]
  simpa only [one_div] using one_div_le_one_div_of_le (sub_pos.mpr hR)
    (complex_circle_denominator_lower R z hR hz j hj)

lemma complex_negative_power_norm_le_one (z : ℂ) (hz : 1 ≤ ‖z‖) (a : ℕ) :
    ‖z ^ (-(a : ℤ))‖ ≤ 1 := by
  rw [zpow_neg, zpow_natCast, norm_inv, norm_pow]
  have hp : 1 ≤ ‖z‖ ^ a := one_le_pow₀ hz
  have hb : (1 : ℝ) / ‖z‖ ^ a ≤ 1 := by
    apply (div_le_iff₀ (lt_of_lt_of_le zero_lt_one hp)).mpr
    simpa using hp
  simpa only [one_div] using hb

lemma complex_cyclotomic_eval_nonzero (R : ℝ) (z : ℂ) (hR : 1 < R)
    (hz : ‖z‖ = R) (j : ℕ) (hj : 0 < j) :
    (cyclotomic j ℤ).eval₂ (Int.castRingHom ℂ) z ≠ 0 := by
  intro hzero
  obtain ⟨p, hp⟩ := Polynomial.cyclotomic.dvd_X_pow_sub_one j ℤ
  have he := congrArg (Polynomial.eval₂ (Int.castRingHom ℂ) z) hp
  simp only [eval₂_sub, eval₂_pow, eval₂_X, eval₂_one, eval₂_mul, hzero, zero_mul] at he
  exact complex_circle_denominator_nonzero R z hR hz j hj he

lemma sourceD_complex_eval_nonzero (n : ℕ) (R : ℝ) (z : ℂ)
    (hR : 1 < R) (hz : ‖z‖ = R) :
    (sourceD n).eval₂ (Int.castRingHom ℂ) z ≠ 0 := by
  classical
  change (eval₂RingHom (Int.castRingHom ℂ) z) (sourceD n) ≠ 0
  simp only [sourceD, map_prod]
  apply Finset.prod_ne_zero_iff.mpr
  intro j hj
  exact complex_cyclotomic_eval_nonzero R z hR hz j (mem_Icc.mp hj).1

lemma sourceOmega_complex_eval_nonzero (n : ℕ) (R : ℝ) (z : ℂ)
    (hR : 1 < R) (hz : ‖z‖ = R) :
    (sourceOmega n).eval₂ (Int.castRingHom ℂ) z ≠ 0 := by
  have h := sourceD_complex_eval_nonzero n R z hR hz
  rw [sourceD_factor, eval₂_mul] at h
  exact (mul_ne_zero_iff.mp h).1

noncomputable def sourceBComplex (n : ℕ) (z : ℂ) : ℂ :=
  sourceBValue (eval₂RingHom (Int.castRingHom ℂ) z) n

noncomputable def sourceACircleMajorant (n : ℕ) (R : ℝ) : ℝ :=
  ((13 * n + 1 : ℕ) : ℝ) * (2 : ℝ) ^ (40 * n) * R ^ sourceK n

lemma sourceBComplex_inner_bound (n s : ℕ) (hs : s ≤ 13 * n)
    (R : ℝ) (z : ℂ) (hR : 1 < R) (hz : ‖z‖ = R) :
    ‖(∑ j ∈ Icc 1 (2 * n + s), (z ^ j - 1)⁻¹) +
      ∑ j ∈ Icc 1 (14 * n), z ^ (-((j * (2 * n + s) : ℕ) : ℤ)) *
        (z ^ j - 1)⁻¹‖ ≤ ((29 * n : ℕ) : ℝ) * (R - 1)⁻¹ := by
  have hC : 0 ≤ (R - 1)⁻¹ := inv_nonneg.mpr (sub_pos.mpr hR).le
  have hfirst : ‖∑ j ∈ Icc 1 (2 * n + s), (z ^ j - 1)⁻¹‖ ≤
      ((2 * n + s : ℕ) : ℝ) * (R - 1)⁻¹ := by
    apply (norm_sum_le _ _).trans
    calc
      _ ≤ ∑ j ∈ Icc 1 (2 * n + s), (R - 1)⁻¹ := by
        apply sum_le_sum
        intro j hj
        exact complex_circle_inverse_denominator_le R z hR hz j (mem_Icc.mp hj).1
      _ = _ := by simp
  have hsecond : ‖∑ j ∈ Icc 1 (14 * n), z ^ (-((j * (2 * n + s) : ℕ) : ℤ)) *
      (z ^ j - 1)⁻¹‖ ≤ ((14 * n : ℕ) : ℝ) * (R - 1)⁻¹ := by
    apply (norm_sum_le _ _).trans
    calc
      _ ≤ ∑ j ∈ Icc 1 (14 * n), (R - 1)⁻¹ := by
        apply sum_le_sum
        intro j hj
        rw [norm_mul]
        have ha := complex_negative_power_norm_le_one z (by rw [hz]; exact hR.le)
          (j * (2 * n + s))
        have hb := complex_circle_inverse_denominator_le R z hR hz j (mem_Icc.mp hj).1
        calc
          _ ≤ 1 * (R - 1)⁻¹ := mul_le_mul ha hb (norm_nonneg _) zero_le_one
          _ = _ := one_mul _
      _ = _ := by simp
  apply (norm_add_le _ _).trans
  have hc : ((2 * n + s : ℕ) : ℝ) + ((14 * n : ℕ) : ℝ) ≤ ((29 * n : ℕ) : ℝ) := by
    exact_mod_cast (show 2 * n + s + 14 * n ≤ 29 * n by omega)
  have hm := mul_le_mul_of_nonneg_right hc hC
  nlinarith

/-- Literal finite B, uniformly on the complete circle outside its poles. -/
theorem actual_B_complex_circle_le (n : ℕ) (R : ℝ) (z : ℂ)
    (hR : 1 < R) (hz : ‖z‖ = R) :
    ‖sourceBComplex n z‖ ≤ sourceACircleMajorant n R *
      (((29 * n : ℕ) : ℝ) * (R - 1)⁻¹) := by
  classical
  unfold sourceBComplex sourceBValue
  simp only [coe_eval₂RingHom, eval₂_X]
  apply (norm_sum_le _ _).trans
  calc
    _ ≤ ∑ s ∈ range (13 * n + 1),
        ((2 : ℝ) ^ (40 * n) * R ^ sourceK n) *
          (((29 * n : ℕ) : ℝ) * (R - 1)⁻¹) := by
      apply sum_le_sum
      intro s hs
      have hs' : s ≤ 13 * n := by have := mem_range.mp hs; omega
      rw [norm_mul]
      apply mul_le_mul
        (actual_ASummand_complex_disk_le n s hs' R z hR.le hz.le)
        (sourceBComplex_inner_bound n s hs' R z hR hz)
      · exact norm_nonneg _
      · positivity
    _ = _ := by simp [sourceACircleMajorant, mul_assoc]

/-- Exact division-free specialisation of the canonical cancelled B. -/
theorem actual_complex_B_normalisation (n : ℕ) (R : ℝ) (z : ℂ)
    (hR : 1 < R) (hz : ‖z‖ = R) :
    (sourceComplement n).eval₂ (Int.castRingHom ℂ) z * sourceBComplex n z =
      z ^ sourceM n * (sourceV n).eval₂ (Int.castRingHom ℂ) z := by
  let f : ℤ[X] →+* ℂ := eval₂RingHom (Int.castRingHom ℂ) z
  have hz0 : z ≠ 0 := norm_ne_zero_iff.mp (by rw [hz]; exact (zero_lt_one.trans hR).ne')
  have hclear := actual_B_first_clearing f n (by simpa [f] using hz0) (by
    intro j hj
    simpa [f] using complex_circle_denominator_nonzero R z hR hz j (mem_Icc.mp hj).1)
  have hinc := congrArg f (actual_B_polynomial_inclusion n)
  have hsplit := congrArg f (sourceD_factor n)
  simp only [map_mul, map_pow] at hinc hsplit
  rw [hsplit] at hclear
  rw [hclear] at hinc
  have hOmega : f (sourceOmega n) ≠ 0 := sourceOmega_complex_eval_nonzero n R z hR hz
  apply mul_left_cancel₀ hOmega
  simpa only [f, sourceBComplex, coe_eval₂RingHom, eval₂_X, mul_assoc] using hinc

/-- Both actual polynomials are controlled by the same explicit complement
factor. No surrogate pair is substituted for U,V. -/
theorem actual_cancelled_pair_circle_bound (n : ℕ) (R : ℝ) (z : ℂ)
    (hR : 1 < R) (hz : ‖z‖ = R) :
    ‖(sourceU n).eval₂ (Int.castRingHom ℂ) z‖ ≤
        ‖(sourceComplement n).eval₂ (Int.castRingHom ℂ) z‖ * sourceACircleMajorant n R ∧
    ‖(sourceV n).eval₂ (Int.castRingHom ℂ) z‖ ≤
        ‖(sourceComplement n).eval₂ (Int.castRingHom ℂ) z‖ * sourceACircleMajorant n R *
          (((29 * n : ℕ) : ℝ) * (R - 1)⁻¹) := by
  have hpow : 1 ≤ R ^ sourceM n := one_le_pow₀ hR.le
  have hA := actual_A_complex_disk_le n R z hR.le hz.le
  change ‖(sourceA n).eval₂ (Int.castRingHom ℂ) z‖ ≤ sourceACircleMajorant n R at hA
  have hAf := congrArg (fun p : ℤ[X] => ‖p.eval₂ (Int.castRingHom ℂ) z‖) (sourceA_factor n)
  simp only [eval₂_mul, eval₂_pow, eval₂_X, norm_mul, norm_pow, hz] at hAf
  have hA0 : ‖(sourceAWithoutMonomial n).eval₂ (Int.castRingHom ℂ) z‖ ≤
      sourceACircleMajorant n R := by
    have hm := mul_le_mul_of_nonneg_right hpow
      (norm_nonneg ((sourceAWithoutMonomial n).eval₂ (Int.castRingHom ℂ) z))
    rw [one_mul] at hm
    rw [← hAf] at hm
    exact hm.trans hA
  constructor
  · simp only [sourceU, eval₂_mul, norm_mul]
    exact mul_le_mul_of_nonneg_left hA0 (norm_nonneg _)
  · have he := congrArg norm (actual_complex_B_normalisation n R z hR hz)
    simp only [norm_mul, norm_pow, hz] at he
    have hm := mul_le_mul_of_nonneg_right hpow
      (norm_nonneg ((sourceV n).eval₂ (Int.castRingHom ℂ) z))
    rw [one_mul, ← he] at hm
    apply hm.trans
    have hb := mul_le_mul_of_nonneg_left (actual_B_complex_circle_le n R z hR hz)
      (norm_nonneg ((sourceComplement n).eval₂ (Int.castRingHom ℂ) z))
    simpa only [mul_assoc] using hb

/-- The source radius costs only a polynomial factor in the B channel. -/
theorem actual_B_source_radius_le (n : ℕ) (hn : 1 ≤ n) (z : ℂ)
    (hz : ‖z‖ = 1 + (1 : ℝ) / n) :
    ‖sourceBComplex n z‖ ≤ sourceACircleMajorant n (1 + (1 : ℝ) / n) *
      (29 * (n : ℝ) ^ 2) := by
  have hn0 : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  have hR : 1 < 1 + (1 : ℝ) / n := by
    have hi : 0 < (1 : ℝ) / n := div_pos zero_lt_one hn0
    linarith
  have h := actual_B_complex_circle_le n (1 + (1 : ℝ) / n) z hR hz
  have he : (((29 * n : ℕ) : ℝ) * ((1 + (1 : ℝ) / n) - 1)⁻¹) = 29 * (n : ℝ) ^ 2 := by
    push_cast
    field_simp
    <;> ring
  rwa [he] at h

end ErdosProblems.Erdos1049.PaperR13
