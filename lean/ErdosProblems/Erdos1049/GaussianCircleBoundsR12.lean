import ErdosProblems.Erdos1049.GaussianDegreeR12
import Mathlib

/-!
# Actual source A on a complex circle


The bound uses the complete Gaussian coefficient mass and the exact source
summand degrees. It applies to every point of the closed disk, not just the
positive real radius. No coefficient-height assumption is made. The separate
cyclotomic-complement and cancelled-B estimates remain separate suppliers.
-/
namespace ErdosProblems.Erdos1049.PaperR12
open Polynomial PaperR11
open scoped BigOperators

/-- Elementary coefficient-mass estimate, with all coefficients counted. -/
theorem polynomial_complex_eval_le_mass (p : ℤ[X]) (R : ℝ) (z : ℂ)
    (hR : 1 ≤ R) (hz : ‖z‖ ≤ R) :
    ‖p.eval₂ (Int.castRingHom ℂ) z‖ ≤
      (integerCoefficientMass p : ℝ) * R ^ p.natDegree := by
  classical
  rw [eval₂_eq_sum]
  unfold Polynomial.sum
  calc
    ‖∑ d ∈ p.support, (p.coeff d : ℂ) * z ^ d‖ ≤
        ∑ d ∈ p.support, ‖(p.coeff d : ℂ) * z ^ d‖ := norm_sum_le _ _
    _ ≤ ∑ d ∈ p.support, (|p.coeff d| : ℝ) * R ^ p.natDegree := by
      apply Finset.sum_le_sum
      intro d hd
      rw [norm_mul, Complex.norm_intCast, norm_pow, ← Int.cast_abs]
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      exact (pow_le_pow_left₀ (norm_nonneg z) hz d).trans
        (pow_le_pow_right₀ hR (le_natDegree_of_ne_zero (mem_support_iff.mp hd)))
    _ = (integerCoefficientMass p : ℝ) * R ^ p.natDegree := by
      rw [← Finset.sum_mul]
      congr 1
      rw [integerCoefficientMass, Int.cast_sum]
      apply Finset.sum_congr rfl
      intro i hi
      simpa only [Int.cast_abs]

/-- Uniform Gaussian bound on the whole disk |z|<=R. -/
theorem gaussian_complex_disk_le (n k : ℕ) (hk : k ≤ n) (R : ℝ) (z : ℂ)
    (hR : 1 ≤ R) (hz : ‖z‖ ≤ R) :
    ‖gaussBinom z n k‖ ≤ (2 : ℝ) ^ n * R ^ (k * (n - k)) := by
  have h := polynomial_complex_eval_le_mass (gaussBinom (X : ℤ[X]) n k) R z hR hz
  rw [eval₂_gaussBinom, gaussian_polynomial_natDegree n k hk] at h
  apply h.trans
  apply mul_le_mul_of_nonneg_right _ (pow_nonneg (by linarith) _)
  exact_mod_cast gaussian_coefficient_mass_le n k

/-- Each actual residue polynomial satisfies one common source-sized bound. -/
theorem actual_ASummand_complex_disk_le (n s : ℕ) (hs : s ≤ 13 * n)
    (R : ℝ) (z : ℂ) (hR : 1 ≤ R) (hz : ‖z‖ ≤ R) :
    ‖(sourceASummand n s).eval₂ (Int.castRingHom ℂ) z‖ ≤
      (2 : ℝ) ^ (40 * n) * R ^ sourceK n := by
  have hG1 := gaussian_complex_disk_le (14 * n + s) (12 * n) (by omega) R z hR hz
  have hG2 := gaussian_complex_disk_le (13 * n) (13 * n - s) (by omega) R z hR hz
  have hi1 : 14 * n + s - 12 * n = 2 * n + s := by omega
  have hi2 : 13 * n - (13 * n - s) = s := by omega
  rw [hi1] at hG1
  rw [hi2] at hG2
  have hp := pow_le_pow_left₀ (norm_nonneg z) hz (sourceM n + sourceAExponent n s)
  have hform : ‖(sourceASummand n s).eval₂ (Int.castRingHom ℂ) z‖ =
      ‖z‖ ^ (sourceM n + sourceAExponent n s) *
        ‖gaussBinom z (14 * n + s) (12 * n)‖ *
        ‖gaussBinom z (13 * n) (13 * n - s)‖ := by
    simp only [sourceASummand, sourceGaussianProduct, eval₂_mul, eval₂_C,
      eval₂_pow, eval₂_X, eval₂_neg, eval₂_one, map_pow, map_neg, map_one, eval₂_gaussBinom,
      norm_mul, norm_pow, norm_neg, norm_one, one_pow, one_mul, mul_assoc]
  rw [hform]
  have hleft := mul_le_mul hp hG1 (norm_nonneg _) (pow_nonneg (by linarith) _)
  calc
    _ ≤ (R ^ (sourceM n + sourceAExponent n s) *
          ((2 : ℝ) ^ (14 * n + s) * R ^ (12 * n * (2 * n + s)))) *
        ((2 : ℝ) ^ (13 * n) * R ^ ((13 * n - s) * s)) :=
      mul_le_mul hleft hG2 (norm_nonneg _) (by positivity)
    _ = (2 : ℝ) ^ (27 * n + s) * R ^ sourceASummandDegree n s := by
      have he : 27 * n + s = (14 * n + s) + 13 * n := by omega
      rw [he]
      simp only [sourceASummandDegree, pow_add]
      ring
    _ ≤ (2 : ℝ) ^ (40 * n) * R ^ sourceK n := by
      apply mul_le_mul
      · exact pow_le_pow_right₀ (by norm_num) (by omega)
      · apply pow_le_pow_right₀ hR
        rw [← sourceASummandDegree_last]
        rcases lt_or_eq_of_le hs with hlt | rfl
        · exact (sourceASummandDegree_strict n hlt le_rfl).le
        · exact le_rfl
      · exact pow_nonneg (by linarith) _
      · positivity

/-- Uniform actual A bound, with no missing number-of-summands factor. -/
theorem actual_A_complex_disk_le (n : ℕ) (R : ℝ) (z : ℂ)
    (hR : 1 ≤ R) (hz : ‖z‖ ≤ R) :
    ‖(sourceA n).eval₂ (Int.castRingHom ℂ) z‖ ≤
      ((13 * n + 1 : ℕ) : ℝ) * (2 : ℝ) ^ (40 * n) * R ^ sourceK n := by
  classical
  have he : (sourceA n).eval₂ (Int.castRingHom ℂ) z =
      ∑ s ∈ Finset.range (13 * n + 1),
        (sourceASummand n s).eval₂ (Int.castRingHom ℂ) z := by
    exact map_sum (eval₂RingHom (Int.castRingHom ℂ) z) _ _
  rw [he]
  calc
    _ ≤ ∑ s ∈ Finset.range (13 * n + 1),
        ‖(sourceASummand n s).eval₂ (Int.castRingHom ℂ) z‖ := norm_sum_le _ _
    _ ≤ ∑ s ∈ Finset.range (13 * n + 1),
        (2 : ℝ) ^ (40 * n) * R ^ sourceK n := by
      apply Finset.sum_le_sum
      intro s hs
      exact actual_ASummand_complex_disk_le n s
        (by have hh := Finset.mem_range.mp hs; omega) R z hR hz
    _ = _ := by simp [mul_assoc]

/-- The requested radius is valid at every positive source index. -/
theorem actual_A_source_radius_le (n : ℕ) (hn : 1 ≤ n) (z : ℂ)
    (hz : ‖z‖ ≤ 1 + (1 : ℝ) / n) :
    ‖(sourceA n).eval₂ (Int.castRingHom ℂ) z‖ ≤
      ((13 * n + 1 : ℕ) : ℝ) * (2 : ℝ) ^ (40 * n) *
        (1 + (1 : ℝ) / n) ^ sourceK n := by
  apply actual_A_complex_disk_le n (1 + (1 : ℝ) / n) z _ hz
  have hn' : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  have hdiv : 0 ≤ (1 : ℝ) / n := div_nonneg (by norm_num) hn'.le
  linarith

end ErdosProblems.Erdos1049.PaperR12
