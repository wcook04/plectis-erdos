import ErdosProblems.Erdos1049.ActualSourceAnalyticIdentityR14
import ErdosProblems.Erdos1049.SourceOmegaCancellationR13
import ErdosProblems.Erdos1049.PaperShortCapR9
import Mathlib

/-!
# Evaluation and nonvanishing of the actual cancelled remainder

Proves the cancelled remainder is positive, with an exact log formula. The real normalisation is
proved directly from the actual integral inclusions. No nonzero source error,
analytic identity, or substitute polynomial pair is assumed.
-/
namespace ErdosProblems.Erdos1049.PaperR14
set_option maxHeartbeats 1000000
open Polynomial Finset
open PaperR10 PaperR11 PaperR12 PaperR13
open scoped BigOperators

lemma real_power_denominator_nonzero (p : ℝ) (hp : 1 < p) (j : ℕ) (hj : 0 < j) :
    p ^ j - 1 ≠ 0 := by
  have hpow : p ≤ p ^ j := by
    simpa only [pow_one] using pow_le_pow_right₀ hp.le (show 1 ≤ j by omega)
  exact (sub_pos.mpr (hp.trans_le hpow)).ne'

lemma real_cyclotomic_eval_nonzero (p : ℝ) (hp : 1 < p) (j : ℕ) (hj : 0 < j) :
    (cyclotomic j ℤ).eval₂ (Int.castRingHom ℝ) p ≠ 0 := by
  intro hzero
  obtain ⟨Q, hQ⟩ := Polynomial.cyclotomic.dvd_X_pow_sub_one j ℤ
  have h := congrArg (Polynomial.eval₂ (Int.castRingHom ℝ) p) hQ
  simp only [eval₂_sub, eval₂_pow, eval₂_X, eval₂_one, eval₂_mul, hzero, zero_mul] at h
  exact real_power_denominator_nonzero p hp j hj h

lemma actual_source_D_real_nonzero (p : ℝ) (hp : 1 < p) (n : ℕ) :
    (sourceD n).eval₂ (Int.castRingHom ℝ) p ≠ 0 := by
  change (eval₂RingHom (Int.castRingHom ℝ) p) (sourceD n) ≠ 0
  simp only [sourceD, map_prod]
  exact prod_ne_zero_iff.mpr (fun j hj =>
    real_cyclotomic_eval_nonzero p hp j (mem_Icc.mp hj).1)

lemma actual_source_Omega_and_complement_real_nonzero (p : ℝ) (hp : 1 < p) (n : ℕ) :
    (sourceOmega n).eval₂ (Int.castRingHom ℝ) p ≠ 0 ∧
      (sourceComplement n).eval₂ (Int.castRingHom ℝ) p ≠ 0 := by
  have h := actual_source_D_real_nonzero p hp n
  rw [sourceD_factor, eval₂_mul] at h
  exact mul_ne_zero_iff.mp h

lemma actual_real_B_normalisation (p : ℝ) (hp : 1 < p) (n : ℕ) :
    (sourceComplement n).eval₂ (Int.castRingHom ℝ) p * sourceBReal n p =
      p ^ sourceM n * (sourceV n).eval₂ (Int.castRingHom ℝ) p := by
  let f : ℤ[X] →+* ℝ := eval₂RingHom (Int.castRingHom ℝ) p
  have hclear := actual_B_first_clearing f n
    (by simpa [f] using (zero_lt_one.trans hp).ne')
    (by
      intro j hj
      simpa [f] using real_power_denominator_nonzero p hp j (mem_Icc.mp hj).1)
  have hinc := congrArg f (actual_B_polynomial_inclusion n)
  have hsplit := congrArg f (sourceD_factor n)
  simp only [map_mul, map_pow] at hinc hsplit
  rw [hsplit] at hclear
  rw [hclear] at hinc
  have hO : f (sourceOmega n) ≠ 0 :=
    (actual_source_Omega_and_complement_real_nonzero p hp n).1
  apply mul_left_cancel₀ hO
  simpa only [f, sourceBReal, coe_eval₂RingHom, eval₂_X, mul_assoc] using hinc

lemma actual_real_A_normalisation (p : ℝ) (n : ℕ) :
    (sourceComplement n).eval₂ (Int.castRingHom ℝ) p *
        (sourceA n).eval₂ (Int.castRingHom ℝ) p =
      p ^ sourceM n * (sourceU n).eval₂ (Int.castRingHom ℝ) p := by
  rw [sourceA_factor]
  simp only [sourceU, eval₂_mul, eval₂_pow, eval₂_X]
  ring

/-- Equality for the unchanged `polynomialRemainder` used by the paper's
height/rate consumers. This closes the source-to-consumer identification. -/
theorem actual_cancelled_remainder_identity (p : ℝ) (hp : 1 < p) (n : ℕ) :
    PaperR9.polynomialRemainder sourceU sourceV PaperR7.paperLambert p n =
      (sourceComplement n).eval₂ (Int.castRingHom ℝ) p * sourcePositiveH p⁻¹ n /
        p ^ sourceM n := by
  have hp0 := (zero_lt_one.trans hp).ne'
  apply (eq_div_iff (pow_ne_zero _ hp0)).mpr
  unfold PaperR9.polynomialRemainder
  have hA := actual_real_A_normalisation p n
  have hB := actual_real_B_normalisation p hp n
  have hH := actual_A_F_sub_B_eq_H_real p hp n
  calc
    _ = ((sourceComplement n).eval₂ (Int.castRingHom ℝ) p *
        (sourceA n).eval₂ (Int.castRingHom ℝ) p) * PaperR7.paperLambert p -
      (sourceComplement n).eval₂ (Int.castRingHom ℝ) p * sourceBReal n p := by
        rw [hA, hB]
        ring
    _ = _ := by rw [mul_assoc, ← mul_sub, hH]

/-- Actual nonvanishing, for every n and p>1, not merely eventual nonvanishing. -/
theorem actual_cancelled_remainder_nonzero (p : ℝ) (hp : 1 < p) (n : ℕ) :
    PaperR9.polynomialRemainder sourceU sourceV PaperR7.paperLambert p n ≠ 0 := by
  rw [actual_cancelled_remainder_identity p hp n]
  apply div_ne_zero
  · apply mul_ne_zero
    · exact (actual_source_Omega_and_complement_real_nonzero p hp n).2
    · have hp0 := zero_lt_one.trans hp
      exact (sourcePositiveH_pos (inv_pos.mpr hp0) ((inv_lt_one₀ hp0).mpr hp) n).ne'
  · exact pow_ne_zero _ (zero_lt_one.trans hp).ne'

/-- The unnormalised source error now inherits the already proved zero
quadratic logarithmic rate of the positive H series. -/
theorem actual_source_error_quadLogRate_zero (p : ℝ) (hp : 1 < p) :
    PaperR9.QuadLogRate
      (fun n => (sourceA n).eval₂ (Int.castRingHom ℝ) p * PaperR7.paperLambert p -
        sourceBReal n p) 0 := by
  have hp0 := zero_lt_one.trans hp
  simpa only [actual_A_F_sub_B_eq_H_real p hp] using
    sourcePositiveH_quadLogRate_zero (inv_pos.mpr hp0) ((inv_lt_one₀ hp0).mpr hp)

/-- Exact logarithmic decomposition; no missing cyclotomic rate is renamed
as a hypothesis of an asserted final source-rate theorem. -/
theorem actual_cancelled_remainder_log (p : ℝ) (hp : 1 < p) (n : ℕ) :
    Real.log |PaperR9.polynomialRemainder sourceU sourceV PaperR7.paperLambert p n| =
      Real.log |(sourceComplement n).eval₂ (Int.castRingHom ℝ) p| -
        (sourceM n : ℝ) * Real.log p + Real.log (sourcePositiveH p⁻¹ n) := by
  have hp0 := zero_lt_one.trans hp
  have hC := (actual_source_Omega_and_complement_real_nonzero p hp n).2
  have hH := sourcePositiveH_pos (inv_pos.mpr hp0) ((inv_lt_one₀ hp0).mpr hp) n
  rw [actual_cancelled_remainder_identity p hp n, abs_div, abs_mul,
    abs_of_pos hH, abs_of_pos (pow_pos hp0 _),
    Real.log_div (mul_ne_zero (abs_ne_zero.mpr hC) hH.ne') (pow_ne_zero _ hp0.ne'),
    Real.log_mul (abs_ne_zero.mpr hC) hH.ne', Real.log_pow]
  ring

end ErdosProblems.Erdos1049.PaperR14
