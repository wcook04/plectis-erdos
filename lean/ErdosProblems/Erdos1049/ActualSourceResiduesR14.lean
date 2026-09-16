import ErdosProblems.Erdos1049.ReciprocalPochhammerR14
import ErdosProblems.Erdos1049.LambertSourceSummationR14
import Mathlib

/-!
# Residues of the literal 2004 rational kernel

Proves the partial-fraction residues of the 2004 rational kernel.

The denominator has 13*n+1 factors, as in the corrected analytic source.
Its residues are proved to be the existing integral A_s evaluated at 1/q,
with the exact pole-power factor. No abstract A/B pair is substituted.
-/
namespace ErdosProblems.Erdos1049.PaperR14
set_option maxHeartbeats 1000000
open Polynomial Finset
open PaperR10 PaperR11 PaperR12
open scoped BigOperators

noncomputable def sourcePoleParameter (q : ℝ) (n s : ℕ) : ℝ :=
  q ^ (14 * n + 1 + s)

noncomputable def sourceKernelNumerator (q : ℝ) (n : ℕ) : ℝ[X] :=
  C (qPochhammer q q (13 * n) / qPochhammer q q (12 * n)) *
    poleProduct (fun i : ℕ => q ^ (i + 1)) (range (12 * n))

noncomputable def sourceKernelDenominator (q : ℝ) (n : ℕ) : ℝ[X] :=
  poleProduct (sourcePoleParameter q n) (range (13 * n + 1))

noncomputable def sourceRationalKernel (q : ℝ) (n : ℕ) (z : ℝ) : ℝ :=
  (sourceKernelNumerator q n).eval z / (sourceKernelDenominator q n).eval z

lemma sourceKernelNumerator_degree (q : ℝ) (n : ℕ) :
    (sourceKernelNumerator q n).natDegree < (range (13 * n + 1)).card := by
  have hm := natDegree_mul_le
    (p := C (qPochhammer q q (13 * n) / qPochhammer q q (12 * n)))
    (q := poleProduct (fun i : ℕ => q ^ (i + 1)) (range (12 * n)))
  have hp := poleProduct_degree (fun i : ℕ => q ^ (i + 1)) (range (12 * n))
  simp only [natDegree_C, zero_add, card_range] at hm hp ⊢
  unfold sourceKernelNumerator
  omega

lemma sourcePoleParameter_nonzero {q : ℝ} (hq0 : 0 < q) (n s : ℕ) :
    sourcePoleParameter q n s ≠ 0 := pow_ne_zero _ hq0.ne'

lemma sourcePoleParameter_injective {q : ℝ} (hq0 : 0 < q) (hq1 : q < 1) (n : ℕ) :
    Function.Injective (sourcePoleParameter q n) := by
  intro s t h
  have he := (pow_right_strictAnti₀ hq0 hq1).injective h
  omega

lemma actual_source_residue_exponent (n s : ℕ) (hs : s ≤ 13 * n) :
    sourceM n + sourceAExponent n s + triangularExponent (13 * n) =
      (14 * n + 1) * (14 * n + 1 + s) +
        triangularExponent (12 * n) + triangularExponent (13 * n - s) := by
  have hc0 := twice_choose_two_int s
  have hc1 := twice_choose_two_int (12 * n)
  have hc2 := twice_choose_two_int (13 * n)
  have hc3 := twice_choose_two_int (13 * n - s)
  have hsub : ((13 * n - s : ℕ) : ℤ) = 13 * (n : ℤ) - (s : ℤ) := by
    rw [Nat.cast_sub hs]
    push_cast
    ring
  have he : ((sourceM n + sourceAExponent n s + triangularExponent (13 * n) : ℕ) : ℤ) =
      (((14 * n + 1) * (14 * n + 1 + s) +
        triangularExponent (12 * n) + triangularExponent (13 * n - s) : ℕ) : ℤ) := by
    simp only [sourceM, sourceAExponent, triangularExponent, Nat.cast_add, Nat.cast_mul,
      Nat.cast_pow, Nat.cast_ofNat, Nat.cast_one] at *
    rw [hsub] at hc3 ⊢
    nlinarith
  exact_mod_cast he

lemma actual_source_residue_factored {p : ℝ} (hp : 1 < p) (n s : ℕ) (hs : s ≤ 13 * n) :
    poleResidue (sourceKernelNumerator p⁻¹ n) (sourcePoleParameter p⁻¹ n)
        (range (13 * n + 1)) s =
      ((-1 : ℝ) ^ s * p ^ (triangularExponent (12 * n) +
          triangularExponent (13 * n - s)) / p ^ triangularExponent (13 * n)) *
        (gaussBinom p (14 * n + s) (12 * n) * gaussBinom p (13 * n) (13 * n - s)) := by
  have hp0 : p ≠ 0 := (zero_lt_one.trans hp).ne'
  have hA := qPochhammer_large_base_nonzero hp (12 * n)
  have hB := qPochhammer_large_base_nonzero hp s
  have hC := qPochhammer_large_base_nonzero hp (13 * n - s)
  have hg1 := gaussBinom_mul_qPochhammer p (show 12 * n ≤ 14 * n + s by omega)
  have he1 : 14 * n + s - 12 * n + 1 = 2 * n + s + 1 := by omega
  rw [he1] at hg1
  have hg2 := gaussBinom_mul_qPochhammer_qPochhammer p (13 * n) (13 * n - s)
    (Nat.sub_le _ _)
  have he2 : 13 * n - (13 * n - s) = s := by omega
  rw [he2] at hg2
  have hnumer : (sourceKernelNumerator p⁻¹ n).eval (p ^ (14 * n + 1 + s)) =
      (qPochhammer p⁻¹ p⁻¹ (13 * n) / qPochhammer p⁻¹ p⁻¹ (12 * n)) *
        qPochhammer p (p ^ (2 * n + s + 1)) (12 * n) := by
    simp only [sourceKernelNumerator, eval_mul, eval_C, poleProduct_eval]
    have he : 14 * n + 1 + s = (2 * n + s + 1) + 12 * n := by omega
    rw [he, reflected_numerator_product p hp0]
  have hdenom :
      (poleProduct (sourcePoleParameter p⁻¹ n) ((range (13 * n + 1)).erase s)).eval
          (p ^ (14 * n + 1 + s)) =
        qPochhammer p p s * qPochhammer p⁻¹ p⁻¹ (13 * n - s) := by
    simp only [poleProduct_eval, sourcePoleParameter]
    exact erased_geometric_pole_product p hp0 (14 * n + 1) (13 * n) s hs
  unfold poleResidue
  simp only [sourcePoleParameter, inv_pow, inv_inv]
  rw [hnumer, hdenom, qPochhammer_reciprocal_div p hp0 (13 * n),
    qPochhammer_reciprocal_div p hp0 (12 * n),
    qPochhammer_reciprocal_div p hp0 (13 * n - s)]
  have hsign : (-1 : ℝ) ^ (13 * n) = (-1 : ℝ) ^ s * (-1 : ℝ) ^ (13 * n - s) := by
    rw [← pow_add]
    congr 1
    omega
  have heven : (-1 : ℝ) ^ (12 * n) = 1 := by rw [pow_mul]; norm_num
  rw [hsign, heven, one_mul, ← hg1, ← hg2, pow_add]
  field_simp [hp0, hA, hB, hC]
  <;> ring

/-- Identification with the literal source coefficient, not just a Gaussian
expression with unproved exponent agreement. -/
theorem actual_source_residue {q : ℝ} (hq0 : 0 < q) (hq1 : q < 1)
    (n s : ℕ) (hs : s ≤ 13 * n) :
    poleResidue (sourceKernelNumerator q n) (sourcePoleParameter q n)
        (range (13 * n + 1)) s =
      q ^ ((14 * n + 1) * (14 * n + 1 + s)) *
        (sourceASummand n s).eval₂ (Int.castRingHom ℝ) q⁻¹ := by
  have hp : 1 < q⁻¹ := (one_lt_inv₀ hq0).mpr hq1
  have hp0 : q⁻¹ ≠ 0 := inv_ne_zero hq0.ne'
  have hres := actual_source_residue_factored hp n s hs
  rw [inv_inv] at hres
  rw [hres]
  have hAe : (sourceASummand n s).eval₂ (Int.castRingHom ℝ) q⁻¹ =
      (-1 : ℝ) ^ s * (q⁻¹) ^ (sourceM n + sourceAExponent n s) *
        (gaussBinom q⁻¹ (14 * n + s) (12 * n) *
          gaussBinom q⁻¹ (13 * n) (13 * n - s)) := by
    simp only [sourceASummand, sourceGaussianProduct, eval₂_mul, eval₂_C, eval₂_pow,
      eval₂_X, eval₂_neg, eval₂_one, map_pow, map_neg, map_one, eval₂_gaussBinom]
  rw [hAe]
  have hqpow : q ^ ((14 * n + 1) * (14 * n + 1 + s)) =
      ((q⁻¹) ^ ((14 * n + 1) * (14 * n + 1 + s)))⁻¹ := by simp
  rw [hqpow]
  have hexp := actual_source_residue_exponent n s hs
  have hpow :
      (q⁻¹) ^ (triangularExponent (12 * n) + triangularExponent (13 * n - s)) *
        (q⁻¹) ^ ((14 * n + 1) * (14 * n + 1 + s)) =
      (q⁻¹) ^ (sourceM n + sourceAExponent n s) *
        (q⁻¹) ^ triangularExponent (13 * n) := by
    rw [← pow_add, ← pow_add]
    congr 1
    omega
  have hPa : q⁻¹ ^ ((14 * n + 1) * (14 * n + 1 + s)) ≠ 0 := pow_ne_zero _ hp0
  have hPT : q⁻¹ ^ triangularExponent (13 * n) ≠ 0 := pow_ne_zero _ hp0
  rw [div_mul_eq_mul_div, eq_comm, inv_mul_eq_div, div_eq_div_iff hPa hPT]
  linear_combination -((-1 : ℝ) ^ s *
    gaussBinom q⁻¹ (14 * n + s) (12 * n) *
    gaussBinom q⁻¹ (13 * n) (13 * n - s)) * hpow

/-- Complete finite partial-fraction identity for the actual rational kernel. -/
theorem actual_source_partial_fractions {q : ℝ} (hq0 : 0 < q) (hq1 : q < 1)
    (n : ℕ) (z : ℝ)
    (hz : ∀ s ∈ range (13 * n + 1), 1 - q ^ (14 * n + 1 + s) * z ≠ 0) :
    sourceRationalKernel q n z =
      ∑ s ∈ range (13 * n + 1),
        (q ^ ((14 * n + 1) * (14 * n + 1 + s)) *
          (sourceASummand n s).eval₂ (Int.castRingHom ℝ) q⁻¹) /
          (1 - q ^ (14 * n + 1 + s) * z) := by
  unfold sourceRationalKernel sourceKernelDenominator
  rw [simple_pole_expansion _ _ _ (sourceKernelNumerator_degree q n)
    (fun s _ => sourcePoleParameter_nonzero hq0 n s)
    (sourcePoleParameter_injective hq0 hq1 n).injOn z hz]
  apply sum_congr rfl
  intro s hs
  rw [actual_source_residue hq0 hq1 n s (by have := mem_range.mp hs; omega)]
  rfl

end ErdosProblems.Erdos1049.PaperR14
