import ErdosProblems.Erdos1049.SourceBMonomialR12
import Mathlib

/-!
# Exact initial coefficient of the actual B numerator


The numerator is divisible by X^M but not X^(M+1): at every n>=1 its
coefficient at M is exactly 1. This is proved by isolating the actual j=n,
s=0 channel. No finite reconstruction or initial-order hypothesis is used.
-/
namespace ErdosProblems.Erdos1049.PaperR12
open Polynomial PaperR11
open scoped BigOperators

theorem gaussian_constant_coefficient (n k : ℕ) (hk : k ≤ n) :
    (gaussBinom (X : ℤ[X]) n k).coeff 0 = 1 := by
  have h := congrArg (constantCoeff : ℤ[X] →+* ℤ)
    (gaussBinom_mul_qPochhammer_qPochhammer (X : ℤ[X]) n k hk)
  simpa only [map_mul, qPochhammer_X_constantCoeff, mul_one] using h

theorem sourceGaussianProduct_constant_coefficient (n s : ℕ) (hs : s ≤ 13 * n) :
    (sourceGaussianProduct n s).coeff 0 = 1 := by
  change constantCoeff (sourceGaussianProduct n s) = 1
  unfold sourceGaussianProduct
  rw [map_mul]
  change (gaussBinom (X : ℤ[X]) (14 * n + s) (12 * n)).coeff 0 *
    (gaussBinom (X : ℤ[X]) (13 * n) (13 * n - s)).coeff 0 = 1
  rw [gaussian_constant_coefficient _ _ (by omega),
    gaussian_constant_coefficient _ _ (by omega), one_mul]

/-- Phi_1 is absent from the quotient because 1 divides every positive j. -/
theorem sourceDQuotient_constant_coefficient (n j : ℕ) (hj : 0 < j) :
    (sourceDQuotient n j).coeff 0 = 1 := by
  classical
  change constantCoeff (sourceDQuotient n j) = 1
  simp only [sourceDQuotient, map_prod]
  apply Finset.prod_eq_one
  intro l hl
  obtain ⟨hlrange, hnot⟩ := Finset.mem_sdiff.mp hl
  have hlpos : 1 ≤ l := (Finset.mem_Icc.mp hlrange).1
  have hlne : l ≠ 1 := by
    intro he
    apply hnot
    rw [he]
    exact Nat.mem_divisors.mpr ⟨one_dvd _, ne_of_gt hj⟩
  exact cyclotomic_coeff_zero ℤ (show 2 ≤ l by omega)

lemma coefficient_zero_of_X_power_dvd (p : ℤ[X]) (m : ℕ)
    (h : (X : ℤ[X]) ^ (m + 1) ∣ p) : p.coeff m = 0 :=
  Polynomial.X_pow_dvd_iff.mp h m (by omega)

lemma sourceASummand_strict_monomial (n s : ℕ) (hn : 1 ≤ n) :
    (X : ℤ[X]) ^ (sourceM n + 1) ∣ sourceASummand n s := by
  unfold sourceASummand
  apply X_power_dvd_signed_summand
  unfold sourceAExponent
  nlinarith [Nat.zero_le ((n + 1) * s), Nat.zero_le (s.choose 2)]

lemma sourceShiftedASummand_strict_early (n s j : ℕ) (hn : 1 ≤ n) (hj : j < n) :
    (X : ℤ[X]) ^ (sourceM n + 1) ∣ sourceShiftedASummand n s j := by
  have hm := Nat.mul_le_mul_right (2 * n + s) (show j + 1 ≤ n by omega)
  have he : j * (2 * n + s) + 1 ≤ sourceAExponent n s := by
    unfold sourceAExponent
    nlinarith [Nat.zero_le (s.choose 2)]
  unfold sourceShiftedASummand
  apply X_power_dvd_signed_summand
  omega

lemma sourceShiftedASummand_middle_exponent (n s : ℕ) :
    sourceM n + sourceAExponent n s - n * (2 * n + s) =
      sourceM n + s + s.choose 2 := by
  have h : sourceM n + sourceAExponent n s =
      sourceM n + s + s.choose 2 + n * (2 * n + s) := by
    unfold sourceAExponent
    ring
  omega

lemma sourceShiftedASummand_middle_strict (n s : ℕ) (hs : 0 < s) :
    (X : ℤ[X]) ^ (sourceM n + 1) ∣ sourceShiftedASummand n s n := by
  unfold sourceShiftedASummand
  rw [sourceShiftedASummand_middle_exponent]
  apply X_power_dvd_signed_summand
  omega

/-- The one channel capable of contributing to degree M has coefficient 1. -/
theorem actual_middle_channel_initial (n : ℕ) (hn : 1 ≤ n) :
    (sourceShiftedASum n n * sourceDQuotient n n).coeff (sourceM n) = 1 := by
  classical
  unfold sourceShiftedASum
  rw [Finset.sum_mul, finset_sum_coeff, Finset.sum_eq_single 0]
  · have hform : sourceShiftedASummand n 0 n =
        (X : ℤ[X]) ^ sourceM n * sourceGaussianProduct n 0 := by
      unfold sourceShiftedASummand
      rw [sourceShiftedASummand_middle_exponent]
      simp
    rw [hform, mul_assoc, coeff_X_pow_mul']
    simp only [le_refl, if_true, Nat.sub_self]
    change constantCoeff (sourceGaussianProduct n 0 * sourceDQuotient n n) = 1
    rw [map_mul]
    change (sourceGaussianProduct n 0).coeff 0 * (sourceDQuotient n n).coeff 0 = 1
    rw [sourceGaussianProduct_constant_coefficient n 0 (by omega),
      sourceDQuotient_constant_coefficient n n (by omega), one_mul]
  · intro s hs hsne
    exact coefficient_zero_of_X_power_dvd _ _
      (dvd_mul_of_dvd_left (sourceShiftedASummand_middle_strict n s (by omega)) _)
  · intro hnot
    exact (hnot (Finset.mem_range.mpr (by omega))).elim

/-- All late channels start strictly after M, not merely at M. -/
theorem actual_shifted_A_sum_strict_late (n j : ℕ)
    (hjn : n < j) (hj : j ≤ 14 * n) :
    (X : ℤ[X]) ^ (sourceM n + 1) ∣ sourceShiftedASum n j := by
  let u := j - n - 1
  have hu : u < 13 * n := by dsimp [u]; omega
  have hju : j = n + u + 1 := by dsimp [u]; omega
  obtain ⟨v, hv⟩ := homogeneous_source_inner_dvd n u hu
  rw [sourceShiftedASum_homogeneous n j u hj hu hju, hv, ← mul_assoc, ← pow_add]
  have he : sourceM n + 1 ≤ sourceHomogeneousBase n j u + sourceHomogeneousOrder n u := by
    rw [sourceHomogeneousBase_order n j u hj hu hju]
    omega
  exact dvd_mul_of_dvd_left (X_power_dvd_of_le _ _ he) v

/-- The actual integral numerator has a unit coefficient at its claimed order. -/
theorem actual_B_initial_coefficient (n : ℕ) (hn : 1 ≤ n) :
    (sourceClearedB n).coeff (sourceM n) = 1 := by
  classical
  rw [sourceClearedB_reordered, coeff_add]
  have hfirst : (∑ s ∈ Finset.range (13 * n + 1),
      ∑ l ∈ Finset.Icc 1 (2 * n + s),
        sourceASummand n s * sourceDQuotient n l).coeff (sourceM n) = 0 := by
    apply coefficient_zero_of_X_power_dvd
    apply Finset.dvd_sum
    intro s hs
    apply Finset.dvd_sum
    intro l hl
    exact dvd_mul_of_dvd_left (sourceASummand_strict_monomial n s hn) _
  rw [hfirst, zero_add, finset_sum_coeff, Finset.sum_eq_single n]
  · exact actual_middle_channel_initial n hn
  · intro j hj hjn
    apply coefficient_zero_of_X_power_dvd
    apply dvd_mul_of_dvd_left
    rcases lt_or_gt_of_ne hjn with hlt | hgt
    · unfold sourceShiftedASum
      exact Finset.dvd_sum (fun s _ => sourceShiftedASummand_strict_early n s j hn hlt)
    · exact actual_shifted_A_sum_strict_late n j hgt (Finset.mem_Icc.mp hj).2
  · intro hnot
    exact (hnot (Finset.mem_Icc.mpr ⟨hn, by omega⟩)).elim

theorem actual_B_without_monomial_constant (n : ℕ) (hn : 1 ≤ n) :
    (sourceBWithoutMonomial n).coeff 0 = 1 := by
  have h := actual_B_initial_coefficient n hn
  rw [actual_B_monomial_factor, coeff_X_pow_mul'] at h
  simpa only [le_refl, if_true, Nat.sub_self] using h

theorem actual_B_without_monomial_ne_zero (n : ℕ) (hn : 1 ≤ n) :
    sourceBWithoutMonomial n ≠ 0 := by
  intro h
  have hc := actual_B_without_monomial_constant n hn
  rw [h, coeff_zero] at hc
  norm_num at hc

theorem actual_B_order_exact (n : ℕ) (hn : 1 ≤ n) :
    (X : ℤ[X]) ^ sourceM n ∣ sourceClearedB n ∧
      ¬ (X : ℤ[X]) ^ (sourceM n + 1) ∣ sourceClearedB n := by
  refine ⟨actual_B_monomial_divisibility n, ?_⟩
  intro h
  have hz := coefficient_zero_of_X_power_dvd _ _ h
  rw [actual_B_initial_coefficient n hn] at hz
  norm_num at hz

/-- At the far end the entire channel vanishes, since every transformed
finite product contains a zero factor. -/
theorem actual_shifted_A_sum_far_zero (n j : ℕ)
    (hjlo : 13 * n < j) (hjhi : j ≤ 14 * n) : sourceShiftedASum n j = 0 := by
  let u := j - n - 1
  have hu : u < 13 * n := by dsimp [u]; omega
  have hul : 12 * n ≤ u := by dsimp [u]; omega
  have hju : j = n + u + 1 := by dsimp [u]; omega
  have ht := homogeneous_source_transform_polynomial u
    (a := 12 * n + 1) (d := 2 * n) (v := 13 * n + 1) (by omega) (by omega)
  simp only [Nat.add_sub_cancel] at ht
  have hz : qPochhammer (X : ℤ[X]) X (12 * n) *
      homogeneousSourceInner X (X ^ u) (12 * n + 1) (2 * n) (13 * n + 1) = 0 := by
    rw [ht]
    apply Finset.sum_eq_zero
    intro h hh
    have hhu : h ≤ u := by have hh' := Finset.mem_range.mp hh; omega
    rw [homogeneousPochhammer_zero u h (13 * n) hu hhu, mul_zero]
  have hi := (mul_eq_zero.mp hz).resolve_left (qPochhammer_X_ne_zero (12 * n))
  rw [sourceShiftedASum_homogeneous n j u hjhi hu hju, hi, mul_zero]

end ErdosProblems.Erdos1049.PaperR12
