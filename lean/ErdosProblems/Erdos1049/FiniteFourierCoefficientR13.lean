import Mathlib

/-!
# Coefficient extraction from a finite circle, without complex integration


The sampling order is strictly larger than the actual polynomial degree;
this condition is essential to prevent aliasing. The extraction identity
uses every sample and the complete polynomial support.
-/
namespace ErdosProblems.Erdos1049.PaperR13
open Polynomial Finset
open scoped BigOperators

lemma finite_geometric_cleared {K : Type*} [CommRing K] (x : K) (M : ℕ) :
    (x - 1) * (∑ j ∈ range M, x ^ j) = x ^ M - 1 := by
  induction M with
  | zero => simp
  | succ M ih =>
      rw [sum_range_succ, mul_add, ih, pow_succ]
      ring

lemma fourier_no_alias (M d k : ℕ) (hd : d < M) (hk : k < M) :
    M ∣ d + (M - k) ↔ d = k := by
  constructor
  · rintro ⟨t, ht⟩
    have hM : 0 < M := by omega
    have hlow : 0 < d + (M - k) := by omega
    have hhigh : d + (M - k) < 2 * M := by omega
    have ht0 : 0 < t := by nlinarith
    have ht2 : t < 2 := by nlinarith
    have ht1 : t = 1 := by omega
    subst t
    omega
  · intro h
    subst d
    have he : k + (M - k) = M := Nat.add_sub_of_le hk.le
    rw [he]

lemma primitive_root_finite_sum {K : Type*} [Field K]
    (q : K) {M : ℕ} (hq : IsPrimitiveRoot q M) (a : ℕ) :
    (∑ j ∈ range M, q ^ (a * j)) = if M ∣ a then (M : K) else 0 := by
  by_cases ha : M ∣ a
  · have hp := (hq.pow_eq_one_iff_dvd a).mpr ha
    simp only [if_pos ha, pow_mul, hp, one_pow, sum_const, card_range, nsmul_eq_mul, mul_one]
  · have hp : q ^ a - 1 ≠ 0 := sub_ne_zero.mpr (fun h => ha (hq.dvd_of_pow_eq_one a h))
    have hg := finite_geometric_cleared (q ^ a) M
    have hpow : (q ^ a) ^ M = 1 := by
      rw [← pow_mul, Nat.mul_comm, pow_mul, hq.pow_eq_one, one_pow]
    rw [hpow, sub_self] at hg
    have hs := (mul_eq_zero.mp hg).resolve_left hp
    simpa only [if_neg ha, pow_mul] using hs

/-- Exact discrete Fourier extraction. The radius is arbitrary in this
algebraic identity, including zero; the subsequent norm bound assumes R>=1. -/
theorem polynomial_finite_fourier_identity (p : ℂ[X]) (R : ℂ)
    (M k : ℕ) (hdeg : p.natDegree < M) (hk : k < M)
    (q : ℂ) (hq : IsPrimitiveRoot q M) :
    (∑ j ∈ range M, p.eval (R * q ^ j) * q ^ ((M - k) * j)) =
      (M : ℂ) * (p.coeff k * R ^ k) := by
  classical
  have he : (∑ j ∈ range M, p.eval (R * q ^ j) * q ^ ((M - k) * j)) =
      ∑ d ∈ p.support, (p.coeff d * R ^ d) *
        (∑ j ∈ range M, q ^ ((d + (M - k)) * j)) := by
    simp only [eval_eq_sum, Polynomial.sum, sum_mul]
    rw [sum_comm]
    apply sum_congr rfl
    intro d hd
    rw [mul_sum]
    apply sum_congr rfl
    intro j hj
    rw [mul_pow, ← pow_mul]
    calc
      _ = (p.coeff d * R ^ d) * (q ^ (j * d) * q ^ ((M - k) * j)) := by ring
      _ = _ := by
        rw [← pow_add]
        congr 2
        ring
  rw [he]
  have hkern : ∀ d ∈ p.support,
      (∑ j ∈ range M, q ^ ((d + (M - k)) * j)) = if d = k then (M : ℂ) else 0 := by
    intro d hd
    rw [primitive_root_finite_sum q hq]
    simp only [fourier_no_alias M d k
      ((le_natDegree_of_ne_zero (mem_support_iff.mp hd)).trans_lt hdeg) hk]
  rw [sum_congr rfl (fun d hd => congrArg (fun t : ℂ => p.coeff d * R ^ d * t) (hkern d hd))]
  rw [sum_eq_single k]
  · simp [mul_comm]
  · intro d hd hdk
    simp [hdk]
  · intro hknot
    have hkzero : p.coeff k = 0 := by simpa [mem_support_iff] using hknot
    simp [hkzero]

/-- A circle supremum bounds every coefficient once its radius is at least
one. This proof is finite and has no analytic-contour or summability premise. -/
theorem polynomial_coeff_norm_le_circle_bound (p : ℂ[X]) (R B : ℝ)
    (hR : 1 ≤ R) (hB : 0 ≤ B)
    (hcircle : ∀ z : ℂ, ‖z‖ = R → ‖p.eval z‖ ≤ B) (k : ℕ) :
    ‖p.coeff k‖ ≤ B := by
  classical
  by_cases hkdeg : k ≤ p.natDegree
  · let M := p.natDegree + 1
    have hM : 0 < M := by dsimp [M]; omega
    let q : ℂ := Complex.exp (2 * Real.pi * Complex.I / M)
    have hq : IsPrimitiveRoot q M := Complex.isPrimitiveRoot_exp M hM.ne'
    have hqn : ‖q‖ = 1 := hq.norm'_eq_one hM.ne'
    have hMR : (0 : ℝ) < M := by exact_mod_cast hM
    have hk : k < M := by dsimp [M]; omega
    have he := congrArg norm (polynomial_finite_fourier_identity p (R : ℂ) M k
      (by dsimp [M]; omega) hk q hq)
    have hsum : ‖∑ j ∈ range M, p.eval ((R : ℂ) * q ^ j) * q ^ ((M - k) * j)‖ ≤
        (M : ℝ) * B := by
      apply (norm_sum_le _ _).trans
      calc
        _ ≤ ∑ j ∈ range M, B := by
          apply sum_le_sum
          intro j hj
          rw [norm_mul, norm_pow, hqn, one_pow, mul_one]
          apply hcircle
          simp only [norm_mul, Complex.norm_real, Real.norm_of_nonneg (zero_le_one.trans hR),
            norm_pow, hqn, one_pow, mul_one]
        _ = _ := by simp
    rw [he] at hsum
    simp only [norm_mul, Complex.norm_natCast, norm_pow, Complex.norm_real,
      Real.norm_of_nonneg (zero_le_one.trans hR)] at hsum
    have hcoeff : ‖p.coeff k‖ * R ^ k ≤ B := by
      nlinarith [hsum, hMR]
    have hp : 1 ≤ R ^ k := one_le_pow₀ hR
    calc
      ‖p.coeff k‖ = ‖p.coeff k‖ * 1 := (mul_one _).symm
      _ ≤ ‖p.coeff k‖ * R ^ k := mul_le_mul_of_nonneg_left hp (norm_nonneg _)
      _ ≤ B := hcoeff
  · rw [coeff_eq_zero_of_natDegree_lt (by omega), norm_zero]
    exact hB

/-- Integer-coefficient version, preserving the literal source polynomial. -/
theorem integer_coeff_abs_le_circle_bound (p : ℤ[X]) (R B : ℝ)
    (hR : 1 ≤ R) (hB : 0 ≤ B)
    (hcircle : ∀ z : ℂ, ‖z‖ = R → ‖p.eval₂ (Int.castRingHom ℂ) z‖ ≤ B)
    (k : ℕ) : (|p.coeff k| : ℝ) ≤ B := by
  have h := polynomial_coeff_norm_le_circle_bound (p.map (Int.castRingHom ℂ)) R B hR hB
    (by
      intro z hz
      simpa only [eval_map] using hcircle z hz) k
  rw [coeff_map] at h
  change ‖((p.coeff k : ℤ) : ℂ)‖ ≤ B at h
  simpa only [Complex.norm_intCast, Int.cast_abs] using h

end ErdosProblems.Erdos1049.PaperR13
