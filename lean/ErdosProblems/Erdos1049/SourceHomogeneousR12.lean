import ErdosProblems.Erdos1049.SourceFiniteTransformR12
import ErdosProblems.Erdos1049.SourceBClearingR12
import ErdosProblems.Erdos1049.GaussianDegreeR12
import Mathlib

/-!
# Homogeneous finite transform and monomial cancellation tools

Homogenisation removes the need to assert
that a Laurent expression is an integral polynomial. The identity is first
proved in a field, then pulled back through the injective fraction-field map.
The final displayed identity is entirely in Z[X].
-/
namespace ErdosProblems.Erdos1049.PaperR12
open Polynomial
open scoped BigOperators

lemma map_gaussian {R S : Type*} [CommRing R] [CommRing S]
    (f : R →+* S) (q : R) (n k : ℕ) : f (gaussBinom q n k) = gaussBinom (f q) n k := by
  induction n generalizing k with
  | zero => cases k <;> simp [gaussBinom]
  | succ n ih =>
      cases k with
      | zero => simp
      | succ k =>
          rw [gaussBinom_succ, gaussBinom_succ, map_add]
          split_ifs <;> simp only [map_mul, map_pow, map_zero, ih]

lemma map_finitePochhammer {R S : Type*} [CommRing R] [CommRing S]
    (f : R →+* S) (q z : R) (n : ℕ) :
    f (qPochhammer q z n) = qPochhammer (f q) (f z) n := by
  induction n with
  | zero => simp
  | succ n ih => simp only [qPochhammer_succ, map_mul, map_sub, map_one, map_pow, ih]

/-- Homogeneous product: no inverse of the polynomial variable occurs. -/
def homogeneousPochhammer {R : Type*} [CommRing R]
    (q y : R) (h N : ℕ) : R :=
  ∏ i ∈ Finset.range N, (y - q ^ (h + i))

def homogeneousSourceInner {R : Type*} [CommRing R]
    (q y : R) (a d v : ℕ) : R :=
  ∑ s ∈ Finset.range v, (-1 : R) ^ s * q ^ s.choose 2 * y ^ (v - 1 - s) *
    gaussBinom q (v - 1) s * gaussBinom q (a + d + s - 1) (a - 1)

lemma pow_mul_inverse_power {K : Type*} [Field K] (y : K) (hy : y ≠ 0)
    (N s : ℕ) (hs : s ≤ N) : y ^ N * (y⁻¹) ^ s = y ^ (N - s) := by
  calc
    _ = (y ^ (N - s) * y ^ s) * (y⁻¹) ^ s := by
      rw [← pow_add, Nat.sub_add_cancel hs]
    _ = y ^ (N - s) := by
      rw [mul_assoc, ← mul_pow, mul_inv_cancel₀ hy, one_pow, mul_one]

lemma homogeneousPochhammer_clearing {K : Type*} [Field K]
    (q y : K) (hy : y ≠ 0) (h N : ℕ) :
    y ^ N * qPochhammer q (y⁻¹ * q ^ h) N = homogeneousPochhammer q y h N := by
  induction N with
  | zero => simp [homogeneousPochhammer]
  | succ N ih =>
      rw [qPochhammer_succ, pow_succ]
      have hf : y * (1 - y⁻¹ * q ^ h * q ^ N) = y - q ^ (h + N) := by
        rw [pow_add]
        field_simp [hy]
        <;> ring
      calc
        _ = (y ^ N * qPochhammer q (y⁻¹ * q ^ h) N) *
            (y * (1 - y⁻¹ * q ^ h * q ^ N)) := by ring
        _ = homogeneousPochhammer q y h N * (y - q ^ (h + N)) := by rw [ih, hf]
        _ = homogeneousPochhammer q y h (N + 1) := by
          simp only [homogeneousPochhammer, Finset.prod_range_succ]

lemma homogeneousSourceInner_clearing {K : Type*} [Field K]
    (q y : K) (hy : y ≠ 0) (a d v : ℕ) :
    y ^ (v - 1) * sourceInnerZ q y⁻¹ a d v = homogeneousSourceInner q y a d v := by
  unfold sourceInnerZ homogeneousSourceInner
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro s hs
  have hs' : s ≤ v - 1 := by have hh := Finset.mem_range.mp hs; omega
  calc
    _ = (-1 : K) ^ s * q ^ s.choose 2 *
        (y ^ (v - 1) * (y⁻¹) ^ s) *
        gaussBinom q (v - 1) s * gaussBinom q (a + d + s - 1) (a - 1) := by ring
    _ = _ := by rw [pow_mul_inverse_power y hy (v - 1) s hs']

/-- Homogenised form of the finite two-q-binomial transform. -/
theorem homogeneous_source_transform {K : Type*} [Field K]
    (q y : K) (hy : y ≠ 0) {a d v : ℕ} (ha : 1 ≤ a) (hv : 1 ≤ v) :
    qPochhammer q q (a - 1) * homogeneousSourceInner q y a d v =
      ∑ h ∈ Finset.range a, (-1 : K) ^ h * q ^ (h * (d + 1) + h.choose 2) *
        gaussBinom q (a - 1) h * homogeneousPochhammer q y h (v - 1) := by
  rw [← homogeneousSourceInner_clearing q y hy]
  calc
    _ = y ^ (v - 1) * (qPochhammer q q (a - 1) * sourceInnerZ q y⁻¹ a d v) := by ring
    _ = y ^ (v - 1) * (∑ h ∈ Finset.range a,
        (-1 : K) ^ h * q ^ (h * (d + 1) + h.choose 2) *
          gaussBinom q (a - 1) h * qPochhammer q (y⁻¹ * q ^ h) (v - 1)) := by
      rw [sourceInnerZ_qPochhammer q y⁻¹ ha hv]
    _ = _ := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro h hh
      calc
        _ = ((-1 : K) ^ h * q ^ (h * (d + 1) + h.choose 2) *
            gaussBinom q (a - 1) h) *
              (y ^ (v - 1) * qPochhammer q (y⁻¹ * q ^ h) (v - 1)) := by ring
        _ = _ := by rw [homogeneousPochhammer_clearing q y hy]

/-- Pullback gives a genuine integral-polynomial identity, even when the
unhomogenised argument would have a negative exponent. -/
theorem homogeneous_source_transform_polynomial (u : ℕ) {a d v : ℕ}
    (ha : 1 ≤ a) (hv : 1 ≤ v) :
    qPochhammer (X : ℤ[X]) X (a - 1) *
        homogeneousSourceInner X (X ^ u) a d v =
      ∑ h ∈ Finset.range a, (-1 : ℤ[X]) ^ h * X ^ (h * (d + 1) + h.choose 2) *
        gaussBinom X (a - 1) h * homogeneousPochhammer X (X ^ u) h (v - 1) := by
  let f : ℤ[X] →+* RatFunc ℤ := algebraMap ℤ[X] (RatFunc ℤ)
  have hy : (f X) ^ u ≠ 0 := pow_ne_zero _ rationalPolynomial_X_ne_zero
  have ht := homogeneous_source_transform (f X) ((f X) ^ u) hy
    (a := a) (d := d) (v := v) ha hv
  have hm : f (qPochhammer (X : ℤ[X]) X (a - 1) *
        homogeneousSourceInner X (X ^ u) a d v -
      ∑ h ∈ Finset.range a, (-1 : ℤ[X]) ^ h * X ^ (h * (d + 1) + h.choose 2) *
        gaussBinom X (a - 1) h * homogeneousPochhammer X (X ^ u) h (v - 1)) = 0 := by
    simp only [map_sub, map_mul, map_sum, map_pow, map_neg, map_one,
      map_gaussian, map_finitePochhammer, homogeneousSourceInner,
      homogeneousPochhammer, map_prod] at ht ⊢
    exact sub_eq_zero.mpr ht
  change algebraMap ℤ[X] (RatFunc ℤ) _ = 0 at hm
  rw [IsFractionRing.to_map_eq_zero_iff] at hm
  exact sub_eq_zero.mp hm

/-- Cancellation of a polynomial with constant coefficient 1 at every
X-adic depth. This is elementary coefficient induction, not an axiom about
orders or a unit in an unspecified completion. -/
theorem X_power_dvd_cancel_constant_one (c p : ℤ[X]) (m : ℕ)
    (hc : c.coeff 0 = 1) (h : (X : ℤ[X]) ^ m ∣ c * p) : X ^ m ∣ p := by
  classical
  have hz := Polynomial.X_pow_dvd_iff.mp h
  apply Polynomial.X_pow_dvd_iff.mpr
  have hcoeff : ∀ d : ℕ, d < m → p.coeff d = 0 := by
    intro d
    induction d using Nat.strong_induction_on with
    | h d ih =>
        intro hd
        have hprod : (c * p).coeff d = p.coeff d := by
          rw [coeff_mul, Finset.sum_eq_single (0, d)]
          · simp [hc]
          · rintro ⟨i, j⟩ hij hne
            have hsum : i + j = d := Finset.mem_antidiagonal.mp hij
            have hjlt : j < d := by
              by_contra hh
              have hi0 : i = 0 := by omega
              have hjd : j = d := by omega
              exact hne (by simp [hi0, hjd])
            rw [ih j hjlt (by omega), mul_zero]
          · intro hnot
            exact (hnot (Finset.mem_antidiagonal.mpr (by omega))).elim
        rw [← hprod]
        exact hz d hd
  exact hcoeff

lemma X_power_dvd_of_le (m e : ℕ) (h : m ≤ e) :
    (X : ℤ[X]) ^ m ∣ X ^ e := by
  refine ⟨X ^ (e - m), ?_⟩
  have he : m + (e - m) = e := by omega
  rw [← pow_add, he]

/-- Every h at or below u hits an actual zero factor. -/
theorem homogeneousPochhammer_zero (u h N : ℕ) (hu : u < N) (hh : h ≤ u) :
    homogeneousPochhammer (X : ℤ[X]) (X ^ u) h N = 0 := by
  unfold homogeneousPochhammer
  apply Finset.prod_eq_zero (Finset.mem_range.mpr (show u - h < N by omega))
  have he : h + (u - h) = u := by omega
  rw [he, sub_self]

/-- Every h above u has a displayed X^(u*N) factor. -/
theorem homogeneousPochhammer_factor (u h N : ℕ) (hh : u < h) :
    homogeneousPochhammer (X : ℤ[X]) (X ^ u) h N =
      X ^ (u * N) * ∏ i ∈ Finset.range N, (1 - X ^ (h + i - u)) := by
  have hf (i : ℕ) : (X : ℤ[X]) ^ u - X ^ (h + i) =
      X ^ u * (1 - X ^ (h + i - u)) := by
    have he : u + (h + i - u) = h + i := by omega
    rw [mul_sub, mul_one, ← pow_add, he]
  unfold homogeneousPochhammer
  simp_rw [hf]
  rw [Finset.prod_mul_distrib]
  simp only [Finset.prod_const, Finset.card_range, ← pow_mul]

end ErdosProblems.Erdos1049.PaperR12
