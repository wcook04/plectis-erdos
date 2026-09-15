import ErdosProblems.Erdos1049.SourcePolynomialR11
import Mathlib

/-!
# Exact Gaussian and actual A degrees


The unique highest summand is proved at every index; finite reconstructions
are not used to infer a polynomial identity. The integer coefficient mass of
each Gaussian is also evaluated exactly, rather than bounding one coefficient
and silently treating that as an l1 bound.
-/
namespace ErdosProblems.Erdos1049.PaperR12
open Polynomial
open PaperR11
open scoped BigOperators

/-- The recurrence specialises to the ordinary binomial coefficient at q=1. -/
theorem gaussian_at_one {R : Type*} [CommRing R] (n k : ℕ) :
    gaussBinom (1 : R) n k = (n.choose k : R) := by
  induction n generalizing k with
  | zero => cases k <;> simp [gaussBinom]
  | succ n ih =>
      cases k with
      | zero => simp
      | succ k =>
          rw [gaussBinom_succ, Nat.choose_succ_succ, Nat.cast_add, ih, ih]
          by_cases hk : k ≤ n
          · simp [hk, add_comm]
          · have hkn : n < k := Nat.lt_of_not_ge hk
            simp [hk, Nat.choose_eq_zero_of_lt hkn]

/-- Symmetry for the actual integral Gaussian polynomial follows by cancelling
nonzero finite Pochhammer polynomials, not by choosing a second definition. -/
theorem gaussian_polynomial_symmetry (n k : ℕ) (hk : k ≤ n) :
    gaussBinom (X : ℤ[X]) n k = gaussBinom X n (n - k) := by
  have hnk : n - k ≤ n := Nat.sub_le n k
  have hsub : n - (n - k) = k := Nat.sub_sub_self hk
  have h1 := gaussBinom_mul_qPochhammer_qPochhammer (X : ℤ[X]) n k hk
  have h2 := gaussBinom_mul_qPochhammer_qPochhammer (X : ℤ[X]) n (n - k) hnk
  rw [hsub] at h2
  apply mul_right_cancel₀ (mul_ne_zero (qPochhammer_X_ne_zero k)
    (qPochhammer_X_ne_zero (n - k)))
  calc
    _ = qPochhammer X X n := by simpa only [mul_assoc] using h1
    _ = _ := by simpa only [mul_assoc, mul_comm, mul_left_comm] using h2.symm

/-- Monicity and exact degree of the recurrence-defined Gaussian polynomial. -/
theorem gaussian_monic_natDegree (n k : ℕ) (hk : k ≤ n) :
    (gaussBinom (X : ℤ[X]) n k).Monic ∧
      (gaussBinom (X : ℤ[X]) n k).natDegree = k * (n - k) := by
  induction n generalizing k with
  | zero =>
      have hk0 : k = 0 := by omega
      subst k
      simp [gaussBinom]
  | succ n ih =>
      cases k with
      | zero => simp
      | succ k =>
          have hkn : k ≤ n := by omega
          by_cases heq : k = n
          · subst k
            simp [gaussBinom_self]
          · have hlt : k < n := by omega
            obtain ⟨hL, hdL⟩ := ih (k + 1) (by omega)
            obtain ⟨hG, hdG⟩ := ih k hkn
            have hR : ((X : ℤ[X]) ^ (n - k) * gaussBinom X n k).Monic :=
              (monic_X_pow (n - k)).mul hG
            have hdR : ((X : ℤ[X]) ^ (n - k) * gaussBinom X n k).natDegree =
                (n - k) + k * (n - k) := by
              rw [natDegree_mul' (by simp [hG.leadingCoeff]), natDegree_X_pow, hdG]
            have hsub : n - (k + 1) + 1 = n - k := by omega
            have hdeglt : (gaussBinom (X : ℤ[X]) n (k + 1)).natDegree <
                ((X : ℤ[X]) ^ (n - k) * gaussBinom X n k).natDegree := by
              rw [hdL, hdR]
              nlinarith
            rw [gaussBinom_succ_of_le X hkn]
            constructor
            · change (_ + _ : ℤ[X]).leadingCoeff = 1
              rw [leadingCoeff_add_of_degree_lt (degree_lt_degree hdeglt), hR.leadingCoeff]
            · rw [natDegree_add_eq_right_of_natDegree_lt hdeglt, hdR]
              have hsub' : n + 1 - (k + 1) = n - k := by omega
              rw [hsub']
              ring

theorem gaussian_polynomial_monic (n k : ℕ) (hk : k ≤ n) :
    (gaussBinom (X : ℤ[X]) n k).Monic := (gaussian_monic_natDegree n k hk).1

theorem gaussian_polynomial_natDegree (n k : ℕ) (hk : k ≤ n) :
    (gaussBinom (X : ℤ[X]) n k).natDegree = k * (n - k) :=
  (gaussian_monic_natDegree n k hk).2

noncomputable def integerCoefficientMass (p : ℤ[X]) : ℤ :=
  ∑ d ∈ p.support, |p.coeff d|

/-- Exact l1 mass, including the out-of-range zero Gaussian. -/
theorem gaussian_coefficient_mass (n k : ℕ) :
    integerCoefficientMass (gaussBinom (X : ℤ[X]) n k) = (n.choose k : ℤ) := by
  have heval : (gaussBinom (X : ℤ[X]) n k).eval 1 = (n.choose k : ℤ) := by
    simpa [gaussian_at_one] using (eval₂_gaussBinom (1 : ℤ) n k)
  rw [← heval, eval_eq_sum]
  unfold integerCoefficientMass Polynomial.sum
  apply Finset.sum_congr rfl
  intro d hd
  simp only [one_pow, mul_one]
  exact abs_of_nonneg (gaussian_coefficient_bounds n k d).1

/-- The exponential l1 bound has no missing degree factor. -/
theorem gaussian_coefficient_mass_le (n k : ℕ) :
    integerCoefficientMass (gaussBinom (X : ℤ[X]) n k) ≤ (2 : ℤ) ^ n := by
  rw [gaussian_coefficient_mass]
  exact_mod_cast choose_le_two_pow n k

/-- Degree and monicity of the two actual source factors together. -/
theorem sourceGaussianProduct_monic_degree (n s : ℕ) (hs : s ≤ 13 * n) :
    (sourceGaussianProduct n s).Monic ∧
      (sourceGaussianProduct n s).natDegree =
        12 * n * (2 * n + s) + (13 * n - s) * s := by
  obtain ⟨h1, hd1⟩ := gaussian_monic_natDegree (14 * n + s) (12 * n) (by omega)
  obtain ⟨h2, hd2⟩ := gaussian_monic_natDegree (13 * n) (13 * n - s) (by omega)
  unfold sourceGaussianProduct
  constructor
  · exact h1.mul h2
  · rw [natDegree_mul' (by simp [h1.leadingCoeff, h2.leadingCoeff]), hd1, hd2]
    have he1 : 14 * n + s - 12 * n = 2 * n + s := by omega
    have he2 : 13 * n - (13 * n - s) = s := by omega
    rw [he1, he2]

def sourceASummandDegree (n s : ℕ) : ℕ :=
  sourceM n + sourceAExponent n s +
    12 * n * (2 * n + s) + (13 * n - s) * s

/-- Every actual summand has the displayed degree and a nonzero signed top. -/
theorem sourceASummand_degree_and_leadingCoeff (n s : ℕ) (hs : s ≤ 13 * n) :
    (sourceASummand n s).natDegree = sourceASummandDegree n s ∧
      (sourceASummand n s).leadingCoeff = (-1 : ℤ) ^ s := by
  obtain ⟨hG, hdG⟩ := sourceGaussianProduct_monic_degree n s hs
  have hmono : ((X : ℤ[X]) ^ (sourceM n + sourceAExponent n s) *
      sourceGaussianProduct n s).Monic := (monic_X_pow _).mul hG
  have hs0 : (-1 : ℤ) ^ s ≠ 0 := pow_ne_zero _ (by norm_num)
  have hform : sourceASummand n s = C ((-1 : ℤ) ^ s) *
      (X ^ (sourceM n + sourceAExponent n s) * sourceGaussianProduct n s) := by
    unfold sourceASummand
    ring
  rw [hform]
  constructor
  · rw [natDegree_mul' (by simp [hmono.leadingCoeff, hs0]), natDegree_C, zero_add,
      natDegree_mul' (by simp [hG.leadingCoeff]), natDegree_X_pow, hdG]
    unfold sourceASummandDegree
    omega
  · exact hmono.leadingCoeff_C_mul _

lemma sourceASummandDegree_succ (n s : ℕ) (hs : s < 13 * n) :
    sourceASummandDegree n (s + 1) = sourceASummandDegree n s + (26 * n - s) := by
  have hsub : 13 * n - (s + 1) + 1 = 13 * n - s := by omega
  have hsub2 : 26 * n - s + s = 26 * n := by omega
  unfold sourceASummandDegree sourceAExponent
  rw [choose_two_succ]
  rw [← hsub, ← hsub2]
  ring_nf
  omega

/-- No cancellation of the top degree is possible in the full alternating sum. -/
theorem sourceASummandDegree_strict (n : ℕ) {s t : ℕ}
    (hst : s < t) (ht : t ≤ 13 * n) :
    sourceASummandDegree n s < sourceASummandDegree n t := by
  induction t with
  | zero => omega
  | succ t ih =>
      have ht' : t < 13 * n := by omega
      have hstep : sourceASummandDegree n t < sourceASummandDegree n (t + 1) := by
        rw [sourceASummandDegree_succ n t ht']
        have hpos : 0 < 26 * n - t := by omega
        omega
      rcases Nat.lt_succ_iff_lt_or_eq.mp hst with hst' | rfl
      · exact (ih hst' (by omega)).trans hstep
      · exact hstep

lemma polynomial_sum_natDegree_le {ι : Type*} (s : Finset ι)
    (p : ι → ℤ[X]) (d : ℕ) (h : ∀ i ∈ s, (p i).natDegree ≤ d) :
    (∑ i ∈ s, p i).natDegree ≤ d := by
  apply natDegree_le_of_degree_le
  apply (degree_le_iff_coeff_zero _ _).2
  intro j hj
  have hj' : d < j := by exact_mod_cast hj
  rw [finset_sum_coeff]
  apply Finset.sum_eq_zero
  intro i hi
  exact coeff_eq_zero_of_natDegree_lt ((h i hi).trans_lt hj')

lemma twice_choose_two_nat (s : ℕ) : 2 * s.choose 2 + s = s * s := by
  have h := twice_choose_two_int s
  have hi : (2 : ℤ) * (s.choose 2 : ℤ) + (s : ℤ) = (s : ℤ) * (s : ℤ) := by
    nlinarith
  exact_mod_cast hi

/-- The printed K is integral; natural division here is justified below. -/
def sourceK (n : ℕ) : ℕ := (1091 * n ^ 2 + 81 * n + 2) / 2

lemma sourceASummandDegree_last (n : ℕ) : sourceASummandDegree n (13 * n) = sourceK n := by
  have hc := twice_choose_two_nat (13 * n)
  have hd : 2 * sourceASummandDegree n (13 * n) = 1091 * n ^ 2 + 81 * n + 2 := by
    unfold sourceASummandDegree sourceAExponent sourceM
    simp only [Nat.sub_self, zero_mul, add_zero]
    nlinarith
  unfold sourceK
  omega

/-- All-index exact source A degree and top coefficient. -/
theorem actual_A_degree_and_leadingCoeff (n : ℕ) :
    (sourceA n).natDegree = sourceK n ∧
      (sourceA n).leadingCoeff = (-1 : ℤ) ^ (13 * n) := by
  classical
  have hlast := sourceASummand_degree_and_leadingCoeff n (13 * n) le_rfl
  have hbound : (sourceA n).natDegree ≤ sourceASummandDegree n (13 * n) := by
    unfold sourceA
    apply polynomial_sum_natDegree_le
    intro s hs
    have hs' : s ≤ 13 * n := by have hh := Finset.mem_range.mp hs; omega
    rw [(sourceASummand_degree_and_leadingCoeff n s hs').1]
    rcases lt_or_eq_of_le hs' with hlt | rfl
    · exact (sourceASummandDegree_strict n hlt le_rfl).le
    · exact le_rfl
  have hcoeff : (sourceA n).coeff (sourceASummandDegree n (13 * n)) =
      (-1 : ℤ) ^ (13 * n) := by
    unfold sourceA
    rw [finset_sum_coeff]
    rw [Finset.sum_eq_single (13 * n)]
    · rw [← hlast.1, coeff_natDegree, hlast.2]
    · intro s hs hne
      have hs' : s < 13 * n := by have hh := Finset.mem_range.mp hs; omega
      apply coeff_eq_zero_of_natDegree_lt
      rw [(sourceASummand_degree_and_leadingCoeff n s hs'.le).1]
      exact sourceASummandDegree_strict n hs' le_rfl
    · intro hnot
      exact (hnot (Finset.mem_range.mpr (Nat.lt_succ_self _))).elim
  have hdegree : (sourceA n).natDegree = sourceASummandDegree n (13 * n) :=
    natDegree_eq_of_le_of_coeff_ne_zero hbound
      (by rw [hcoeff]; exact pow_ne_zero _ (by norm_num : (-1 : ℤ) ≠ 0))
  constructor
  · exact hdegree.trans (sourceASummandDegree_last n)
  · change (sourceA n).coeff (sourceA n).natDegree = _
    rw [hdegree, hcoeff]

theorem actual_A_ne_zero (n : ℕ) : sourceA n ≠ 0 := by
  apply leadingCoeff_ne_zero.mp
  rw [(actual_A_degree_and_leadingCoeff n).2]
  exact pow_ne_zero _ (by norm_num)

theorem actual_A_without_monomial_ne_zero (n : ℕ) : sourceAWithoutMonomial n ≠ 0 := by
  intro h
  have hz : sourceA n = 0 := by rw [sourceA_factor, h, mul_zero]
  exact actual_A_ne_zero n hz

theorem actual_A_without_monomial_degree (n : ℕ) :
    (sourceAWithoutMonomial n).natDegree = sourceK n - sourceM n := by
  have hd := (actual_A_degree_and_leadingCoeff n).1
  rw [sourceA_factor, natDegree_mul' (by
      simpa only [leadingCoeff_X_pow, one_mul] using
        (leadingCoeff_ne_zero.mpr (actual_A_without_monomial_ne_zero n))),
    natDegree_X_pow] at hd
  omega

/-- Degree of the literal complementary cyclotomic product. -/
theorem sourceComplement_monic_degree (n : ℕ) :
    (sourceComplement n).Monic ∧ (sourceComplement n).natDegree =
      ∑ l ∈ Finset.Icc 1 (15 * n), if sourceWeight n l = 0 then l.totient else 0 := by
  classical
  have hall (s : Finset ℕ) :
      (∏ l ∈ s, if sourceWeight n l = 0 then cyclotomic l ℤ else 1).Monic ∧
      (∏ l ∈ s, if sourceWeight n l = 0 then cyclotomic l ℤ else 1).natDegree =
        ∑ l ∈ s, if sourceWeight n l = 0 then l.totient else 0 := by
    induction s using Finset.induction_on with
    | empty => simp
    | @insert l s hls ih =>
        rw [Finset.prod_insert hls, Finset.sum_insert hls]
        have hm : (if sourceWeight n l = 0 then cyclotomic l ℤ else (1 : ℤ[X])).Monic := by
          split_ifs
          · exact cyclotomic.monic l ℤ
          · exact monic_one
        constructor
        · exact hm.mul ih.1
        · rw [natDegree_mul' (by simp [hm.leadingCoeff, ih.1.leadingCoeff]), ih.2]
          split_ifs <;> simp [natDegree_cyclotomic]
  exact hall _

/-- Actual U, not a hypothetical height-cap polynomial, has the printed W. -/
theorem actual_U_degree (n : ℕ) :
    (sourceU n).natDegree = sourceK n - sourceM n +
      ∑ l ∈ Finset.Icc 1 (15 * n), if sourceWeight n l = 0 then l.totient else 0 := by
  obtain ⟨hC, hdC⟩ := sourceComplement_monic_degree n
  unfold sourceU
  rw [natDegree_mul' (by
    simpa only [hC.leadingCoeff, one_mul] using
      (leadingCoeff_ne_zero.mpr (actual_A_without_monomial_ne_zero n))),
    hdC, actual_A_without_monomial_degree]
  omega

end ErdosProblems.Erdos1049.PaperR12
