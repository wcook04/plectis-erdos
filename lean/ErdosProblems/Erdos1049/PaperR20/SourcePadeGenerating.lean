import ErdosProblems.Erdos1049.GaussianDegreeR12
import Mathlib.RingTheory.PowerSeries.Basic

/-!
# The finite generating function behind the 2016 Padé quotient

The reciprocal of `∏_{j=0}^m (1-p^j z)` has coefficient
`[m+r choose m]_p`.  This file proves that assertion as an identity of formal
power series over `ℤ[p]`, directly from the recurrence-defined Gaussian
binomial.  Convolution with the explicit numerator coefficients then gives
the triangular coefficient `S_(m,l)` used in the polynomial quotient.
-/

namespace ErdosProblems.Erdos1049.PaperR20

open Finset Polynomial
open scoped BigOperators

abbrev PadeParameterPolynomial := ℤ[X]
abbrev PadeGeneratingSeries := PowerSeries PadeParameterPolynomial

noncomputable section

/-- The coefficient `[m+r choose m]_p` of the reciprocal denominator. -/
def sourceReciprocalCoeff (m r : ℕ) : PadeParameterPolynomial :=
  gaussBinom (X : PadeParameterPolynomial) (m + r) m

/-- The reciprocal-denominator series with Gaussian coefficients. -/
def sourceReciprocalSeries (m : ℕ) : PadeGeneratingSeries :=
  PowerSeries.mk (sourceReciprocalCoeff m)

/-- The literal denominator `∏_{j=0}^m (1-p^j z)`, recursively ordered. -/
def sourceDenominatorSeries : ℕ → PadeGeneratingSeries
  | 0 => 1 - PowerSeries.X
  | m + 1 => sourceDenominatorSeries m *
      (1 - PowerSeries.C ((X : PadeParameterPolynomial) ^ (m + 1)) *
        PowerSeries.X)

/-- The recursive denominator is the literal product
`∏_{j=0}^m(1-p^j z)`. -/
theorem sourceDenominatorSeries_eq_prod (m : ℕ) :
    sourceDenominatorSeries m =
      ∏ j ∈ range (m + 1),
        (1 - PowerSeries.C ((X : PadeParameterPolynomial) ^ j) *
          PowerSeries.X) := by
  induction m with
  | zero => simp [sourceDenominatorSeries]
  | succ m ih =>
      simp [sourceDenominatorSeries, ih, Finset.prod_range_succ, mul_assoc]

/-- The second Pascal recurrence, obtained from the existing Gaussian
symmetry theorem and the defining first Pascal recurrence. -/
theorem sourceReciprocalCoeff_succ (m r : ℕ) :
    sourceReciprocalCoeff (m + 1) (r + 1) =
      sourceReciprocalCoeff m (r + 1) +
        (X : PadeParameterPolynomial) ^ (m + 1) *
          sourceReciprocalCoeff (m + 1) r := by
  have hleft :
      gaussBinom (X : PadeParameterPolynomial) (m + r + 2) (m + 1) =
        gaussBinom X (m + r + 2) (r + 1) := by
    simpa only [show m + r + 2 - (m + 1) = r + 1 by omega] using
      PaperR12.gaussian_polynomial_symmetry (m + r + 2) (m + 1) (by omega)
  have hfirst :
      gaussBinom (X : PadeParameterPolynomial) (m + r + 1) (r + 1) =
        gaussBinom X (m + r + 1) m := by
    simpa only [show m + r + 1 - (r + 1) = m by omega] using
      PaperR12.gaussian_polynomial_symmetry (m + r + 1) (r + 1) (by omega)
  have hsecond :
      gaussBinom (X : PadeParameterPolynomial) (m + r + 1) r =
        gaussBinom X (m + r + 1) (m + 1) := by
    simpa only [show m + r + 1 - r = m + 1 by omega] using
      PaperR12.gaussian_polynomial_symmetry (m + r + 1) r (by omega)
  unfold sourceReciprocalCoeff
  rw [show m + 1 + (r + 1) = m + r + 2 by omega, hleft]
  rw [show m + r + 2 = (m + r + 1) + 1 by omega,
    show r + 1 = r + 1 by rfl,
    gaussBinom_succ_of_le (X : PadeParameterPolynomial) (show r ≤ m + r + 1 by omega)]
  rw [hfirst, hsecond]
  rw [show m + r + 1 - r = m + 1 by omega]
  simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm]

@[simp] theorem sourceReciprocalCoeff_zero (r : ℕ) :
    sourceReciprocalCoeff 0 r = 1 := by
  simp [sourceReciprocalCoeff]

/-- Multiplying by the newest denominator factor lowers `m` by one. -/
theorem denominatorFactor_mul_sourceReciprocalSeries (m : ℕ) :
    (1 - PowerSeries.C ((X : PadeParameterPolynomial) ^ (m + 1)) *
        PowerSeries.X) * sourceReciprocalSeries (m + 1) =
      sourceReciprocalSeries m := by
  apply PowerSeries.ext
  intro n
  cases n with
  | zero => simp [sourceReciprocalSeries, sourceReciprocalCoeff, gaussBinom_self]
  | succ r =>
      rw [sub_mul, one_mul, mul_assoc]
      simp only [sourceReciprocalSeries, map_sub, PowerSeries.coeff_mk, PowerSeries.coeff_C_mul,
        PowerSeries.coeff_succ_X_mul]
      change sourceReciprocalCoeff (m + 1) (r + 1) -
        X ^ (m + 1) * sourceReciprocalCoeff (m + 1) r =
          sourceReciprocalCoeff m (r + 1)
      rw [sourceReciprocalCoeff_succ]
      ring

/-- The `m=0` geometric series is inverse to `1-z`. -/
theorem denominator_zero_mul_sourceReciprocalSeries :
    sourceDenominatorSeries 0 * sourceReciprocalSeries 0 = 1 := by
  ext (_ | r)
  · simp [sourceDenominatorSeries, sourceReciprocalSeries]
  · rw [sourceDenominatorSeries, sub_mul, one_mul]
    simp [sourceReciprocalSeries]

/-- Exact reciprocal-product identity
`∏_{j=0}^m(1-p^j z) * Σ_r [m+r choose m]_p z^r = 1`. -/
theorem sourceDenominator_mul_sourceReciprocalSeries (m : ℕ) :
    sourceDenominatorSeries m * sourceReciprocalSeries m = 1 := by
  induction m with
  | zero => exact denominator_zero_mul_sourceReciprocalSeries
  | succ m ih =>
      rw [sourceDenominatorSeries, mul_assoc,
        denominatorFactor_mul_sourceReciprocalSeries, ih]

/-- The Gaussian recurrence in the orientation needed when a new numerator
factor `p^(m+1)-z` is appended. -/
theorem gaussBinom_succ_alt (m k : ℕ) (hk : k ≤ m) :
    gaussBinom (X : PadeParameterPolynomial) (m + 1) (k + 1) =
      X ^ (k + 1) * gaussBinom X m (k + 1) + gaussBinom X m k := by
  by_cases hkm : k = m
  · subst k
    simp [gaussBinom_self, gaussBinom_eq_zero_of_lt]
  · have hlt : k < m := lt_of_le_of_ne hk hkm
    have hleft := PaperR12.gaussian_polynomial_symmetry (m + 1) (k + 1) (by omega)
    have hfirst := PaperR12.gaussian_polynomial_symmetry m (m - k) (by omega)
    have hsecond := PaperR12.gaussian_polynomial_symmetry m (m - k - 1) (by omega)
    have hrec := gaussBinom_succ_of_le (X : PadeParameterPolynomial)
        (show m - k - 1 ≤ m by omega)
    rw [show (m - k - 1) + 1 = m - k by omega] at hrec
    rw [show m - (m - k - 1) = k + 1 by omega] at hrec
    rw [show m + 1 - (k + 1) = m - k by omega] at hleft
    rw [show m - (m - k) = k by omega] at hfirst
    rw [show m - (m - k - 1) = k + 1 by omega] at hsecond
    calc
      gaussBinom (X : PadeParameterPolynomial) (m + 1) (k + 1) =
          gaussBinom X (m + 1) (m - k) := hleft
      _ = gaussBinom X m (m - k) +
          X ^ (k + 1) * gaussBinom X m (m - k - 1) := by
        exact hrec
      _ = _ := by rw [hfirst, hsecond]; ring

/-- Coefficient of `z^k` in `∏_{j=1}^m(p^j-z)`.  Only the range `k≤m`
is used below, so every displayed natural subtraction is exact. -/
def sourceNumeratorCoeff (m k : ℕ) : PadeParameterPolynomial :=
  (-1 : PadeParameterPolynomial) ^ k *
    X ^ (m - k + 1).choose 2 * gaussBinom X m k

theorem sourceNumeratorCoeff_zero_succ (m : ℕ) :
    sourceNumeratorCoeff (m + 1) 0 =
      X ^ (m + 1) * sourceNumeratorCoeff m 0 := by
  unfold sourceNumeratorCoeff
  rw [show m + 1 - 0 + 1 = (m + 1) + 1 by omega,
    show m - 0 + 1 = m + 1 by omega, choose_two_succ, pow_add]
  simp [gaussBinom_zero_right]
  ring

/-- Coefficient recursion induced by multiplying by `p^(m+1)-z`. -/
theorem sourceNumeratorCoeff_succ (m k : ℕ) (hk : k ≤ m) :
    sourceNumeratorCoeff (m + 1) (k + 1) =
      X ^ (m + 1) * sourceNumeratorCoeff m (k + 1) -
        sourceNumeratorCoeff m k := by
  by_cases hkm : k = m
  · subst k
    simp [sourceNumeratorCoeff, gaussBinom_self, gaussBinom_eq_zero_of_lt,
      pow_succ]
  have hlt : k < m := lt_of_le_of_ne hk hkm
  have hsub1 : m + 1 - (k + 1) = m - k := by omega
  have hsub2 : m - (k + 1) + 1 = m - k := by omega
  have hchoose := choose_two_succ (m - k)
  have hexponent :
      m + 1 + (m - k).choose 2 = (m - k + 1).choose 2 + (k + 1) := by
    omega
  have hpower :
      (X : PadeParameterPolynomial) ^ (m - k + 1).choose 2 * X ^ (k + 1) =
        X ^ (m + 1) * X ^ (m - k).choose 2 := by
    rw [← pow_add, ← pow_add, ← hexponent]
  unfold sourceNumeratorCoeff
  rw [hsub1, hsub2, gaussBinom_succ_alt m k hk]
  calc
    _ = (-1 : PadeParameterPolynomial) ^ (k + 1) *
          (X ^ (m - k + 1).choose 2 * X ^ (k + 1)) *
            gaussBinom X m (k + 1) +
        (-1 : PadeParameterPolynomial) ^ (k + 1) *
          X ^ (m - k + 1).choose 2 * gaussBinom X m k := by ring
    _ = (-1 : PadeParameterPolynomial) ^ (k + 1) *
          (X ^ (m + 1) * X ^ (m - k).choose 2) *
            gaussBinom X m (k + 1) +
        (-1 : PadeParameterPolynomial) ^ (k + 1) *
          X ^ (m - k + 1).choose 2 * gaussBinom X m k := by rw [hpower]
    _ = _ := by rw [pow_succ]; ring

/-- The finite numerator series, defined from its exact finite coefficients. -/
def sourceNumeratorSeries (m : ℕ) : PadeGeneratingSeries :=
  PowerSeries.mk fun k => if k ≤ m then sourceNumeratorCoeff m k else 0

/-- Appending the next literal factor gives exactly the coefficient recursion
above. -/
theorem sourceNumeratorSeries_succ (m : ℕ) :
    sourceNumeratorSeries (m + 1) = sourceNumeratorSeries m *
      (PowerSeries.C ((X : PadeParameterPolynomial) ^ (m + 1)) -
        PowerSeries.X) := by
  apply PowerSeries.ext
  intro n
  cases n with
  | zero =>
      simp [sourceNumeratorSeries]
      rw [sourceNumeratorCoeff_zero_succ]
      ring
  | succ k =>
      rw [mul_sub]
      simp only [map_sub, PowerSeries.coeff_mk, PowerSeries.coeff_mul_C,
        PowerSeries.coeff_succ_mul_X]
      by_cases hk : k ≤ m
      · have hks : k + 1 ≤ m + 1 := Nat.succ_le_succ hk
        by_cases hkm : k < m
        · have hksm : k + 1 ≤ m := Nat.succ_le_iff.mpr hkm
          simp [sourceNumeratorSeries, hks, hksm, hk, hkm,
            sourceNumeratorCoeff_succ m k hk]
          ring
        · have hkeq : k = m := Nat.le_antisymm hk (Nat.le_of_not_gt hkm)
          subst k
          have hzero : sourceNumeratorCoeff m (m + 1) = 0 := by
            unfold sourceNumeratorCoeff
            rw [gaussBinom_eq_zero_of_lt (X : PadeParameterPolynomial)
              (show m < m + 1 by omega)]
            ring
          simp [sourceNumeratorSeries, sourceNumeratorCoeff_succ, hzero]
      · have hks : ¬k + 1 ≤ m + 1 := by omega
        have hkm : ¬ k < m := fun h => hk h.le
        simp [sourceNumeratorSeries, hks, hk, hkm]

/-- The coefficient-defined numerator is the literal finite product
`∏_{j=1}^m(p^j-z)`. -/
theorem sourceNumeratorSeries_eq_prod (m : ℕ) :
    sourceNumeratorSeries m =
      ∏ j ∈ range m,
        (PowerSeries.C ((X : PadeParameterPolynomial) ^ (j + 1)) -
          PowerSeries.X) := by
  induction m with
  | zero =>
      ext (_ | k) <;> simp [sourceNumeratorSeries, sourceNumeratorCoeff]
  | succ m ih =>
      rw [sourceNumeratorSeries_succ, ih, Finset.prod_range_succ]

/-- The triangular convolution appearing in the source quotient. -/
def sourceTriangularCoeff (m l : ℕ) : PadeParameterPolynomial :=
  ∑ k ∈ range (l + 1),
    sourceNumeratorCoeff m k * sourceReciprocalCoeff m (l - k)

/-- The coefficient of the numerator times the reciprocal denominator is the
literal triangular Gaussian convolution `S_(m,l)`. -/
theorem coeff_sourceNumerator_mul_sourceReciprocalSeries
    (m l : ℕ) (hl : l ≤ m) :
    PowerSeries.coeff l
        (sourceNumeratorSeries m * sourceReciprocalSeries m) =
      sourceTriangularCoeff m l := by
  rw [PowerSeries.coeff_mul,
    Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  unfold sourceNumeratorSeries sourceReciprocalSeries sourceTriangularCoeff
  apply Finset.sum_congr rfl
  intro k hk
  have hkl : k ≤ l := Nat.le_of_lt_succ (Finset.mem_range.mp hk)
  simp [sourceNumeratorCoeff, hkl.trans hl]

/-- Formal generating identity for the triangular quotient coefficients. -/
theorem sourceTriangular_generating_identity (m : ℕ) :
    sourceDenominatorSeries m *
        (sourceNumeratorSeries m * sourceReciprocalSeries m) =
      sourceNumeratorSeries m := by
  calc
    _ = sourceNumeratorSeries m *
        (sourceDenominatorSeries m * sourceReciprocalSeries m) := by ring
    _ = _ := by rw [sourceDenominator_mul_sourceReciprocalSeries, mul_one]

/-- The same generating identity with both finite products displayed
literally. -/
theorem sourceTriangular_literal_generating_identity (m : ℕ) :
    (∏ j ∈ range (m + 1),
        (1 - PowerSeries.C ((X : PadeParameterPolynomial) ^ j) *
          PowerSeries.X)) *
        (sourceNumeratorSeries m * sourceReciprocalSeries m) =
      ∏ j ∈ range m,
        (PowerSeries.C ((X : PadeParameterPolynomial) ^ (j + 1)) -
          PowerSeries.X) := by
  rw [← sourceDenominatorSeries_eq_prod,
    ← sourceNumeratorSeries_eq_prod, sourceTriangular_generating_identity]

#print axioms sourceReciprocalCoeff_succ
#print axioms sourceDenominator_mul_sourceReciprocalSeries
#print axioms sourceNumeratorSeries_eq_prod
#print axioms coeff_sourceNumerator_mul_sourceReciprocalSeries
#print axioms sourceTriangular_generating_identity
#print axioms sourceTriangular_literal_generating_identity

end

end ErdosProblems.Erdos1049.PaperR20
