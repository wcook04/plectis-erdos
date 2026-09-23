import ErdosProblems.Erdos1049.PaperR20.SourcePadeGenerating
import ErdosProblems.Erdos1049.PaperR20.SourcePadeResidues

/-!
# Finite quotient extracted from the Padé generating identity

The full triangular series is the numerator divided by the finite denominator.
Truncating it through degree `m` therefore agrees with the numerator after
multiplication by the denominator in every degree at most `m`.  This is the
formal-series form of the polynomial-division remainder bound.  The normalized
coefficients below also expose the exact powers needed for the integral
clearing `d=max(m(m-1)/2-1,0)`, including `m=0,1`.
-/

namespace ErdosProblems.Erdos1049.PaperR20

open Finset Polynomial
open scoped BigOperators
noncomputable section

/-- `d=max(m(m-1)/2-1,0)` in natural-subtraction form. -/
def sourceQuotientClearD (m : ℕ) : ℕ := m * (m - 1) / 2 - 1

/-- `e=max(1-m(m-1)/2,0)` in natural-subtraction form. -/
def sourceQuotientClearE (m : ℕ) : ℕ := 1 - m * (m - 1) / 2

theorem sourceQuotientClearD_sub_E (m : ℕ) :
    sourceQuotientClearD m + 1 =
      m * (m - 1) / 2 + sourceQuotientClearE m := by
  unfold sourceQuotientClearD sourceQuotientClearE
  omega

@[simp] theorem sourceQuotientClearD_zero : sourceQuotientClearD 0 = 0 := by
  rfl

@[simp] theorem sourceQuotientClearD_one : sourceQuotientClearD 1 = 0 := by
  rfl

@[simp] theorem sourceQuotientClearE_zero : sourceQuotientClearE 0 = 1 := by
  rfl

@[simp] theorem sourceQuotientClearE_one : sourceQuotientClearE 1 = 1 := by
  rfl

/-- The forced `p`-power is removed termwise from the triangular coefficient.
Every exponent is a natural number when `k≤l≤m`. -/
def sourceNormalizedTriangularCoeff (m l : ℕ) : PadeParameterPolynomial :=
  ∑ k ∈ range (l + 1),
    (-1 : PadeParameterPolynomial) ^ k *
      X ^ ((m - k + 1).choose 2 - (m - l + 1).choose 2) *
      gaussBinom X m k * gaussBinom X (m + l - k) m

/-- Exact extraction of the common triangular `p`-valuation. -/
theorem sourceTriangularCoeff_eq_X_pow_mul_normalized
    (m l : ℕ) (hl : l ≤ m) :
    sourceTriangularCoeff m l =
      X ^ (m - l + 1).choose 2 * sourceNormalizedTriangularCoeff m l := by
  unfold sourceTriangularCoeff sourceNormalizedTriangularCoeff
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro k hk
  have hkl : k ≤ l := Nat.le_of_lt_succ (Finset.mem_range.mp hk)
  have hindex : m + (l - k) = m + l - k := by omega
  have hchoose : (m - l + 1).choose 2 ≤ (m - k + 1).choose 2 := by
    apply Nat.choose_le_choose 2
    omega
  have hpow :
      (X : PadeParameterPolynomial) ^ (m - l + 1).choose 2 *
          X ^ ((m - k + 1).choose 2 - (m - l + 1).choose 2) =
        X ^ (m - k + 1).choose 2 := by
    rw [← pow_add, Nat.add_sub_of_le hchoose]
  simp only [sourceNumeratorCoeff, sourceReciprocalCoeff, hindex]
  rw [← hpow]
  ring

/-- The integral coefficient of `X^(m-l)` in the cleared quotient `Qbar`.
The exceptional extra power for `m=0,1` is exactly `e`; for `m≥2`, `e=0`. -/
def sourceClearedQuotientCoeff (m l : ℕ) : PadeParameterPolynomial :=
  -(sourceDeltaPoly m ^ 3 *
    X ^ ((l + 1).choose 2 + sourceQuotientClearE m) *
    sourceNormalizedTriangularCoeff m l)

/-- The concrete all-`m` cleared quotient, with coefficients ordered by
descending powers `X^(m-l)` of the kernel variable. -/
noncomputable def sourceClearedQuotientPoly (m : ℕ) : (ℤ[X])[X] :=
  ∑ l ∈ range (m + 1),
    C (sourceClearedQuotientCoeff m l) * X ^ (m - l)

/-- The triangular series truncated exactly through the polynomial quotient
range `0≤l≤m`. -/
def sourceTriangularTruncation (m : ℕ) : PadeGeneratingSeries :=
  PowerSeries.mk fun l => if l ≤ m then sourceTriangularCoeff m l else 0

@[simp] theorem coeff_sourceTriangularTruncation (m l : ℕ) (hl : l ≤ m) :
    PowerSeries.coeff l (sourceTriangularTruncation m) =
      sourceTriangularCoeff m l := by
  simp [sourceTriangularTruncation, hl]

private theorem coeff_mul_eq_of_right_coeff_eq_up_to
    {R : Type*} [CommRing R] (A B C : PowerSeries R) (m l : ℕ) (hl : l ≤ m)
    (hcoeff : ∀ n, n ≤ m → PowerSeries.coeff n B = PowerSeries.coeff n C) :
    PowerSeries.coeff l (A * B) = PowerSeries.coeff l (A * C) := by
  rw [PowerSeries.coeff_mul, PowerSeries.coeff_mul]
  apply Finset.sum_congr rfl
  intro ij hij
  have hadd : ij.1 + ij.2 = l := Finset.mem_antidiagonal.mp hij
  rw [hcoeff ij.2 (by omega)]

/-- Multiplying the truncated quotient series by the literal denominator
matches the literal numerator in every degree at most `m`.  Equivalently, the
residual starts in degree `m+1`; after reversal this is the desired polynomial
remainder degree bound `<m+1`. -/
theorem source_truncated_generating_remainder_coeff_zero
    (m l : ℕ) (hl : l ≤ m) :
    PowerSeries.coeff l
        (sourceNumeratorSeries m -
          sourceDenominatorSeries m * sourceTriangularTruncation m) = 0 := by
  have htrunc : ∀ n, n ≤ m →
      PowerSeries.coeff n (sourceTriangularTruncation m) =
        PowerSeries.coeff n
          (sourceNumeratorSeries m * sourceReciprocalSeries m) := by
    intro n hn
    rw [coeff_sourceTriangularTruncation m n hn,
      coeff_sourceNumerator_mul_sourceReciprocalSeries m n hn]
  have hmul := coeff_mul_eq_of_right_coeff_eq_up_to
    (sourceDenominatorSeries m) (sourceTriangularTruncation m)
    (sourceNumeratorSeries m * sourceReciprocalSeries m) m l hl htrunc
  rw [sourceTriangular_generating_identity] at hmul
  simpa only [map_sub, sub_eq_zero] using hmul.symm

/-! ## Reversal at infinity

The polynomial quotient is read from the expansion at infinity.  After putting
`z = x⁻¹`, its numerator is `∏_{a=1}^m (1-p^a z)` and its denominator is
`∏_{j=0}^m (1-p^(m+1+j) z)`.  The latter is obtained from the already proved
denominator identity by rescaling the series variable by `p^(m+1)`.
-/

/-- Coefficient of `z^k` in `∏_{a=1}^m (1-p^a z)`. -/
def sourceInfinityNumeratorCoeff (m k : ℕ) : PadeParameterPolynomial :=
  (-1 : PadeParameterPolynomial) ^ k *
    X ^ (k + 1).choose 2 * gaussBinom X m k

/-- The reversed numerator series at infinity. -/
def sourceInfinityNumeratorSeries (m : ℕ) : PadeGeneratingSeries :=
  PowerSeries.mk fun k => if k ≤ m then sourceInfinityNumeratorCoeff m k else 0

theorem sourceInfinityNumeratorCoeff_zero_succ (m : ℕ) :
    sourceInfinityNumeratorCoeff (m + 1) 0 =
      sourceInfinityNumeratorCoeff m 0 := by
  simp [sourceInfinityNumeratorCoeff, gaussBinom_zero_right]

/-- Coefficient recursion induced by appending `1-p^(m+1)z`. -/
theorem sourceInfinityNumeratorCoeff_succ (m k : ℕ) (hk : k ≤ m) :
    sourceInfinityNumeratorCoeff (m + 1) (k + 1) =
      sourceInfinityNumeratorCoeff m (k + 1) -
        X ^ (m + 1) * sourceInfinityNumeratorCoeff m k := by
  by_cases hkm : k = m
  · subst k
    simp only [sourceInfinityNumeratorCoeff, gaussBinom_self,
      gaussBinom_eq_zero_of_lt (X : PadeParameterPolynomial) (by omega : m < m + 1), mul_zero, zero_sub, mul_one]
    rw [choose_two_succ (m + 1)]
    simp only [pow_add, pow_one]
    ring
  have hlt : k < m := lt_of_le_of_ne hk hkm
  have hrec := gaussBinom_succ_of_le (X : PadeParameterPolynomial) hk
  have hexponent :
      (k + 1).choose 2 + (m + 1) =
        (k + 2).choose 2 + (m - k) := by
    have h : (k + 2).choose 2 = (k + 1).choose 2 + (k + 1) := by
      simpa only [Nat.add_assoc] using choose_two_succ (k + 1)
    omega
  have hpower :
      (X : PadeParameterPolynomial) ^ (k + 2).choose 2 * X ^ (m - k) =
        X ^ (m + 1) * X ^ (k + 1).choose 2 := by
    rw [← pow_add, ← pow_add]
    congr 1
    omega
  unfold sourceInfinityNumeratorCoeff
  rw [hrec]
  calc
    _ = (-1 : PadeParameterPolynomial) ^ (k + 1) *
          X ^ (k + 2).choose 2 * gaussBinom X m (k + 1) +
        (-1 : PadeParameterPolynomial) ^ (k + 1) *
          (X ^ (k + 2).choose 2 * X ^ (m - k)) * gaussBinom X m k := by
      ring
    _ = (-1 : PadeParameterPolynomial) ^ (k + 1) *
          X ^ (k + 2).choose 2 * gaussBinom X m (k + 1) +
        (-1 : PadeParameterPolynomial) ^ (k + 1) *
          (X ^ (m + 1) * X ^ (k + 1).choose 2) * gaussBinom X m k := by
      rw [hpower]
    _ = _ := by rw [pow_succ]; ring

/-- The reversed numerator is the literal finite product. -/
theorem sourceInfinityNumeratorSeries_eq_prod (m : ℕ) :
    sourceInfinityNumeratorSeries m =
      ∏ j ∈ range m,
        (1 - PowerSeries.C ((X : PadeParameterPolynomial) ^ (j + 1)) *
          PowerSeries.X) := by
  induction m with
  | zero =>
      ext (_ | k) : 1 <;>
        simp [sourceInfinityNumeratorSeries, sourceInfinityNumeratorCoeff]
  | succ m ih =>
      rw [Finset.prod_range_succ, ← ih]
      ext (_ | k) : 1
      · simp [sourceInfinityNumeratorSeries, sourceInfinityNumeratorCoeff_zero_succ]
      · rw [mul_sub, mul_one, ← mul_assoc]
        simp only [map_sub,
          PowerSeries.coeff_succ_mul_X, PowerSeries.coeff_mul_C]
        by_cases hk : k ≤ m
        · have hks : k + 1 ≤ m + 1 := Nat.succ_le_succ hk
          simp only [sourceInfinityNumeratorSeries, PowerSeries.coeff_mk, if_pos hks, if_pos hk]
          rw [sourceInfinityNumeratorCoeff_succ m k hk]
          by_cases hkm : k < m
          · simp [Nat.succ_le_iff, hkm, mul_comm]
          · have heq : k = m := by omega
            subst k
            simp [sourceInfinityNumeratorCoeff, gaussBinom_eq_zero_of_lt, mul_comm]
        · have hks : ¬k + 1 ≤ m + 1 := by omega
          simp [sourceInfinityNumeratorSeries, hks, hk, show ¬ k < m by omega]

/-- Denominator at infinity, obtained by the variable rescaling
`z ↦ p^(m+1)z`. -/
noncomputable def sourceInfinityDenominatorSeries (m : ℕ) : PadeGeneratingSeries :=
  PowerSeries.rescale ((X : PadeParameterPolynomial) ^ (m + 1))
    (sourceDenominatorSeries m)

/-- Reciprocal denominator at infinity, with coefficient
`p^((m+1)r)[m+r choose m]_p`. -/
noncomputable def sourceInfinityReciprocalSeries (m : ℕ) : PadeGeneratingSeries :=
  PowerSeries.rescale ((X : PadeParameterPolynomial) ^ (m + 1))
    (sourceReciprocalSeries m)

@[simp] theorem coeff_sourceInfinityReciprocalSeries (m r : ℕ) :
    PowerSeries.coeff r (sourceInfinityReciprocalSeries m) =
      X ^ ((m + 1) * r) * sourceReciprocalCoeff m r := by
  simp [sourceInfinityReciprocalSeries, pow_mul, sourceReciprocalSeries]

theorem sourceInfinityDenominator_mul_reciprocal (m : ℕ) :
    sourceInfinityDenominatorSeries m * sourceInfinityReciprocalSeries m = 1 := by
  change PowerSeries.rescale (X ^ (m + 1)) (sourceDenominatorSeries m) *
      PowerSeries.rescale (X ^ (m + 1)) (sourceReciprocalSeries m) = 1
  rw [← map_mul, sourceDenominator_mul_sourceReciprocalSeries, map_one]

/-- Coefficient of the reversed quotient expansion at infinity. -/
def sourceInfinityTriangularCoeff (m l : ℕ) : PadeParameterPolynomial :=
  ∑ k ∈ range (l + 1),
    sourceInfinityNumeratorCoeff m k *
      (X ^ ((m + 1) * (l - k)) * sourceReciprocalCoeff m (l - k))

/-- The reversed convolution is exactly the normalized triangular coefficient
used in `sourceClearedQuotientPoly`. -/
theorem sourceInfinityTriangularCoeff_eq_normalized
    (m l : ℕ) (hl : l ≤ m) :
    sourceInfinityTriangularCoeff m l =
      X ^ (l + 1).choose 2 * sourceNormalizedTriangularCoeff m l := by
  unfold sourceInfinityTriangularCoeff sourceNormalizedTriangularCoeff
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro k hk
  have hkl : k ≤ l := Nat.le_of_lt_succ (Finset.mem_range.mp hk)
  have hkm : k ≤ m := hkl.trans hl
  have hchoose : (m - l + 1).choose 2 ≤ (m - k + 1).choose 2 := by
    apply Nat.choose_le_choose 2
    omega
  have hmk : m - k + 1 = (m - l + 1) + (l - k) := by omega
  have hlk : l + 1 = (k + 1) + (l - k) := by omega
  have hk2 := PaperR12.twice_choose_two_nat (k + 1)
  have hl2 := PaperR12.twice_choose_two_nat (l + 1)
  have hmk2 := PaperR12.twice_choose_two_nat (m - k + 1)
  have hml2 := PaperR12.twice_choose_two_nat (m - l + 1)
  have hsum :
      (k + 1).choose 2 + (m + 1) * (l - k) +
          (m - l + 1).choose 2 =
        (l + 1).choose 2 + (m - k + 1).choose 2 := by
    have hml : m - l + l = m := Nat.sub_add_cancel hl
    have hlk' : l - k + k = l := Nat.sub_add_cancel hkl
    have hmk' : m - k + k = m := Nat.sub_add_cancel hkm
    rw [hmk] at hmk2
    rw [hlk] at hl2
    rw [show m + 1 = (m - l + 1) + (l - k) + k by omega, hlk, hmk]
    nlinarith only [hk2, hl2, hmk2, hml2]
  have hexponent :
      (k + 1).choose 2 + (m + 1) * (l - k) =
        (l + 1).choose 2 +
          ((m - k + 1).choose 2 - (m - l + 1).choose 2) := by
    omega
  simp only [sourceInfinityNumeratorCoeff, sourceReciprocalCoeff]
  have hpow :
      (X : PadeParameterPolynomial) ^ (k + 1).choose 2 *
          X ^ ((m + 1) * (l - k)) =
        X ^ (l + 1).choose 2 *
          X ^ ((m - k + 1).choose 2 - (m - l + 1).choose 2) := by
    rw [← pow_add, ← pow_add, hexponent]
  have hindex : m + (l - k) = m + l - k := by omega
  rw [hindex]
  linear_combination (-1 : PadeParameterPolynomial)^k * gaussBinom X m k * gaussBinom X (m+l-k) m * hpow

/-- Coefficient extraction from the full reversed numerator/reciprocal
product. -/
theorem coeff_sourceInfinityNumerator_mul_reciprocal
    (m l : ℕ) (hl : l ≤ m) :
    PowerSeries.coeff l
        (sourceInfinityNumeratorSeries m * sourceInfinityReciprocalSeries m) =
      sourceInfinityTriangularCoeff m l := by
  rw [PowerSeries.coeff_mul,
    Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  unfold sourceInfinityNumeratorSeries sourceInfinityTriangularCoeff
  apply Finset.sum_congr rfl
  intro k hk
  have hkl : k ≤ l := Nat.le_of_lt_succ (Finset.mem_range.mp hk)
  simp [hkl.trans hl]

/-- Truncation of the concrete reversed quotient through degree `m`. -/
def sourceInfinityTriangularTruncation (m : ℕ) : PadeGeneratingSeries :=
  PowerSeries.mk fun l => if l ≤ m then sourceInfinityTriangularCoeff m l else 0

/-- The finite reversed quotient is exact through order `m`; hence the
unreversed polynomial remainder has outer degree at most `m`. -/
theorem source_infinity_truncated_remainder_coeff_zero
    (m l : ℕ) (hl : l ≤ m) :
    PowerSeries.coeff l
        (sourceInfinityNumeratorSeries m -
          sourceInfinityDenominatorSeries m *
            sourceInfinityTriangularTruncation m) = 0 := by
  have htrunc : ∀ n, n ≤ m →
      PowerSeries.coeff n (sourceInfinityTriangularTruncation m) =
        PowerSeries.coeff n
          (sourceInfinityNumeratorSeries m * sourceInfinityReciprocalSeries m) := by
    intro n hn
    rw [coeff_sourceInfinityNumerator_mul_reciprocal m n hn]
    simp [sourceInfinityTriangularTruncation, hn]
  have hmul := coeff_mul_eq_of_right_coeff_eq_up_to
    (sourceInfinityDenominatorSeries m) (sourceInfinityTriangularTruncation m)
    (sourceInfinityNumeratorSeries m * sourceInfinityReciprocalSeries m)
    m l hl htrunc
  rw [mul_left_comm (sourceInfinityDenominatorSeries m), sourceInfinityDenominator_mul_reciprocal, mul_one] at hmul
  simpa only [map_sub, sub_eq_zero] using hmul.symm

theorem sourceInfinityDenominatorSeries_eq_prod (m : ℕ) :
    sourceInfinityDenominatorSeries m =
      ∏ j ∈ range (m + 1),
        (1 - PowerSeries.C ((X : PadeParameterPolynomial) ^ (m + 1 + j)) *
          PowerSeries.X) := by
  rw [sourceInfinityDenominatorSeries, sourceDenominatorSeries_eq_prod, map_prod]
  apply Finset.prod_congr rfl
  intro j hj
  have hC (r : PadeParameterPolynomial) :
      PowerSeries.rescale ((X : PadeParameterPolynomial) ^ (m + 1))
          (PowerSeries.C r) = PowerSeries.C r := by
    ext n : 1
    cases n <;> simp [PowerSeries.coeff_rescale]
  simp only [map_sub, map_one, map_mul, hC, PowerSeries.rescale_X]
  rw [← mul_assoc, ← map_mul, ← pow_add]
  simp only [Nat.add_comm]

/-- Finite polynomial forms of the three reversed series. -/
noncomputable def sourceInfinityNumeratorPoly (m : ℕ) : (ℤ[X])[X] :=
  ∏ j ∈ range m, (1 - C ((X : ℤ[X]) ^ (j + 1)) * X)

noncomputable def sourceInfinityDenominatorPoly (m : ℕ) : (ℤ[X])[X] :=
  ∏ j ∈ range (m + 1), (1 - C ((X : ℤ[X]) ^ (m + 1 + j)) * X)

noncomputable def sourceInfinityQuotientPoly (m : ℕ) : (ℤ[X])[X] :=
  ∑ l ∈ range (m + 1), C (sourceInfinityTriangularCoeff m l) * X ^ l

theorem sourceInfinityNumeratorPoly_toPowerSeries (m : ℕ) :
    (sourceInfinityNumeratorPoly m : PadeGeneratingSeries) =
      sourceInfinityNumeratorSeries m := by
  rw [sourceInfinityNumeratorSeries_eq_prod]
  unfold sourceInfinityNumeratorPoly
  rw [← Polynomial.coeToPowerSeries.ringHom_apply, map_prod]
  simp only [Polynomial.coeToPowerSeries.ringHom_apply, Polynomial.coe_sub, Polynomial.coe_one, Polynomial.coe_mul, Polynomial.coe_C, Polynomial.coe_X]

theorem sourceInfinityDenominatorPoly_toPowerSeries (m : ℕ) :
    (sourceInfinityDenominatorPoly m : PadeGeneratingSeries) =
      sourceInfinityDenominatorSeries m := by
  rw [sourceInfinityDenominatorSeries_eq_prod]
  unfold sourceInfinityDenominatorPoly
  rw [← Polynomial.coeToPowerSeries.ringHom_apply, map_prod]
  simp only [Polynomial.coeToPowerSeries.ringHom_apply, Polynomial.coe_sub, Polynomial.coe_one, Polynomial.coe_mul, Polynomial.coe_C, Polynomial.coe_X]

theorem sourceInfinityQuotientPoly_toPowerSeries (m : ℕ) :
    (sourceInfinityQuotientPoly m : PadeGeneratingSeries) =
      sourceInfinityTriangularTruncation m := by
  ext l
  by_cases hl : l ≤ m
  · simp [sourceInfinityQuotientPoly, sourceInfinityTriangularTruncation,
      hl, Finset.mem_range]
  · simp [sourceInfinityQuotientPoly, sourceInfinityTriangularTruncation,
      hl, Finset.mem_range]

/-- **Finite generating-function truncation.**  The reversed residual has a
zero of order at least `m+1`.  Since all three series in the residual are
finite through the relevant quotient range, reversing this statement is the
outer polynomial remainder bound `≤m`. -/
theorem source_infinity_remainder_X_pow_dvd (m : ℕ) :
    PowerSeries.X ^ (m + 1) ∣
      sourceInfinityNumeratorSeries m -
        sourceInfinityDenominatorSeries m *
          sourceInfinityTriangularTruncation m := by
  rw [PowerSeries.X_pow_dvd_iff]
  intro l hl
  exact source_infinity_truncated_remainder_coeff_zero m l (by omega)

/-- Polynomial version of the finite truncation.  This is the direct input to
the final `reflect` step that turns an order-`m+1` zero at the origin into an
outer remainder degree bound `≤m`. -/
theorem source_infinity_polynomial_remainder_X_pow_dvd (m : ℕ) :
    (X : (ℤ[X])[X]) ^ (m + 1) ∣
      sourceInfinityNumeratorPoly m -
        sourceInfinityDenominatorPoly m * sourceInfinityQuotientPoly m := by
  rw [Polynomial.X_pow_dvd_iff]
  intro l hl
  have hzero := source_infinity_truncated_remainder_coeff_zero m l (by omega)
  rw [← sourceInfinityNumeratorPoly_toPowerSeries,
    ← sourceInfinityDenominatorPoly_toPowerSeries,
    ← sourceInfinityQuotientPoly_toPowerSeries] at hzero
  simpa only [← Polynomial.coe_mul, ← Polynomial.coe_sub, Polynomial.coeff_coe] using hzero

/-- The displayed integral quotient coefficient is exactly the reversed
generating coefficient, multiplied by the numerator's clearing factor. -/
theorem sourceClearedQuotientCoeff_eq_infinity
    (m l : ℕ) (hl : l ≤ m) :
    sourceClearedQuotientCoeff m l =
      -(sourceDeltaPoly m ^ 3 * X ^ sourceQuotientClearE m *
        sourceInfinityTriangularCoeff m l) := by
  rw [sourceInfinityTriangularCoeff_eq_normalized m l hl]
  unfold sourceClearedQuotientCoeff
  ring

/-- Concrete reversal formula for the bivariate quotient used by the finite
remainder consumer.  The outer exponent `m-l` is the reversal of the
generating index `l`; the inner scalar is exactly the integral clearing
factor, including the exceptional `e` at `m=0,1`. -/
theorem sourceClearedQuotientPoly_eq_reversed (m : ℕ) :
    sourceClearedQuotientPoly m =
      C (-(sourceDeltaPoly m ^ 3 * X ^ sourceQuotientClearE m)) *
        ∑ l ∈ range (m + 1),
          C (sourceInfinityTriangularCoeff m l) * X ^ (m - l) := by
  rw [sourceClearedQuotientPoly, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro l hl
  rw [sourceClearedQuotientCoeff_eq_infinity m l
    (Nat.le_of_lt_succ (Finset.mem_range.mp hl))]
  simp only [map_neg, map_mul]
  ring

#print axioms sourceTriangularCoeff_eq_X_pow_mul_normalized
#print axioms source_truncated_generating_remainder_coeff_zero
#print axioms sourceInfinityNumeratorSeries_eq_prod
#print axioms sourceInfinityTriangularCoeff_eq_normalized
#print axioms source_infinity_truncated_remainder_coeff_zero
#print axioms source_infinity_remainder_X_pow_dvd
#print axioms source_infinity_polynomial_remainder_X_pow_dvd
#print axioms sourceClearedQuotientCoeff_eq_infinity
#print axioms sourceClearedQuotientPoly_eq_reversed

end
end ErdosProblems.Erdos1049.PaperR20
