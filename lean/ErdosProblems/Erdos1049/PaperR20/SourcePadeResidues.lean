import ErdosProblems.Erdos1049.PaperR20.CoefficientPencil

/-!
# Integer polynomial residues of the coefficient-moment kernel

The explicit finite products expose every denominator factor in the residue
correction. Gaussian-binomial factorial identities identify their sum with
the literal paper coefficient `coefficientAlphaPoly`. No partial-fraction
identity or analytic remainder theorem is assumed here.
-/

namespace ErdosProblems.Erdos1049.PaperR20
open Polynomial Finset
open scoped BigOperators
noncomputable section

/-- The product of `X^a - 1` for `1 ≤ a ≤ m`. -/
def sourceDeltaPoly (m : ℕ) : ℤ[X] :=
  ∏ j ∈ range m, (X ^ (j + 1) - 1)

/-- The consecutive product with exponents `a+1` through `a+n`. -/
def sourceDeltaSegmentPoly (a n : ℕ) : ℤ[X] :=
  ∏ j ∈ range n, (X ^ (a + j + 1) - 1)

theorem sourceDeltaSegment_eq_signed_pochhammer (a n : ℕ) :
    sourceDeltaSegmentPoly a n =
      (-1 : ℤ[X]) ^ n * qPochhammer X (X ^ (a + 1)) n := by
  induction n with
  | zero => simp [sourceDeltaSegmentPoly]
  | succ n ih =>
    have hrec : sourceDeltaSegmentPoly a (n + 1) =
        sourceDeltaSegmentPoly a n * (X ^ (a + n + 1) - 1) := by
      simp only [sourceDeltaSegmentPoly, prod_range_succ]
    rw [hrec, ih, pow_succ (-1 : ℤ[X]) n, qPochhammer_succ]
    have hpow : (X : ℤ[X]) ^ (a + 1) * X ^ n = X ^ (a + n + 1) := by
      rw [← pow_add]
      congr 1
      omega
    rw [hpow]
    ring

theorem sourceDelta_eq_signed_pochhammer (m : ℕ) :
    sourceDeltaPoly m = (-1 : ℤ[X]) ^ m * qPochhammer X X m := by
  simpa [sourceDeltaSegmentPoly, sourceDeltaPoly] using
    sourceDeltaSegment_eq_signed_pochhammer 0 m

theorem sourceDelta_add (a n : ℕ) :
    sourceDeltaPoly (a + n) = sourceDeltaPoly a * sourceDeltaSegmentPoly a n := by
  simp only [sourceDeltaPoly, sourceDeltaSegmentPoly, prod_range_add]

theorem gaussBinom_mul_sourceDelta {n k : ℕ} (hk : k ≤ n) :
    gaussBinom (X : ℤ[X]) n k * sourceDeltaPoly k =
      sourceDeltaSegmentPoly (n - k) k := by
  rw [sourceDelta_eq_signed_pochhammer, sourceDeltaSegment_eq_signed_pochhammer]
  calc
    _ = (-1 : ℤ[X]) ^ k *
        (gaussBinom X n k * qPochhammer X X k) := by ring
    _ = _ := by rw [gaussBinom_mul_qPochhammer_X hk]

/-- The two Gaussian factors clear exactly against three factorial products. -/
theorem sourceDelta_cube_mul_gauss {m k : ℕ} (hk : k ≤ m) :
    sourceDeltaPoly m ^ 3 * gaussBinom X m k * gaussBinom X (m + k) k =
      sourceDeltaSegmentPoly k (m - k) ^ 2 *
        sourceDeltaSegmentPoly (m - k) k * sourceDeltaPoly (m + k) := by
  have hsplit : sourceDeltaPoly m =
      sourceDeltaPoly k * sourceDeltaSegmentPoly k (m - k) := by
    simpa only [show k + (m - k) = m by omega] using sourceDelta_add k (m - k)
  have hfirst := gaussBinom_mul_sourceDelta hk
  have hsecond : gaussBinom (X : ℤ[X]) (m + k) k * sourceDeltaPoly k =
      sourceDeltaSegmentPoly m k := by
    simpa using gaussBinom_mul_sourceDelta (n := m + k) (k := k) (by omega)
  calc
    _ = sourceDeltaPoly m * sourceDeltaSegmentPoly k (m - k) ^ 2 *
        (gaussBinom X m k * sourceDeltaPoly k) *
        (gaussBinom X (m + k) k * sourceDeltaPoly k) := by
      rw [hsplit]
      ring
    _ = sourceDeltaPoly m * sourceDeltaSegmentPoly k (m - k) ^ 2 *
        sourceDeltaSegmentPoly (m - k) k * sourceDeltaSegmentPoly m k := by
      rw [hfirst, hsecond]
    _ = _ := by rw [sourceDelta_add]; ring

/-- The fully factored integer residue at the pole indexed by `k`. -/
def sourceResiduePoly (m k : ℕ) : ℤ[X] :=
  C ((-1 : ℤ) ^ (m + k)) * X ^ (m + 1 + k * (k + 1) / 2) *
    sourceDeltaSegmentPoly k (m - k) ^ 2 *
    sourceDeltaSegmentPoly (m - k) k * sourceDeltaPoly (m + k)

theorem sourceResidue_eq_gauss {m k : ℕ} (hk : k ≤ m) :
    sourceResiduePoly m k =
      X ^ (m + 1) * sourceDeltaPoly m ^ 3 *
        (C ((-1 : ℤ) ^ (m + k)) * X ^ (k * (k + 1) / 2) *
          gaussBinom X m k * gaussBinom X (m + k) k) := by
  unfold sourceResiduePoly
  rw [pow_add (X : ℤ[X]) (m + 1) (k * (k + 1) / 2)]
  calc
    _ = C ((-1 : ℤ) ^ (m + k)) * X ^ (m + 1) * X ^ (k * (k + 1) / 2) *
        (sourceDeltaSegmentPoly k (m - k) ^ 2 *
          sourceDeltaSegmentPoly (m - k) k * sourceDeltaPoly (m + k)) := by ring
    _ = _ := by rw [← sourceDelta_cube_mul_gauss hk]; ring

/-- The Gaussian factorial is the ordinary product with `(X-1)^m` removed. -/
theorem sourceDelta_eq_qFactorial (m : ℕ) :
    sourceDeltaPoly m = (X - 1) ^ m * coefficientQFactorialPoly m := by
  unfold sourceDeltaPoly coefficientQFactorialPoly
  calc
    _ = ∏ j ∈ range m, ((X - 1) * ∑ i ∈ range (j + 1), (X : ℤ[X]) ^ i) := by
      apply prod_congr rfl
      intro j _
      rw [mul_comm, geom_sum_mul]
    _ = _ := by rw [prod_mul_distrib]; simp

/-- Every index, with no finite rank bound: the residues sum to literal alpha. -/
theorem sum_sourceResidue_eq_coefficientAlpha (m : ℕ) :
    (∑ k ∈ range (m + 1), sourceResiduePoly m k) = coefficientAlphaPoly m := by
  calc
    _ = ∑ k ∈ range (m + 1),
        X ^ (m + 1) * sourceDeltaPoly m ^ 3 *
          (C ((-1 : ℤ) ^ (m + k)) * X ^ (k * (k + 1) / 2) *
            gaussBinom X m k * gaussBinom X (m + k) k) := by
      apply sum_congr rfl
      intro k hk
      exact sourceResidue_eq_gauss (by have := mem_range.mp hk; omega)
    _ = X ^ (m + 1) * sourceDeltaPoly m ^ 3 * coefficientRPoly m := by
      rw [coefficientRPoly, mul_sum]
    _ = coefficientAlphaPoly m := by
      rw [sourceDelta_eq_qFactorial]
      simp only [coefficientAlphaPoly, coefficientMomentPoly, mul_pow, ← pow_mul]
      rw [Nat.mul_comm m 3, pow_succ]
      ring

/-- Literal finite-index version consumed by the remainder certificate. -/
theorem sum_sourceResidue_fin_eq_coefficientAlpha (m : ℕ) :
    (∑ k : Fin (m + 1), sourceResiduePoly m k.val) = coefficientAlphaPoly m := by
  simpa only [Fin.sum_univ_eq_sum_range] using sum_sourceResidue_eq_coefficientAlpha m

/-- Remove the required denominator from the final Delta factor explicitly. -/
def sourceResidueQuotientPoly (m k n : ℕ) : ℤ[X] :=
  C ((-1 : ℤ) ^ (m + k)) * X ^ (m + 1 + k * (k + 1) / 2) *
    sourceDeltaSegmentPoly k (m - k) ^ 2 * sourceDeltaSegmentPoly (m - k) k *
      ∏ j ∈ (range (m + k)).erase n, (X ^ (j + 1) - 1)

/-- Every denominator of the full residue prefix is cleared, not only the
short source prefix. No assumption `k ≤ m` is needed for this factor identity. -/
theorem sourceResidue_factor (m k n : ℕ) (hn : n < m + k) :
    sourceResiduePoly m k = (X ^ (n + 1) - 1) * sourceResidueQuotientPoly m k n := by
  have hprod := Finset.mul_prod_erase
    (range (m + k)) (fun j => (X : ℤ[X]) ^ (j + 1) - 1) (mem_range.mpr hn)
  unfold sourceResiduePoly sourceResidueQuotientPoly sourceDeltaPoly
  rw [← hprod]
  ring

#print axioms sum_sourceResidue_eq_coefficientAlpha
#print axioms sourceResidue_factor
end
end ErdosProblems.Erdos1049.PaperR20
