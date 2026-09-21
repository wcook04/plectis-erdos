import ErdosProblems.Erdos1049.MahlerTriangularR11
import ErdosProblems.Erdos1049.PaperR16.R15BoundaryWeights

/-!
# Reconciliation of the two supplied finite-row normalisations

Candidate source; new Lean checks UNRUN. The two imported files are reproduced
byte-for-byte from the packet. This module supplies the missing comparison;
it defines no third weight matrix and does not reprove either elimination.
-/

noncomputable section
open scoped BigOperators
open Polynomial

namespace ErdosProblems.Erdos1049.PaperR16

open ErdosProblems.Erdos1049.PaperR11
open Rolling1049.Remaining.R15BoundaryWeights

variable {K : Type*} [Field K]

/-- R15 row `s`, multiplied by `k^s`, is exactly the R11 row. -/
theorem boundaryWeight_scale (k : K) (hk : k ≠ 0) (s i : ℕ) :
    k ^ s * boundaryWeight k s i = mahlerWeight k s i := by
  by_cases hi : i ≤ s
  · simp [boundaryWeight, mahlerWeight, hi, max_eq_left hi, pow_ne_zero s hk]
  · have hsi : s ≤ i := by omega
    have hp : k ^ i = k ^ s * k ^ (i - s) := by
      rw [← pow_add]
      congr 1
      omega
    simp only [boundaryWeight, mahlerWeight, if_neg hi, max_eq_right hsi, hp,
      mul_inv, ← inv_pow]
    simp [mul_assoc, mul_left_comm, mul_comm, pow_ne_zero s hk]

theorem boundaryRow_scale (k : K) (hk : k ≠ 0) (D s : ℕ) (A : ℕ → K) :
    k ^ s * boundaryRow k D A s = mahlerRow D k A s := by
  unfold boundaryRow mahlerRow
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  rw [← mul_assoc, boundaryWeight_scale k hk]

theorem boundaryRow_zero_iff (k : K) (hk : k ≠ 0) (D s : ℕ) (A : ℕ → K) :
    boundaryRow k D A s = 0 ↔ mahlerRow D k A s = 0 := by
  constructor
  · intro h
    rw [← boundaryRow_scale k hk D s A, h, mul_zero]
  · intro h
    have hh : k ^ s * boundaryRow k D A s = 0 := by
      rw [boundaryRow_scale k hk D s A, h]
    exact (mul_eq_zero.mp hh).resolve_left (pow_ne_zero s hk)

theorem polynomialBoundaryRow_scale (k : K) (hk : k ≠ 0)
    (D s : ℕ) (A : ℕ → K[X]) :
    Polynomial.C (k ^ s) * polynomialBoundaryRow k D A s =
      mahlerPolynomialRow D k A s := by
  unfold polynomialBoundaryRow mahlerPolynomialRow
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  rw [← mul_assoc, ← Polynomial.C_mul, boundaryWeight_scale k hk]

theorem polynomialBoundaryRow_zero_iff (k : K) (hk : k ≠ 0)
    (D s : ℕ) (A : ℕ → K[X]) :
    polynomialBoundaryRow k D A s = 0 ↔ mahlerPolynomialRow D k A s = 0 := by
  constructor
  · intro h
    rw [← polynomialBoundaryRow_scale k hk D s A, h, mul_zero]
  · intro h
    have hh : Polynomial.C (k ^ s) * polynomialBoundaryRow k D A s = 0 := by
      rw [polynomialBoundaryRow_scale k hk D s A, h]
    have hC : Polynomial.C (k ^ s) ≠ 0 :=
      Polynomial.C_ne_zero.mpr (pow_ne_zero s hk)
    exact (mul_eq_zero.mp hh).resolve_left hC

theorem all_polynomial_rows_zero_iff (k : K) (hk : k ≠ 0)
    (D : ℕ) (A : ℕ → K[X]) :
    (∀ s ≤ D, polynomialBoundaryRow k D A s = 0) ↔
      (∀ s ≤ D, mahlerPolynomialRow D k A s = 0) := by
  constructor <;> intro h s hs
  · exact (polynomialBoundaryRow_zero_iff k hk D s A).1 (h s hs)
  · exact (polynomialBoundaryRow_zero_iff k hk D s A).2 (h s hs)

/-- Includes the root-order scalar omitted from R15's matrix definition. -/
theorem full_radial_weight_scale (ell k : K) (hell : ell ≠ 0) (hk : k ≠ 0)
    (s i : ℕ) :
    (ell * k ^ s) * (ell * k ^ max s i)⁻¹ = mahlerWeight k s i := by
  calc
    (ell * k ^ s) * (ell * k ^ max s i)⁻¹ = k ^ s * boundaryWeight k s i := by
      unfold boundaryWeight
      field_simp [hell, hk] <;> ring
    _ = mahlerWeight k s i := boundaryWeight_scale k hk s i

end ErdosProblems.Erdos1049.PaperR16
