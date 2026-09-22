import Mathlib

/-!
# The finite algebra at the end of the root-of-unity obstruction

Candidate source; new Lean checks/audits UNRUN.
The analytic root-of-unity limit is NOT introduced as an axiom. This module
formalises the concluding triangular argument as a separate reusable lemma.
The remaining analytic-to-polynomial bridge is expressly recorded in the
manifest and ordinary proof, rather than passed off as a Lean theorem.
-/
namespace ErdosProblems.Erdos1049.PaperR11
open scoped BigOperators
open Polynomial

variable {K : Type*} [Field K]

def mahlerWeight (k : K) (r i : ℕ) : K :=
  if i ≤ r then 1 else k⁻¹ ^ (i - r)

def mahlerRow (D : ℕ) (k : K) (P : ℕ → K) (r : ℕ) : K :=
  ∑ i ∈ Finset.range (D + 1), mahlerWeight k r i * P i

lemma mahlerRow_succ (D : ℕ) (k : K) (P : ℕ → K) (r : ℕ) :
    mahlerRow (D + 1) k P r = mahlerRow D k P r +
      mahlerWeight k r (D + 1) * P (D + 1) := by
  simp only [mahlerRow, Finset.sum_range_succ]

lemma mahlerRow_top (D : ℕ) (k : K) (P : ℕ → K) :
    mahlerRow D k P D = ∑ i ∈ Finset.range (D + 1), P i := by
  unfold mahlerRow
  apply Finset.sum_congr rfl
  intro i hi
  have hiD : i ≤ D := by have h := Finset.mem_range.mp hi; omega
  simp [mahlerWeight, hiD]

lemma mahlerRow_penultimate (D : ℕ) (k : K) (P : ℕ → K) :
    mahlerRow (D + 1) k P D =
      (∑ i ∈ Finset.range (D + 1), P i) + k⁻¹ * P (D + 1) := by
  rw [mahlerRow_succ, mahlerRow_top]
  simp [mahlerWeight]

/-- The triangular root-order equations force all coefficients to vanish.
There is no root-limit, determinant-nonzero or coefficient-vanishing premise
hidden in this finite algebra statement. -/
theorem mahler_triangular_injective (D : ℕ) (k : K) (hk : k ≠ 1) (P : ℕ → K) :
    (∀ r ≤ D, mahlerRow D k P r = 0) → ∀ i ≤ D, P i = 0 := by
  induction D with
  | zero =>
      intro h i hi
      have hi0 : i = 0 := by omega
      subst i
      simpa [mahlerRow, mahlerWeight] using h 0 (by omega)
  | succ D ih =>
      intro h i hi
      have htop := h (D + 1) (by omega)
      have hprev := h D (by omega)
      rw [mahlerRow_top, Finset.sum_range_succ] at htop
      rw [mahlerRow_penultimate] at hprev
      have hlast : (1 - k⁻¹) * P (D + 1) = 0 := by
        linear_combination htop - hprev
      have hfactor : 1 - k⁻¹ ≠ 0 := by
        intro hzero
        have hinv : k⁻¹ = 1 := (sub_eq_zero.mp hzero).symm
        have heq := congrArg (fun z : K => z⁻¹) hinv
        exact hk (by simpa using heq)
      have hP : P (D + 1) = 0 := (mul_eq_zero.mp hlast).resolve_left hfactor
      have hsmall : ∀ r ≤ D, mahlerRow D k P r = 0 := by
        intro r hr
        have hh := h r (by omega)
        rw [mahlerRow_succ, hP, mul_zero, add_zero] at hh
        exact hh
      by_cases heq : i = D + 1
      · simpa [heq] using hP
      · exact ih hsmall i (by omega)

noncomputable def mahlerPolynomialRow (D : ℕ) (k : K)
    (P : ℕ → K[X]) (r : ℕ) : K[X] :=
  ∑ i ∈ Finset.range (D + 1), Polynomial.C (mahlerWeight k r i) * P i

/-- Coefficientwise lifting gives the exact polynomial conclusion used by the
ordinary proof once the infinitely-many-roots step has been supplied. -/
theorem mahler_polynomial_rows_injective (D : ℕ) (k : K) (hk : k ≠ 1)
    (P : ℕ → K[X]) (h : ∀ r ≤ D, mahlerPolynomialRow D k P r = 0) :
    ∀ i ≤ D, P i = 0 := by
  intro i hi
  apply Polynomial.ext
  intro d
  have hcoeff : ∀ r ≤ D,
      mahlerRow D k (fun j => (P j).coeff d) r = 0 := by
    intro r hr
    have hh := congrArg (fun p : K[X] => p.coeff d) (h r hr)
    simpa [mahlerPolynomialRow, mahlerRow] using hh
  simpa using mahler_triangular_injective D k hk
    (fun j => (P j).coeff d) hcoeff i hi

end ErdosProblems.Erdos1049.PaperR11
