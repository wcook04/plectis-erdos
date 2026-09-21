import Mathlib

/-!
# Correct boundary weights for a polynomial Mahler relation

The pole of L(z^(k^i)) at a primitive (ell*k^s)-th root contributes
1/(ell*k^(max i s)), not k^(s-i) with natural-number subtraction.
This file proves the finite algebraic elimination after the boundary rows
have been obtained. It does not assume or claim the radial/source bridge.

Status: authored candidate; not elaborated in Lean in this environment.
-/

noncomputable section
open scoped BigOperators
namespace Rolling1049.Remaining.R15BoundaryWeights

variable {K : Type*} [Field K]

def boundaryWeight (k : K) (s i : ℕ) : K := (k ^ max s i)⁻¹

def boundaryRow (k : K) (m : ℕ) (A : ℕ → K) (s : ℕ) : K :=
  ∑ i ∈ Finset.range (m + 1), boundaryWeight k s i * A i

theorem boundaryWeight_of_le {s i : ℕ} (k : K) (hi : i ≤ s) :
    boundaryWeight k s i = (k ^ s)⁻¹ := by
  simp [boundaryWeight, max_eq_left hi]

theorem boundaryWeight_of_ge {s i : ℕ} (k : K) (hi : s ≤ i) :
    boundaryWeight k s i = (k ^ i)⁻¹ := by
  simp [boundaryWeight, max_eq_right hi]

theorem boundaryWeight_difference (k : K) (s i : ℕ) :
    boundaryWeight k s i - boundaryWeight k (s + 1) i =
      if i ≤ s then (k ^ s)⁻¹ - (k ^ (s + 1))⁻¹ else 0 := by
  by_cases h : i ≤ s
  · simp [boundaryWeight, h, max_eq_left h,
      max_eq_left (Nat.le_trans h (Nat.le_succ s))]
  · have h' : s + 1 ≤ i := by omega
    simp [boundaryWeight, h, max_eq_right (by omega : s ≤ i),
      max_eq_right h']

theorem inverse_power_step_ne_zero (k : K) (hk : k ≠ 0)
    (hk1 : k ≠ 1) (s : ℕ) :
    (k ^ s)⁻¹ - (k ^ (s + 1))⁻¹ ≠ 0 := by
  intro h
  have hpow : k ^ s = k ^ (s + 1) := inv_injective (sub_eq_zero.mp h)
  have hz : k ^ s ≠ 0 := pow_ne_zero s hk
  have heq : k ^ s * 1 = k ^ s * k := by simpa [pow_succ] using hpow
  have hone : (1 : K) = k := mul_left_cancel₀ hz heq
  exact hk1 hone.symm

/-- Successive rows isolate a coefficient once all earlier coefficients vanish. -/
theorem row_difference_isolates (k : K) (m i : ℕ) (A : ℕ → K)
    (hi : i ≤ m) (hprevious : ∀ j < i, A j = 0) :
    boundaryRow k m A i - boundaryRow k m A (i + 1) =
      ((k ^ i)⁻¹ - (k ^ (i + 1))⁻¹) * A i := by
  classical
  unfold boundaryRow
  rw [← Finset.sum_sub_distrib]
  have hsum :
      (∑ j ∈ Finset.range (m + 1),
        (boundaryWeight k i j * A j - boundaryWeight k (i + 1) j * A j)) =
      boundaryWeight k i i * A i - boundaryWeight k (i + 1) i * A i := by
    apply Finset.sum_eq_single i
    · intro j hj hji
      by_cases hjlt : j < i
      · simp [hprevious j hjlt]
      · have hge : i + 1 ≤ j := by omega
        simp [boundaryWeight_of_ge k (by omega : i ≤ j),
          boundaryWeight_of_ge k hge]
    · intro hnot
      exact False.elim (hnot (Finset.mem_range.mpr (by omega)))
  rw [hsum]
  simp only [boundaryWeight_of_le k (Nat.le_refl i),
    boundaryWeight_of_le k (Nat.le_succ i), pow_succ, mul_inv_rev, inv_pow]
  ring

/-- The last boundary row isolates the final coefficient. -/
theorem last_row_isolates (k : K) (m : ℕ) (A : ℕ → K)
    (hprevious : ∀ j < m, A j = 0) :
    boundaryRow k m A m = (k ^ m)⁻¹ * A m := by
  classical
  unfold boundaryRow
  rw [Finset.sum_eq_single m]
  · exact congrArg (fun x : K => x * A m)
      (boundaryWeight_of_le k (Nat.le_refl m))
  · intro j hj hjm
    have hjlt : j < m := by
      have := Finset.mem_range.mp hj
      omega
    simp [hprevious j hjlt]
  · intro hnot
    exact False.elim (hnot (Finset.mem_range.mpr (Nat.lt_succ_self m)))

/-- Invertibility of the exact triangular boundary system. -/
theorem boundary_rows_injective (k : K) (hk : k ≠ 0) (hk1 : k ≠ 1)
    (m : ℕ) (A : ℕ → K)
    (hrow : ∀ s ≤ m, boundaryRow k m A s = 0) :
    ∀ i ≤ m, A i = 0 := by
  have hall : ∀ i : ℕ, i ≤ m → A i = 0 := by
    intro i
    induction i using Nat.strong_induction_on with
    | h i ih =>
      intro hi
      have hprevious : ∀ j < i, A j = 0 := by
        intro j hj
        exact ih j hj (by omega)
      by_cases him : i < m
      · have hd := row_difference_isolates k m i A hi hprevious
        rw [hrow i hi, hrow (i + 1) (by omega), sub_self] at hd
        exact (mul_eq_zero.mp hd.symm).resolve_left
          (inverse_power_step_ne_zero k hk hk1 i)
      · have hieq : i = m := by omega
        subst i
        have hd := last_row_isolates k m A hprevious
        rw [hrow m (Nat.le_refl m)] at hd
        exact (mul_eq_zero.mp hd.symm).resolve_left
          (inv_ne_zero (pow_ne_zero m hk))
  exact hall

/-- The same elimination applies coefficientwise to polynomial rows. -/
def polynomialBoundaryRow (k : K) (m : ℕ) (A : ℕ → Polynomial K)
    (s : ℕ) : Polynomial K :=
  ∑ i ∈ Finset.range (m + 1), Polynomial.C (boundaryWeight k s i) * A i

theorem polynomial_boundary_rows_injective (k : K) (hk : k ≠ 0)
    (hk1 : k ≠ 1) (m : ℕ) (A : ℕ → Polynomial K)
    (hrow : ∀ s ≤ m, polynomialBoundaryRow k m A s = 0) :
    ∀ i ≤ m, A i = 0 := by
  intro i hi
  apply Polynomial.ext
  intro d
  have hc : ∀ s ≤ m,
      boundaryRow k m (fun j => (A j).coeff d) s = 0 := by
    intro s hs
    have heq := congrArg (fun p : Polynomial K => p.coeff d) (hrow s hs)
    simpa [polynomialBoundaryRow, boundaryRow, Polynomial.coeff_C_mul] using heq
  simpa using boundary_rows_injective k hk hk1 m
    (fun j => (A j).coeff d) hc i hi

end Rolling1049.Remaining.R15BoundaryWeights
end
