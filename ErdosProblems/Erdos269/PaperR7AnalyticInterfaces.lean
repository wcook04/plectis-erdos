import ErdosProblems.Erdos269.KernelCarryRank
import Mathlib.RingTheory.Algebraic.Basic
import Mathlib.Tactic

/-!
# Round 7: proved algebra around explicitly unresolved analytic inputs

This file DOES NOT prove the two-prime transcendence theorem. Its final algebraic
step is separated from THREE hypotheses still requiring analytic proofs:
transcendence of the specified Hecke--Mahler value, and the two identities for
the actual series. The parameters are visible, not axioms or admitted theorems.

It also proves the constant rank-one upper witness for the uniform carry
approximation. The lower bound over every finite separated rank remains open
as a formalisation obligation in this return.

Validation: authored, not compiled. No admissions.
-/

namespace ErdosProblems.Erdos269.PaperR7

open Polynomial

/-- Exact value named `A` on the page; this definition makes no arithmetic assertion. -/
noncomputable def twoPrimeHeckeValue (p q : ℕ) : ℝ :=
  ∑' n : ℕ, ((p : ℝ)⁻¹) ^ n *
    ((q : ℝ)⁻¹) ^ ⌊(n : ℝ) * Real.logb q p⌋₊

private theorem transcendental_polynomial_image_of_coeff
    {A : ℝ} (hA : Transcendental ℚ A) (f : ℚ[X])
    (n : ℕ) (hn : 0 < n) (hcoeff : f.coeff n ≠ 0) :
    Transcendental ℚ (Polynomial.aeval A f) := by
  have hf : f ≠ 0 := by
    intro h
    apply hcoeff
    simp [h]
  have hdeg : f.natDegree ≠ 0 := by
    intro h
    apply hcoeff
    exact Polynomial.coeff_eq_zero_of_natDegree_lt (by omega)
  exact hA.aeval f hdeg
    (mem_nonZeroDivisors_of_ne_zero (Polynomial.leadingCoeff_ne_zero.mpr hf))

noncomputable def distinctValuePolynomial (p q : ℚ) : ℚ[X] :=
  C ((q - p) / (q - 1)) * X + C (p / (q - 1))

noncomputable def repeatedValuePolynomial (p q : ℚ) : ℚ[X] :=
  C ((p + q - 1) / (q - 1)) * X - C ((p - 1) / (q - 1)) * X ^ 2

/-- Algebraic reduction only. In particular `hA`, `hD`, `hR` are not discharged. -/
theorem two_prime_transcendence_from_analytic_inputs
    (p q : ℚ) (hp : 1 < p) (hq : 1 < q) (hpq : p ≠ q)
    (A D R : ℝ) (hA : Transcendental ℚ A)
    (hD : D = (((q : ℝ) - p) * A + p) / ((q : ℝ) - 1))
    (hR : R = (((p : ℝ) + q - 1) * A - ((p : ℝ) - 1) * A ^ 2) /
      ((q : ℝ) - 1)) :
    Transcendental ℚ D ∧ Transcendental ℚ R := by
  have hp1 : p - 1 ≠ 0 := sub_ne_zero.mpr (ne_of_gt hp)
  have hq1 : q - 1 ≠ 0 := sub_ne_zero.mpr (ne_of_gt hq)
  have hqp : q - p ≠ 0 := sub_ne_zero.mpr hpq.symm
  have hDc : (distinctValuePolynomial p q).coeff 1 ≠ 0 := by
    simpa [distinctValuePolynomial] using div_ne_zero hqp hq1
  have hRc : (repeatedValuePolynomial p q).coeff 2 ≠ 0 := by
    simpa [repeatedValuePolynomial] using neg_ne_zero.mpr (div_ne_zero hp1 hq1)
  have hDt := transcendental_polynomial_image_of_coeff hA
    (distinctValuePolynomial p q) 1 (by norm_num) hDc
  have hRt := transcendental_polynomial_image_of_coeff hA
    (repeatedValuePolynomial p q) 2 (by norm_num) hRc
  have heD : Polynomial.aeval A (distinctValuePolynomial p q) = D := by
    rw [hD]
    simp [distinctValuePolynomial]
    push_cast
    ring
  have heR : Polynomial.aeval A (repeatedValuePolynomial p q) = R := by
    rw [hR]
    simp [repeatedValuePolynomial]
    push_cast
    ring
  exact ⟨heD ▸ hDt, heR ▸ hRt⟩

/-- The normalised real-valued carry matrix, using the actual integer-log carry. -/
noncomputable def realCarryMatrix (p q r i j : ℕ) : ℝ :=
  ((r : ℝ)⁻¹) ^ logCarry r (p ^ i) (q ^ j)

/-- The rank-one upper witness and its exact pointwise error. This is not the
universal lower bound, and is not counted as `res:uniform-rank` in coverage. -/
theorem uniform_carry_midpoint_witness {p q r : ℕ}
    (hp : 0 < p) (hq : 0 < q) (hr : 1 < r) :
    (∃ f g : ℕ → ℝ, ∀ i j,
      (1 + (r : ℝ)⁻¹) / 2 = f i * g j) ∧
    (∀ i j,
      |realCarryMatrix p q r i j - (1 + (r : ℝ)⁻¹) / 2| =
        ((r : ℝ) - 1) / (2 * (r : ℝ))) := by
  refine ⟨⟨fun _ => (1 + (r : ℝ)⁻¹) / 2, fun _ => 1, by simp⟩, ?_⟩
  intro i j
  have hbit := logCarry_le_one hr (pow_ne_zero i hp.ne') (pow_ne_zero j hq.ne')
  have hrR : (1 : ℝ) < r := by exact_mod_cast hr
  have hr0 : (0 : ℝ) < r := by linarith
  have hinv : (r : ℝ)⁻¹ ≤ 1 := (inv_le_one₀ hr0).mpr hrR.le
  have hcase : logCarry r (p ^ i) (q ^ j) = 0 ∨
      logCarry r (p ^ i) (q ^ j) = 1 := by omega
  rcases hcase with h | h
  · rw [realCarryMatrix, h, pow_zero, abs_of_nonneg (by linarith)]
    field_simp [ne_of_gt hr0] <;> ring
  · rw [realCarryMatrix, h, pow_one, abs_of_nonpos (by linarith)]
    field_simp [ne_of_gt hr0] <;> ring

end ErdosProblems.Erdos269.PaperR7
