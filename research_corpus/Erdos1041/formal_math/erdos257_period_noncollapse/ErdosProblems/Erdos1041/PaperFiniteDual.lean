import Mathlib

/-!
# The finite dual implication behind the circle-slice arity floor

The majorant and the common-circle packing inequalities are explicit inputs.
This is the finite summation and supremum step, NOT a formalisation of the
hyperbolic packing supplier. See the coverage row `res:dual-arity-floor`.

New source, not elaborated in this environment.
-/

noncomputable section

namespace ErdosProblems.Erdos1041.PaperFiniteDual

open scoped BigOperators
open Set

/-- A dual majorant and slice-wise packing bounds force an arity floor. -/
theorem arity_floor_of_majorant
    {k q : ℕ} {x U π₀ : ℝ}
    (d : Fin k → ℝ) (r σ : Fin q → ℝ)
    (ell : ℝ → ℝ) (width : ℝ → ℝ → ℝ)
    (hU : 0 < U) (hσ : ∀ i, 0 ≤ σ i)
    (hmass : x ≤ ∑ j, ell (d j))
    (hmajorant : ∀ j, ell (d j) ≤ U + ∑ i, σ i * width (d j) (r i))
    (hpacking : ∀ i, ∑ j, width (d j) (r i) ≤ π₀) :
    (x - π₀ * ∑ i, σ i) / U ≤ (k : ℝ) := by
  have hsum : x ≤ (k : ℝ) * U + π₀ * ∑ i, σ i := by
    calc
      x ≤ ∑ j, ell (d j) := hmass
      _ ≤ ∑ j, (U + ∑ i, σ i * width (d j) (r i)) :=
        Finset.sum_le_sum (fun j _ => hmajorant j)
      _ = (k : ℝ) * U + ∑ i, σ i * ∑ j, width (d j) (r i) := by
        simp only [Finset.sum_add_distrib, Finset.sum_const,
          Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
        congr 1
        rw [Finset.sum_comm]
        exact Finset.sum_congr rfl (fun i _ => (Finset.mul_sum _ _ _).symm)
      _ ≤ (k : ℝ) * U + ∑ i, σ i * π₀ := by
        have hstep : ∑ i, σ i * ∑ j, width (d j) (r i) ≤ ∑ i, σ i * π₀ :=
          Finset.sum_le_sum fun i _ =>
            mul_le_mul_of_nonneg_left (hpacking i) (hσ i)
        linarith
      _ = (k : ℝ) * U + π₀ * ∑ i, σ i := by
        rw [← Finset.sum_mul]
        ring
  apply (div_le_iff₀ hU).2
  linarith

/-- The supremum used in the displayed paper is an ordinary real supremum;
its bounded-above hypothesis must not be silently omitted in Lean. -/
def dualValues {q : ℕ} (d₀ : ℝ) (r σ : Fin q → ℝ)
    (ell : ℝ → ℝ) (width : ℝ → ℝ → ℝ) : Set ℝ :=
  {u | ∃ d : ℝ, d₀ ≤ d ∧ u = ell d - ∑ i, σ i * width d (r i)}

theorem majorant_of_sSup {q : ℕ} {d₀ d : ℝ}
    (r σ : Fin q → ℝ) (ell : ℝ → ℝ) (width : ℝ → ℝ → ℝ)
    (hbounded : BddAbove (dualValues d₀ r σ ell width)) (hd : d₀ ≤ d) :
    ell d ≤ sSup (dualValues d₀ r σ ell width) + ∑ i, σ i * width d (r i) := by
  have hmem : ell d - ∑ i, σ i * width d (r i) ∈ dualValues d₀ r σ ell width :=
    ⟨d, hd, rfl⟩
  have h := le_csSup hbounded hmem
  linarith

/-- Supremum formulation of the finite consumer; packing remains a premise. -/
theorem arity_floor_of_sSup
    {k q : ℕ} {d₀ x π₀ : ℝ}
    (d : Fin k → ℝ) (r σ : Fin q → ℝ)
    (ell : ℝ → ℝ) (width : ℝ → ℝ → ℝ)
    (hd : ∀ j, d₀ ≤ d j)
    (hbounded : BddAbove (dualValues d₀ r σ ell width))
    (hU : 0 < sSup (dualValues d₀ r σ ell width))
    (hσ : ∀ i, 0 ≤ σ i)
    (hmass : x ≤ ∑ j, ell (d j))
    (hpacking : ∀ i, ∑ j, width (d j) (r i) ≤ π₀) :
    (x - π₀ * ∑ i, σ i) / sSup (dualValues d₀ r σ ell width) ≤ (k : ℝ) :=
  arity_floor_of_majorant d r σ ell width hU hσ hmass
    (fun j => majorant_of_sSup r σ ell width hbounded (hd j)) hpacking

#print axioms arity_floor_of_sSup

end ErdosProblems.Erdos1041.PaperFiniteDual
