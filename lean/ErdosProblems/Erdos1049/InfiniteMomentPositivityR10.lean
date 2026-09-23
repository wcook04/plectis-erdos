import Mathlib.Analysis.Matrix.PosDef
import Mathlib.LinearAlgebra.Vandermonde
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Topology.Algebra.InfiniteSum.Real
import Mathlib.Topology.Algebra.InfiniteSum.Ring
import Mathlib.Tactic

/-!
# Infinite positive discrete moments

Candidate, UNRUN. These theorems concern the actual infinite sum, not a finite
atomic surrogate. Positive summable weights on distinct points of [0,1] give
positive definite Hankel matrices at every rank, including the empty rank.
Identifying the paper's particular hypergeometric rows with these moments is
a separate obligation, explicitly recorded in the manifest.

Pinned APIs inspected: Matrix/PosDef (finite dot-product interface),
Analysis/Matrix/PosDef (`PosDef.det_pos`), Vandermonde, InfiniteSum/Basic and
InfiniteSum/Order (`HasSum.congr_fun`, `hasSum_sum`, `Summable.tsum_pos`).
-/
namespace ErdosProblems.Erdos1049.PaperR10
open scoped BigOperators

noncomputable def discreteMoment (ω x : ℕ → ℝ) (m : ℕ) : ℝ :=
  ∑' k : ℕ, ω k * x k ^ m

noncomputable def discreteMomentHankel (ω x : ℕ → ℝ) (N : ℕ) :
    Matrix (Fin N) (Fin N) ℝ :=
  fun i j => discreteMoment ω x (i.val + j.val)

/-- The compact support bounds imply convergence of every moment. -/
theorem summable_discreteMoment (ω x : ℕ → ℝ)
    (hω : Summable ω) (hω0 : ∀ k, 0 ≤ ω k)
    (hx0 : ∀ k, 0 ≤ x k) (hx1 : ∀ k, x k ≤ 1) (m : ℕ) :
    Summable (fun k => ω k * x k ^ m) := by
  apply summable_of_sum_le (fun k => mul_nonneg (hω0 k) (pow_nonneg (hx0 k) _))
  intro s
  calc
    ∑ k ∈ s, ω k * x k ^ m ≤ ∑ k ∈ s, ω k := by
      apply Finset.sum_le_sum
      intro k hk
      simpa using mul_le_mul_of_nonneg_left (pow_le_one₀ (hx0 k) (hx1 k)) (hω0 k)
    _ ≤ ∑' k, ω k := hω.sum_le_tsum s (fun k _ => hω0 k)

noncomputable def momentPolynomialValue {N : ℕ} (c : Fin N → ℝ) (y : ℝ) : ℝ :=
  ∑ i : Fin N, c i * y ^ i.val

/-- The finite algebraic identity underlying the infinite Gram form. -/
lemma rankOne_quadratic_identity {N : ℕ} (c : Fin N → ℝ) (w y : ℝ) :
    (∑ i : Fin N, ∑ j : Fin N, c i * (w * y ^ (i.val + j.val)) * c j) =
      w * momentPolynomialValue c y ^ 2 := by
  unfold momentPolynomialValue
  rw [pow_two]
  simp only [Finset.mul_sum, Finset.sum_mul, pow_add]
  apply Finset.sum_congr rfl
  intro i hi
  apply Finset.sum_congr rfl
  intro j hj
  ring

/-- Interchange is justified by a finite sum of convergent moment series.
This proves both convergence of the squared-polynomial integral and its value. -/
theorem hasSum_moment_quadratic {N : ℕ} (ω x : ℕ → ℝ)
    (hω : Summable ω) (hω0 : ∀ k, 0 ≤ ω k)
    (hx0 : ∀ k, 0 ≤ x k) (hx1 : ∀ k, x k ≤ 1)
    (c : Fin N → ℝ) :
    HasSum (fun k => ω k * momentPolynomialValue c (x k) ^ 2)
      (∑ i : Fin N, ∑ j : Fin N,
        c i * discreteMoment ω x (i.val + j.val) * c j) := by
  have hm (m : ℕ) := (summable_discreteMoment ω x hω hω0 hx0 hx1 m).hasSum
  have h : HasSum
      (fun k => ∑ i : Fin N, ∑ j : Fin N,
        c i * (ω k * x k ^ (i.val + j.val)) * c j)
      (∑ i : Fin N, ∑ j : Fin N,
        c i * discreteMoment ω x (i.val + j.val) * c j) := by
    apply hasSum_sum
    intro i hi
    apply hasSum_sum
    intro j hj
    exact ((hm (i.val + j.val)).mul_left (c i)).mul_right (c j)
  exact h.congr_fun (fun k => (rankOne_quadratic_identity c (ω k) (x k)).symm)

/-- A nonzero coefficient vector cannot vanish at every atom. The first N
atoms already suffice, by the Vandermonde determinant. -/
theorem exists_atom_nonzero {N : ℕ} (x : ℕ → ℝ)
    (hx : Function.Injective x) (c : Fin N → ℝ) (hc : c ≠ 0) :
    ∃ k : ℕ, momentPolynomialValue c (x k) ≠ 0 := by
  by_contra h
  push_neg at h
  apply hc
  apply Matrix.eq_zero_of_forall_index_sum_mul_pow_eq_zero
    (f := fun i : Fin N => x i.val)
  · intro i j hij
    exact Fin.ext (hx hij)
  · intro j
    exact h j.val

theorem discreteMomentHankel_isHermitian (ω x : ℕ → ℝ) (N : ℕ) :
    (discreteMomentHankel ω x N).IsHermitian := by
  change (discreteMomentHankel ω x N).conjTranspose = discreteMomentHankel ω x N
  ext i j
  simp [Matrix.conjTranspose_apply, discreteMomentHankel, Nat.add_comm]

/-- Infinite support and positive mass at every atom give strict positivity,
not merely a limit of nonnegative finite determinants. -/
theorem discreteMomentHankel_posDef (ω x : ℕ → ℝ)
    (hω : Summable ω) (hωpos : ∀ k, 0 < ω k)
    (hx0 : ∀ k, 0 ≤ x k) (hx1 : ∀ k, x k ≤ 1)
    (hx : Function.Injective x) (N : ℕ) :
    (discreteMomentHankel ω x N).PosDef := by
  apply Matrix.PosDef.of_dotProduct_mulVec_pos (discreteMomentHankel_isHermitian ω x N)
  intro c hc
  have hs := hasSum_moment_quadratic ω x hω (fun k => (hωpos k).le) hx0 hx1 c
  obtain ⟨k, hk⟩ := exists_atom_nonzero x hx c hc
  have hp : 0 < ∑' k, ω k * momentPolynomialValue c (x k) ^ 2 :=
    hs.summable.tsum_pos (fun k => mul_nonneg (hωpos k).le (sq_nonneg _)) k
      (mul_pos (hωpos k) (sq_pos_of_ne_zero hk))
  rw [hs.tsum_eq] at hp
  simpa [dotProduct, Matrix.mulVec, discreteMomentHankel,
    Finset.mul_sum, mul_assoc] using hp

theorem discreteMomentHankel_det_pos (ω x : ℕ → ℝ)
    (hω : Summable ω) (hωpos : ∀ k, 0 < ω k)
    (hx0 : ∀ k, 0 ≤ x k) (hx1 : ∀ k, x k ≤ 1)
    (hx : Function.Injective x) (N : ℕ) :
    0 < (discreteMomentHankel ω x N).det :=
  (discreteMomentHankel_posDef ω x hω hωpos hx0 hx1 hx N).det_pos

/-- The logarithm proof handles atom 0 (the node 1) without a special case. -/
theorem geometricNodes_injective {q : ℝ} (hq0 : 0 < q) (hq1 : q < 1) :
    Function.Injective (fun k : ℕ => q ^ k) := by
  intro i j hij
  have hlog : Real.log q < 0 := Real.log_neg hq0 hq1
  have h := congrArg Real.log hij
  rw [Real.log_pow, Real.log_pow] at h
  have heq : (i : ℝ) = (j : ℝ) := mul_right_cancel₀ hlog.ne h
  exact_mod_cast heq

/-- A complete all-rank infinite-moment positivity theorem on a geometric
lattice. No finite-rank bound is present in its statement. -/
theorem geometricMomentHankel_det_pos (ω : ℕ → ℝ) (q : ℝ)
    (hω : Summable ω) (hωpos : ∀ k, 0 < ω k)
    (hq0 : 0 < q) (hq1 : q < 1) (N : ℕ) :
    0 < (discreteMomentHankel ω (fun k => q ^ k) N).det :=
  discreteMomentHankel_det_pos ω _ hω hωpos
    (fun k => pow_nonneg hq0.le k)
    (fun _ => pow_le_one₀ hq0.le hq1.le)
    (geometricNodes_injective hq0 hq1) N

@[simp] theorem discreteMomentHankel_det_zero_rank (ω x : ℕ → ℝ) :
    (discreteMomentHankel ω x 0).det = 1 := by simp

end ErdosProblems.Erdos1049.PaperR10
