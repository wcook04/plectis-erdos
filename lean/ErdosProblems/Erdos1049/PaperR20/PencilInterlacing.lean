import ErdosProblems.Erdos1049.PaperR20.QuadraticInertia
import Mathlib

/-!
# Inertia interlacing for nested matrix pencils

This file works in the original coordinate spaces.  The rank-`n` form is the
literal restriction of the rank-`n+1` form to the last-coordinate-zero
hyperplane.  No independently normalized matrices are compared.
-/

namespace ErdosProblems.Erdos1049.PaperR20

open Matrix Module QuadraticMap

noncomputable section

/-- The last-coordinate-zero hyperplane in `Fin (n + 1) → ℝ`. -/
def finLastZero (n : ℕ) : Submodule ℝ (Fin (n + 1) → ℝ) :=
  LinearMap.ker (LinearMap.proj (Fin.last n))

/-- Append a zero coordinate, regarded as an equivalence onto the
last-coordinate-zero hyperplane. -/
def finSnocZeroEquiv (n : ℕ) : (Fin n → ℝ) ≃ₗ[ℝ] finLastZero n where
  toFun x := ⟨Fin.snoc x 0, by simp [finLastZero, LinearMap.mem_ker]⟩
  invFun x := fun i => x.1 i.castSucc
  left_inv x := by
    funext i
    simp
  right_inv x := by
    apply Subtype.ext
    have hx : x.1 (Fin.last n) = 0 := by
      exact x.property
    funext i
    refine Fin.lastCases ?_ (fun j => ?_) i
    · simp [hx]
    · simp
  map_add' x y := by
    apply Subtype.ext
    funext i
    refine Fin.lastCases ?_ (fun j => ?_) i
    · simp
    · simp
  map_smul' c x := by
    apply Subtype.ext
    funext i
    refine Fin.lastCases ?_ (fun j => ?_) i
    · simp
    · simp

/-- The quadratic form of the real symmetric pencil `B - t A`. -/
def pencilQuadratic {n : ℕ} (A B : Matrix (Fin n) (Fin n) ℝ) (t : ℝ) :
    QuadraticForm ℝ (Fin n → ℝ) :=
  (B - t • A).toQuadraticMap'

/-- Extending a vector by zero identifies the leading principal quadratic
form with the restriction of the full quadratic form. -/
theorem pencilQuadratic_leadingPrincipal_equivalent {n : ℕ}
    (A B : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ) (t : ℝ) :
    QuadraticMap.Equivalent
      (pencilQuadratic (A.submatrix Fin.castSucc Fin.castSucc)
        (B.submatrix Fin.castSucc Fin.castSucc) t)
      ((pencilQuadratic A B t).restrict (finLastZero n)) := by
  refine ⟨⟨finSnocZeroEquiv n, ?_⟩⟩
  intro x
  simp only [pencilQuadratic, QuadraticMap.restrict_apply,
    Matrix.toQuadraticMap', LinearMap.BilinMap.toQuadraticMap_apply,
    Matrix.toLinearMap₂'_apply', Matrix.sub_apply, Matrix.smul_apply,
    Matrix.submatrix_apply, smul_eq_mul]
  simp [finSnocZeroEquiv, dotProduct, Matrix.mulVec, Fin.sum_univ_castSucc]

/-- At every real threshold, the number of positive directions of a leading
principal pencil lies between the full positive index and that index minus
one.  This is the inertia form of non-strict consecutive-rank interlacing. -/
theorem principalPencil_sigPos_interlaces {n : ℕ}
    (A B : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ) (t : ℝ) :
    _root_.sigPos
        (pencilQuadratic (A.submatrix Fin.castSucc Fin.castSucc)
          (B.submatrix Fin.castSucc Fin.castSucc) t) ≤
      _root_.sigPos (pencilQuadratic A B t) ∧
    _root_.sigPos (pencilQuadratic A B t) ≤
      _root_.sigPos
          (pencilQuadratic (A.submatrix Fin.castSucc Fin.castSucc)
            (B.submatrix Fin.castSucc Fin.castSucc) t) + 1 := by
  have hcodim : finrank ℝ (finLastZero n) + 1 =
      finrank ℝ (Fin (n + 1) → ℝ) := by
    rw [← (finSnocZeroEquiv n).finrank_eq]
    simp
  have hrest := sigPos_restrict_codim_one (pencilQuadratic A B t) (finLastZero n) hcodim
  have heq := (pencilQuadratic_leadingPrincipal_equivalent A B t).sigPos_eq
  simpa only [heq] using hrest

end

end ErdosProblems.Erdos1049.PaperR20
