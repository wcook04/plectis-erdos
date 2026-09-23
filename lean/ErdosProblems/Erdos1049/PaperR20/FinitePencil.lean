import Mathlib

/-!
# Symmetric definite matrix pencils

These generic lemmas are the spectral step for the finite coefficient pencil.
They retain positive definiteness and the positive remainder matrix as explicit
hypotheses. The coefficient identities and finite determinant certificates are
separate obligations. Candidate proofs; kernel validation is pending.
-/

namespace ErdosProblems.Erdos1049.PaperR20

open Matrix Polynomial

noncomputable section

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- The literal determinant polynomial det(X A − B). -/
def determinantPencil (A B : Matrix ι ι ℝ) : ℝ[X] :=
  Matrix.det (Matrix.of fun i j => X * C (A i j) - C (B i j))

theorem determinantPencil_eval (A B : Matrix ι ι ℝ) (x : ℝ) :
    (determinantPencil A B).eval x = (x • A - B).det := by
  change (Polynomial.evalRingHom x) (Matrix.det _) = _
  rw [RingHom.map_det]
  congr 1
  ext i j
  change (evalRingHom x) (X * C (A i j) - C (B i j)) = x * A i j - B i j
  simp only [map_sub, map_mul, coe_evalRingHom, eval_X, eval_C]

/-- The square-root change of coordinates preserves all roots, including their
multiplicities: the pencil is a nonzero constant times a real symmetric
characteristic polynomial. -/
theorem determinantPencil_splits {A B : Matrix ι ι ℝ}
    (hA : A.PosDef) (hB : B.IsHermitian) :
    (determinantPencil A B).Splits := by
  obtain ⟨S, hS, hArepr⟩ := Matrix.posDef_iff_eq_conjTranspose_mul_self.mp hA
  let T := S⁻¹
  have hTS : T * S = 1 :=
    Matrix.nonsing_inv_mul _ ((Matrix.isUnit_iff_isUnit_det S).mp hS)
  have hSTstar : Sᴴ * Tᴴ = 1 := by
    rw [← Matrix.conjTranspose_mul, hTS, Matrix.conjTranspose_one]
  let H := Tᴴ * B * T
  have hH : H.IsHermitian := Matrix.isHermitian_conjTranspose_mul_mul T hB
  have hBrepr : Sᴴ * H * S = B := by
    calc
      Sᴴ * H * S = (Sᴴ * Tᴴ) * B * (T * S) := by
        dsimp [H]
        noncomm_ring
      _ = B := by rw [hSTstar, hTS, Matrix.one_mul, Matrix.mul_one]
  have hcongruence (x : ℝ) : x • A - B = Sᴴ * (x • (1 : Matrix ι ι ℝ) - H) * S := by
    rw [Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_smul, Matrix.smul_mul,
      Matrix.mul_one, ← hArepr, hBrepr]
  have hpoly : determinantPencil A B = C (S.det * S.det) * H.charpoly := by
    apply Polynomial.funext
    intro x
    rw [determinantPencil_eval, hcongruence, Matrix.det_mul, Matrix.det_mul]
    simp only [Matrix.det_conjTranspose, star_trivial, Polynomial.eval_mul,
      Polynomial.eval_C, Matrix.eval_charpoly, Matrix.scalar_apply,
      Matrix.smul_one_eq_diagonal]
    ring
  rw [hpoly]
  exact hH.splits_charpoly.C_mul _

/-- A positive remainder at F puts every real root strictly below F. -/
theorem determinantPencil_root_lt {A B : Matrix ι ι ℝ} {F x : ℝ}
    (hA : A.PosDef) (hR : (F • A - B).PosDef)
    (hx : (determinantPencil A B).IsRoot x) : x < F := by
  by_contra h
  have hle : F ≤ x := le_of_not_gt h
  have hpos := hR.add_posSemidef (hA.posSemidef.smul (sub_nonneg.mpr hle))
  have heq : (F • A - B) + (x - F) • A = x • A - B := by
    ext i j
    simp only [Matrix.add_apply, Matrix.sub_apply, Matrix.smul_apply, smul_eq_mul]
    ring
  rw [heq] at hpos
  have hz : (x • A - B).det = 0 := by
    simpa only [Polynomial.IsRoot, determinantPencil_eval] using hx
  exact hpos.det_pos.ne' hz

/-- The complete root statement requires splitting, not merely a claim about
the subset of roots already known to be real. -/
theorem determinantPencil_splits_and_roots_lt {A B : Matrix ι ι ℝ} {F : ℝ}
    (hA : A.PosDef) (hB : B.IsHermitian) (hR : (F • A - B).PosDef) :
    (determinantPencil A B).Splits ∧
      ∀ x : ℝ, (determinantPencil A B).IsRoot x → x < F :=
  ⟨determinantPencil_splits hA hB, fun _ hx => determinantPencil_root_lt hA hR hx⟩

#print axioms determinantPencil_splits_and_roots_lt

end
end ErdosProblems.Erdos1049.PaperR20
