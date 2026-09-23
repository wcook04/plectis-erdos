import ErdosProblems.Erdos1049.PaperR20.PencilInterlacing
import ErdosProblems.Erdos1049.PaperR20.FinitePencil
import Mathlib.Analysis.Matrix.Spectrum
import Mathlib.LinearAlgebra.QuadraticForm.Signature

/-!
# Spectral inertia for real symmetric pencils

The main lemma diagonalizes the quadratic form of `H - t I` in the
orthonormal eigenbasis of a Hermitian matrix.  It therefore computes its
positive index as the number of eigenvalues strictly above `t`, with repeated
eigenvalues counted by their indices.
-/

namespace ErdosProblems.Erdos1049.PaperR20

open Matrix Polynomial Module QuadraticMap
open scoped Matrix
open scoped BigOperators

noncomputable section

/-- For a symmetric real matrix, polarizing its matrix quadratic form returns
the original bilinear form. -/
theorem associated_toQuadraticMap'_apply_of_isSymm {n : Type*}
    [Fintype n] [DecidableEq n] {M : Matrix n n ℝ} (hM : M.IsSymm)
    (x y : n → ℝ) :
    QuadraticMap.associated (M.toQuadraticMap') x y =
      Matrix.toLinearMap₂' ℝ M x y := by
  rw [Matrix.toQuadraticMap', QuadraticMap.associated_left_inverse]
  intro u v
  simp only [Matrix.toLinearMap₂'_apply', dotProduct, Matrix.mulVec, Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i hi
  apply Finset.sum_congr rfl
  intro j hj
  rw [hM.apply i j]
  ring

/-- The matrix quadratic form of a Hermitian matrix shifted by `t I` is
equivalent to the weighted sum of squares whose weights are `λᵢ - t`. -/
theorem hermitian_sub_smul_one_equivalent_weightedSumSquares {n : Type*}
    [Fintype n] [DecidableEq n] (H : Matrix n n ℝ) (hH : H.IsHermitian)
    (t : ℝ) :
    QuadraticMap.Equivalent
      ((H - t • (1 : Matrix n n ℝ)).toQuadraticMap')
      (QuadraticMap.weightedSumSquares ℝ (fun i : n ↦ hH.eigenvalues i - t)) := by
  let Q : QuadraticForm ℝ (n → ℝ) :=
    (H - t • (1 : Matrix n n ℝ)).toQuadraticMap'
  let v : Basis n ℝ (n → ℝ) := hH.eigenvectorBasis.toBasis.map (WithLp.linearEquiv 2 ℝ (n → ℝ))
  have hM : (H - t • (1 : Matrix n n ℝ)).IsSymm := by
    have hHs : H.IsSymm := by simpa [Matrix.IsHermitian] using hH
    exact hHs.sub (Matrix.isSymm_one.smul t)
  have heig (i : n) : H *ᵥ v i = hH.eigenvalues i • v i :=
    hH.mulVec_eigenvectorBasis i
  have hdot (i j : n) : v i ⬝ᵥ v j = if i = j then 1 else 0 := by
    have hi := (orthonormal_iff_ite.mp hH.eigenvectorBasis.orthonormal) i j
    simpa only [EuclideanSpace.inner_eq_star_dotProduct, star_trivial,
      dotProduct_comm] using hi
  have hform (i j : n) :
      Matrix.toLinearMap₂' ℝ (H - t • (1 : Matrix n n ℝ)) (v i) (v j) =
        (hH.eigenvalues j - t) * (v i ⬝ᵥ v j) := by
    simp only [Matrix.toLinearMap₂'_apply', Matrix.sub_mulVec,
      Matrix.smul_mulVec, Matrix.one_mulVec, heig, dotProduct_sub, dotProduct_smul,
      smul_eq_mul]
    ring
  have hvortho : (QuadraticMap.associated Q).IsOrthoᵢ v := by
    intro i j hij
    change QuadraticMap.associated Q (v i) (v j) = 0
    rw [associated_toQuadraticMap'_apply_of_isSymm hM, hform, hdot, if_neg hij, mul_zero]
  have hrepr : Q.basisRepr v =
      QuadraticMap.weightedSumSquares ℝ (fun i : n ↦ hH.eigenvalues i - t) := by
    rw [QuadraticMap.basisRepr_eq_of_iIsOrtho Q v hvortho]
    congr 1
    funext i
    change Matrix.toLinearMap₂' ℝ (H - t • (1 : Matrix n n ℝ)) (v i) (v i) = _
    rw [hform, hdot, if_pos rfl, mul_one]
  rw [← hrepr]
  exact ⟨Q.isometryEquivBasisRepr v⟩

/-- Sylvester inertia in an eigenbasis: the positive index is the number of
Hermitian eigenvalues strictly above the threshold. -/
theorem hermitian_sub_smul_one_sigPos_eq_card {n : Type*}
    [Fintype n] [DecidableEq n] (H : Matrix n n ℝ) (hH : H.IsHermitian)
    (t : ℝ) :
    _root_.sigPos
        ((H - t • (1 : Matrix n n ℝ)).toQuadraticMap') =
      {i | t < hH.eigenvalues i}.ncard := by
  rw [(hermitian_sub_smul_one_equivalent_weightedSumSquares H hH t).sigPos_eq,
    QuadraticForm.sigPos_weightedSumSquares]
  congr 1
  ext i
  simp only [Set.mem_setOf_eq, sub_pos]

/-- Reindexing Mathlib's eigenvalues by the original finite type preserves
every strict-threshold count. -/
theorem card_eigenvalues_gt_eq_card_eigenvalues₀_gt {n : Type*}
    [Fintype n] [DecidableEq n] (H : Matrix n n ℝ) (hH : H.IsHermitian)
    (t : ℝ) :
    {i | t < hH.eigenvalues i}.ncard = {i | t < hH.eigenvalues₀ i}.ncard := by
  apply Set.ncard_congr'
  let e : n ≃ Fin (Fintype.card n) :=
    (Fintype.equivOfCardEq (Fintype.card_fin _)).symm
  exact e.subtypeEquiv (fun i ↦ by simp only [Matrix.IsHermitian.eigenvalues, e, Set.mem_setOf_eq])

/-- Congruence by an invertible real matrix preserves the quadratic form up
to linear equivalence. -/
theorem congr_toQuadraticMap'_equivalent {n : Type*}
    [Fintype n] [DecidableEq n] (S M : Matrix n n ℝ) (hS : IsUnit S) :
    QuadraticMap.Equivalent ((Sᴴ * M * S).toQuadraticMap') M.toQuadraticMap' := by
  obtain ⟨hSinv⟩ := hS.nonempty_invertible
  refine ⟨{ __ := S.toLinearEquiv' hSinv, map_app' := ?_ }⟩
  intro x
  simp only [Matrix.toLinearEquiv'_apply, Matrix.toQuadraticMap',
    LinearMap.BilinMap.toQuadraticMap_apply, Matrix.toLinearMap₂'_apply']
  change (S *ᵥ x) ⬝ᵥ (M *ᵥ (S *ᵥ x)) = x ⬝ᵥ ((Sᴴ * M * S) *ᵥ x)
  rw [Matrix.conjTranspose_eq_transpose_of_trivial, ← Matrix.mulVec_mulVec,
    ← Matrix.mulVec_mulVec, Matrix.dotProduct_mulVec x Sᵀ, Matrix.vecMul_transpose]

/-- The source-level Sylvester identity for a real symmetric definite pencil.
The normalization is produced from positive definiteness, and the result is
stated as an existential so no independently chosen normalization is compared
with another rank. -/
theorem pencil_sigPos_eq_card_normalized_eigenvalues {n : ℕ}
    (A B : Matrix (Fin n) (Fin n) ℝ)
    (hA : A.PosDef) (hB : B.IsHermitian) :
    ∃ (H : Matrix (Fin n) (Fin n) ℝ) (hH : H.IsHermitian),
      (∀ t : ℝ, _root_.sigPos (pencilQuadratic A B t) =
        {i | t < hH.eigenvalues₀ i}.ncard) ∧
      (determinantPencil A B).roots =
        Multiset.map (RCLike.ofReal ∘ hH.eigenvalues₀) Finset.univ.val := by
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
  refine ⟨H, hH, ?_, ?_⟩
  · intro t
    have hcongruence :
        B - t • A =
          Sᴴ * (H - t • (1 : Matrix (Fin n) (Fin n) ℝ)) * S := by
      rw [Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_smul, Matrix.smul_mul,
        Matrix.mul_one, ← hArepr, hBrepr]
    have hequiv := congr_toQuadraticMap'_equivalent S
      (H - t • (1 : Matrix (Fin n) (Fin n) ℝ)) hS
    rw [pencilQuadratic, hcongruence, hequiv.sigPos_eq]
    rw [hermitian_sub_smul_one_sigPos_eq_card H hH t,
      card_eigenvalues_gt_eq_card_eigenvalues₀_gt H hH t]
  · have hcongruence (x : ℝ) :
        x • A - B =
          Sᴴ * (x • (1 : Matrix (Fin n) (Fin n) ℝ) - H) * S := by
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
    rw [hpoly, Polynomial.roots_C_mul]
    · exact hH.roots_charpoly_eq_eigenvalues₀
    · exact mul_ne_zero ((Matrix.isUnit_iff_isUnit_det S).mp hS).ne_zero
        ((Matrix.isUnit_iff_isUnit_det S).mp hS).ne_zero

end

#print axioms pencil_sigPos_eq_card_normalized_eigenvalues

end ErdosProblems.Erdos1049.PaperR20
