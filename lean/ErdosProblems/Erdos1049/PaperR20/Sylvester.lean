import Mathlib

/-!
# Positive leading determinants imply positive definiteness

This supplies the finite-dimensional criterion needed to turn the literal
#1049 coefficient-Hankel determinant certificates into positive definiteness.
The proof adds one coordinate at a time and uses a one-dimensional Schur
complement. No determinant positivity is assumed implicitly.

Candidate proof: kernel and axiom validation are pending.
-/

namespace ErdosProblems.Erdos1049.PaperR20

open Matrix

noncomputable section

private theorem posDef_one_coordinate_extension
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    {A : Matrix ι ι ℝ} (hA : A.PosDef)
    (B : Matrix ι (Fin 1) ℝ) (D : Matrix (Fin 1) (Fin 1) ℝ)
    (hdet : 0 < (Matrix.fromBlocks A B Bᴴ D).det) :
    (Matrix.fromBlocks A B Bᴴ D).PosDef := by
  letI := hA.isUnit.invertible
  let S := D - Bᴴ * A⁻¹ * B
  have hsdet : 0 < S.det := by
    apply (mul_pos_iff_of_pos_left hA.det_pos).mp
    simpa only [Matrix.det_fromBlocks₁₁, Matrix.invOf_eq_nonsing_inv] using hdet
  have hs : 0 < S 0 0 := by simpa only [Matrix.det_fin_one] using hsdet
  have hdiag : S = Matrix.diagonal (fun _ : Fin 1 => S 0 0) := by
    ext i j
    have hi : i = 0 := Subsingleton.elim _ _
    have hj : j = 0 := Subsingleton.elim _ _
    subst i
    subst j
    simp
  have hS : S.PosSemidef := by
    rw [hdiag]
    exact Matrix.PosSemidef.diagonal (fun _ => hs.le)
  have hPSD : (Matrix.fromBlocks A B Bᴴ D).PosSemidef :=
    (hA.fromBlocks₁₁ B D).mpr hS
  apply hPSD.posDef_iff_isUnit.mpr
  exact (Matrix.isUnit_iff_isUnit_det _).mpr (isUnit_iff_ne_zero.mpr hdet.ne')

/-- The first k rows and columns, retaining their original coordinate order. -/
def leadingPrincipalMatrix {n : ℕ} (M : Matrix (Fin n) (Fin n) ℝ)
    (k : ℕ) (hk : k ≤ n) : Matrix (Fin k) (Fin k) ℝ :=
  M.submatrix (Fin.castLE hk) (Fin.castLE hk)

/-- Sylvester's sufficient criterion, with every nonempty leading minor
explicitly required. The empty matrix is included without a spurious premise. -/
theorem posDef_of_positive_leading_determinants :
    ∀ n : ℕ, ∀ M : Matrix (Fin n) (Fin n) ℝ,
      M.IsHermitian →
      (∀ k : ℕ, ∀ hk : k ≤ n, 0 < k →
        0 < (leadingPrincipalMatrix M k hk).det) → M.PosDef := by
  intro n
  induction n with
  | zero =>
      intro M hM hdet
      apply Matrix.PosDef.of_dotProduct_mulVec_pos hM
      intro x hx
      exact (hx (by ext i; exact Fin.elim0 i)).elim
  | succ n ih =>
      intro M hM hdet
      let e : Fin n ⊕ Fin 1 ≃ Fin (n + 1) := finSumFinEquiv
      let A : Matrix (Fin n) (Fin n) ℝ :=
        M.submatrix (fun i => e (Sum.inl i)) (fun i => e (Sum.inl i))
      let B : Matrix (Fin n) (Fin 1) ℝ :=
        M.submatrix (fun i => e (Sum.inl i)) (fun j => e (Sum.inr j))
      let D : Matrix (Fin 1) (Fin 1) ℝ :=
        M.submatrix (fun i => e (Sum.inr i)) (fun j => e (Sum.inr j))
      have hA : A.PosDef := by
        apply ih A (hM.submatrix _)
        intro k hk hkpos
        have heq : leadingPrincipalMatrix A k hk =
            leadingPrincipalMatrix M k (hk.trans (Nat.le_succ n)) := by
          ext i j
          rfl
        rw [heq]
        exact hdet k _ hkpos
      have hblocks : M.submatrix e e = Matrix.fromBlocks A B Bᴴ D := by
        ext i j
        rcases i with i | i <;> rcases j with j | j
        · rfl
        · rfl
        · exact (hM.apply (e (Sum.inr i)) (e (Sum.inl j))).symm
        · rfl
      have hMdet : 0 < M.det := by
        simpa [leadingPrincipalMatrix] using hdet (n + 1) le_rfl (Nat.succ_pos n)
      have hblockdet : 0 < (Matrix.fromBlocks A B Bᴴ D).det := by
        rw [← hblocks, Matrix.det_submatrix_equiv_self]
        exact hMdet
      have hblock := posDef_one_coordinate_extension hA B D hblockdet
      have hPSD : M.PosSemidef := by
        rw [← hblocks] at hblock
        simpa only [Matrix.submatrix_submatrix, e.self_comp_symm, Matrix.submatrix_id_id]
          using hblock.posSemidef.submatrix e.symm
      apply hPSD.posDef_iff_isUnit.mpr
      exact (Matrix.isUnit_iff_isUnit_det _).mpr (isUnit_iff_ne_zero.mpr hMdet.ne')

#print axioms posDef_of_positive_leading_determinants

end
end ErdosProblems.Erdos1049.PaperR20
