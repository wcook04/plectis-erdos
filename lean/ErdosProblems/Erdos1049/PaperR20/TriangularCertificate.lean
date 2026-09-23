import Mathlib

/-!
# Small exact determinant certificates by triangular multiplication

A certificate supplies an upper triangular matrix U. Checking the entries on
and above the diagonal of M U proves the claimed determinant by det_mul.
The certificate producer need not be trusted, and no elimination algorithm or
division is used by the verifier. Candidate proof; kernel validation pending.
-/

namespace ErdosProblems.Erdos1049.PaperR20

open Matrix
open scoped BigOperators

variable {R : Type*} [CommRing R] [IsDomain R]

private theorem shifted_diagonal_product (D : ℕ → R) (h0 : D 0 = 1) :
    ∀ n : ℕ, (∏ i : Fin n, D (i.val + 1)) = (∏ i : Fin n, D i.val) * D n := by
  intro n
  induction n with
  | zero => simp [h0]
  | succ n ih =>
      simp only [Fin.prod_univ_castSucc, Fin.val_castSucc, Fin.val_last]
      rw [ih]

/-- Every premise is either a scalar polynomial identity, a zero entry, or a
nonzero previously certified determinant. The witness U may come from any
producer; the conclusion refers to the original literal matrix M. -/
theorem determinant_of_triangular_certificate {n : ℕ}
    (M U : Matrix (Fin n) (Fin n) R) (D : ℕ → R)
    (h0 : D 0 = 1)
    (hU : ∀ i j, j < i → U i j = 0)
    (hMU : ∀ i j, i < j → (M * U) i j = 0)
    (hUdiag : ∀ i, U i i = D i.val)
    (hMUdiag : ∀ i, (M * U) i i = D (i.val + 1))
    (hprev : ∀ i : Fin n, D i.val ≠ 0) : M.det = D n := by
  have hupper : U.BlockTriangular id := fun i j h => hU i j h
  have hlower : (M * U).BlockTriangular OrderDual.toDual := fun i j h => hMU i j h
  have hdetU : U.det = ∏ i : Fin n, D i.val := by
    rw [Matrix.det_of_upperTriangular hupper]
    simp only [hUdiag]
  have hdetMU : (M * U).det = ∏ i : Fin n, D (i.val + 1) := by
    rw [Matrix.det_of_lowerTriangular (M * U) hlower]
    simp only [hMUdiag]
  have hprod : (∏ i : Fin n, D i.val) ≠ 0 :=
    Finset.prod_ne_zero_iff.mpr (fun i _ => hprev i)
  apply mul_right_cancel₀ hprod
  calc
    M.det * (∏ i : Fin n, D i.val) = (M * U).det := by
      rw [← hdetU, Matrix.det_mul]
    _ = (∏ i : Fin n, D i.val) * D n := by
      rw [hdetMU, shifted_diagonal_product D h0]
    _ = D n * (∏ i : Fin n, D i.val) := mul_comm _ _

#print axioms determinant_of_triangular_certificate

end ErdosProblems.Erdos1049.PaperR20
