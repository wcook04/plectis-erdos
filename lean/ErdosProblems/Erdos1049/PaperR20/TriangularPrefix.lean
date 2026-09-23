import ErdosProblems.Erdos1049.PaperR20.TriangularCertificate

/-!
# Reuse one triangular witness at every leading rank

Upper triangularity makes restriction of M U to a leading square commute
with multiplication. Thus a single rank-eight witness can certify each
smaller determinant without repeating its polynomial entry calculations.
This generic infrastructure does not supply any particular witness equations.
-/

namespace ErdosProblems.Erdos1049.PaperR20

open Matrix
open scoped BigOperators

variable {R : Type*} [CommRing R] [IsDomain R]

theorem leading_submatrix_mul_upper {n N : ℕ} (hn : n ≤ N)
    (M U : Matrix (Fin N) (Fin N) R)
    (hU : ∀ i j, j < i → U i j = 0) :
    M.submatrix (Fin.castLE hn) (Fin.castLE hn) *
        U.submatrix (Fin.castLE hn) (Fin.castLE hn) =
      (M * U).submatrix (Fin.castLE hn) (Fin.castLE hn) := by
  ext i j
  simp only [Matrix.mul_apply, Matrix.submatrix_apply]
  apply Fintype.sum_of_injective (Fin.castLE hn) (Fin.castLE_injective hn)
  · intro k hk
    have hkn : n ≤ k.val := by
      by_contra h
      apply hk
      exact ⟨⟨k.val, by omega⟩, Fin.ext rfl⟩
    have hjk : Fin.castLE hn j < k := by
      change j.val < k.val
      omega
    rw [hU k (Fin.castLE hn j) hjk, mul_zero]
  · intro k
    rfl

/-- Prefixes inherit the same determinant sequence from one full witness. -/
theorem leading_determinant_of_triangular_certificate {N : ℕ}
    (M U : Matrix (Fin N) (Fin N) R) (D : ℕ → R)
    (h0 : D 0 = 1)
    (hU : ∀ i j, j < i → U i j = 0)
    (hMU : ∀ i j, i < j → (M * U) i j = 0)
    (hUdiag : ∀ i, U i i = D i.val)
    (hMUdiag : ∀ i, (M * U) i i = D (i.val + 1))
    (hprev : ∀ i : Fin N, D i.val ≠ 0)
    (n : ℕ) (hn : n ≤ N) :
    (M.submatrix (Fin.castLE hn) (Fin.castLE hn)).det = D n := by
  apply determinant_of_triangular_certificate
    (M.submatrix (Fin.castLE hn) (Fin.castLE hn))
    (U.submatrix (Fin.castLE hn) (Fin.castLE hn)) D h0
  · intro i j h
    exact hU (Fin.castLE hn i) (Fin.castLE hn j) h
  · intro i j h
    rw [leading_submatrix_mul_upper hn M U hU]
    exact hMU (Fin.castLE hn i) (Fin.castLE hn j) h
  · intro i
    exact hUdiag (Fin.castLE hn i)
  · intro i
    rw [leading_submatrix_mul_upper hn M U hU]
    exact hMUdiag (Fin.castLE hn i)
  · intro i
    exact hprev (Fin.castLE hn i)

#print axioms leading_determinant_of_triangular_certificate

end ErdosProblems.Erdos1049.PaperR20
