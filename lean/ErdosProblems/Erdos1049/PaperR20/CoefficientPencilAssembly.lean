import ErdosProblems.Erdos1049.PaperR20.CoefficientPencil
import ErdosProblems.Erdos1049.PaperR20.Sylvester
import ErdosProblems.Erdos1049.PaperR20.PencilRootInterlacing
import ErdosProblems.Erdos1049.ActualPositiveMeasureR16
import ErdosProblems.Erdos1049.PaperR16.LambertBasic

/-!
# Assembly of the literal coefficient pencil

The paper's coefficient matrices are used throughout.  The finite certificate
inputs are precisely positive leading Hankel determinants and the remainder
identity at the moment indices occurring in the selected matrix.  Neither
input is silently assumed to hold at every rank.

The positive-definiteness result for the actual remainder moments, by contrast,
holds at every rank and uses the existing positive discrete measure theorem.

Proof candidates: kernel and axiom validation are pending.
-/

namespace ErdosProblems.Erdos1049.PaperR20

open Matrix Polynomial

noncomputable section

/-- All ranks of the actual source moment matrix are positive definite. -/
theorem actualMomentHankel_posDef {q : ℝ} (hq0 : 0 < q) (hq1 : q < 1)
    (N : ℕ) : (PaperR16.actualMomentHankel q N).PosDef := by
  apply posDef_of_positive_leading_determinants N
  · ext i j
    simp [Matrix.conjTranspose_apply, PaperR16.actualMomentHankel, Nat.add_comm]
  · intro k hk _
    change 0 < (PaperR16.actualMomentHankel q k).det
    exact PaperR16.actualMomentHankel_det_pos hq0 hq1 k

/-- Leading determinant certificates imply positivity of the literal moment
matrix.  No certificate for a larger rank is required. -/
theorem coefficientMomentMatrix_posDef_of_determinants (p : ℝ) (N : ℕ)
    (hdet : ∀ k : ℕ, k ≤ N → 0 < k →
      0 < (coefficientHankelDetPoly k 0).eval₂ (Int.castRingHom ℝ) p) :
    (coefficientMomentMatrix p N).PosDef := by
  apply posDef_of_positive_leading_determinants N
  · ext i j
    simp [Matrix.conjTranspose_apply, coefficientMomentMatrix, Nat.add_comm]
  · intro k hk hk0
    have h := hdet k hk hk0
    rw [coefficientHankelDetPoly_eval] at h
    simpa only [Nat.add_zero] using h

/-- The positive diagonal congruence transfers the checked moment determinants
to the paper's alpha matrix. -/
theorem coefficientAlphaMatrix_posDef_of_determinants {p : ℝ} (hp : 1 < p)
    (N : ℕ)
    (hdet : ∀ k : ℕ, k ≤ N → 0 < k →
      0 < (coefficientHankelDetPoly k 0).eval₂ (Int.castRingHom ℝ) p) :
    (coefficientAlphaMatrix p N).PosDef := by
  have hM := coefficientMomentMatrix_posDef_of_determinants p N hdet
  have hD : Function.Injective (coefficientDiagonal p N).mulVec := by
    intro x y hxy
    funext i
    have hi := congrFun hxy i
    simp only [coefficientDiagonal, Matrix.mulVec_diagonal] at hi
    exact mul_left_cancel₀ (coefficientDiagonal_entry_pos hp i.val).ne' hi
  have hconj : (coefficientDiagonal p N)ᴴ = coefficientDiagonal p N := by
    simp [coefficientDiagonal]
  rw [coefficientAlphaMatrix_diagonal_congruence]
  apply Matrix.PosDef.smul _ (lt_trans zero_lt_one hp)
  simpa only [hconj] using hM.conjTranspose_mul_mul_same hD

/-- The only remainder identities needed for rank N are the entries i+j.
This formulation includes rank zero without natural-subtraction edge cases. -/
theorem coefficientPencil_remainder_matrix (p : ℝ) (N : ℕ)
    (hremainder : ∀ i j : Fin N,
      PaperR12.actualMoment p⁻¹ (i.val + j.val) =
        coefficientAlpha p (i.val + j.val) * PaperR16.lambert p⁻¹ -
          coefficientBeta p (i.val + j.val)) :
    PaperR16.lambert p⁻¹ • coefficientAlphaMatrix p N -
        coefficientBetaMatrix p N = PaperR16.actualMomentHankel p⁻¹ N := by
  ext i j
  simpa only [coefficientAlphaMatrix, coefficientBetaMatrix,
    PaperR16.actualMomentHankel, Matrix.sub_apply, Matrix.smul_apply,
    Matrix.of_apply, smul_eq_mul, mul_comm] using (hremainder i j).symm

/-- The complete finite-rank spectral conclusion, conditional only on its
explicit determinant and remainder certificates.  Splitting asserts that all
roots are real; the strict bound applies to every root. -/
theorem coefficientPencil_splits_and_roots_lt_of_certificates {p : ℝ}
    (hp : 1 < p) (N : ℕ)
    (hdet : ∀ k : ℕ, k ≤ N → 0 < k →
      0 < (coefficientHankelDetPoly k 0).eval₂ (Int.castRingHom ℝ) p)
    (hremainder : ∀ i j : Fin N,
      PaperR12.actualMoment p⁻¹ (i.val + j.val) =
        coefficientAlpha p (i.val + j.val) * PaperR16.lambert p⁻¹ -
          coefficientBeta p (i.val + j.val)) :
    (coefficientAlphaMatrix p N).PosDef ∧
    (coefficientPencilPoly p N).Splits ∧
      ∀ x : ℝ, (coefficientPencilPoly p N).IsRoot x →
        x < PaperR16.lambert p⁻¹ := by
  have hA := coefficientAlphaMatrix_posDef_of_determinants hp N hdet
  have hB : (coefficientBetaMatrix p N).IsHermitian := by
    ext i j
    simp [Matrix.conjTranspose_apply, coefficientBetaMatrix, Nat.add_comm]
  have hR : (PaperR16.lambert p⁻¹ • coefficientAlphaMatrix p N -
      coefficientBetaMatrix p N).PosDef := by
    rw [coefficientPencil_remainder_matrix p N hremainder]
    exact actualMomentHankel_posDef (inv_pos.mpr (lt_trans zero_lt_one hp))
      ((inv_lt_one₀ (lt_trans zero_lt_one hp)).mpr hp) N
  exact ⟨hA, determinantPencil_splits_and_roots_lt hA hB hR⟩

/-- Consecutive literal coefficient pencils interlace whenever the larger
alpha matrix has its positive leading determinant certificates.  The root
multisets retain every algebraic multiplicity. -/
theorem coefficientPencil_interlaces_of_certificates {p : ℝ} (hp : 1 < p)
    (N : ℕ)
    (hdet : ∀ k : ℕ, k ≤ N + 1 → 0 < k →
      0 < (coefficientHankelDetPoly k 0).eval₂ (Int.castRingHom ℝ) p) :
    ∃ (large : Fin (N + 1) → ℝ) (small : Fin N → ℝ),
      Antitone large ∧ Antitone small ∧
      (coefficientPencilPoly p (N + 1)).roots =
        Multiset.map large Finset.univ.val ∧
      (coefficientPencilPoly p N).roots =
        Multiset.map small Finset.univ.val ∧
      ∀ i : Fin N, small i ≤ large i.castSucc ∧ large i.succ ≤ small i := by
  have hA := coefficientAlphaMatrix_posDef_of_determinants hp (N + 1) hdet
  have hB : (coefficientBetaMatrix p (N + 1)).IsHermitian := by
    ext i j
    simp [Matrix.conjTranspose_apply, coefficientBetaMatrix, Nat.add_comm]
  obtain ⟨Hlarge, hHlarge, Hsmall, hHsmall, hlarge, hsmall, hinterlace⟩ :=
    nested_pencil_ordered_root_interlaces
      (coefficientAlphaMatrix p (N + 1)) (coefficientBetaMatrix p (N + 1)) hA hB
  -- `eigenvalues₀` is indexed by `Fin (Fintype.card (Fin k))`, which is only
  -- propositionally `Fin k`; reindex along `Fintype.card_fin` by `Fin.cast`.
  have hreindex : ∀ {k m : ℕ} (h : m = k) (f : Fin k → ℝ),
      Multiset.map (fun j : Fin m => f (Fin.cast h j)) Finset.univ.val =
        Multiset.map f Finset.univ.val := by
    intro k m h f
    subst h
    simp
  have hanti_cast : ∀ {k m : ℕ} (h : m = k) (f : Fin k → ℝ), Antitone f →
      Antitone (fun j : Fin m => f (Fin.cast h j)) :=
    fun h _ hf => hf.comp_monotone (Fin.cast_strictMono h).monotone
  refine ⟨fun j => hHlarge.eigenvalues₀ (Fin.cast (Fintype.card_fin (N + 1)).symm j),
    fun j => hHsmall.eigenvalues₀ (Fin.cast (Fintype.card_fin N).symm j),
    hanti_cast _ _ hHlarge.eigenvalues₀_antitone,
    hanti_cast _ _ hHsmall.eigenvalues₀_antitone, ?_, ?_, hinterlace⟩
  · rw [hreindex (Fintype.card_fin (N + 1)).symm hHlarge.eigenvalues₀]
    simpa only [RCLike.ofReal_real_eq_id, Function.id_comp] using hlarge
  · rw [hreindex (Fintype.card_fin N).symm hHsmall.eigenvalues₀]
    simpa only [RCLike.ofReal_real_eq_id, Function.id_comp] using hsmall

#print axioms actualMomentHankel_posDef
#print axioms coefficientPencil_splits_and_roots_lt_of_certificates
#print axioms coefficientPencil_interlaces_of_certificates

end
end ErdosProblems.Erdos1049.PaperR20
