import ErdosProblems.Erdos1049.PaperR20.FinitePencil
import ErdosProblems.Erdos1049.PaperR20.PencilInterlacing
import ErdosProblems.Erdos1049.PaperR20.PencilSpectralInertia

/-!
# Ordered roots of consecutive symmetric definite pencils

This file separates two exact parts of the pencil interlacing argument.  First,
an elementary counting lemma turns threshold-count interlacing of two
antitone tuples into the usual pointwise inequalities.  Second, the
square-root congruence identifies the roots of a symmetric definite pencil,
with multiplicity, with the eigenvalues of a Hermitian matrix.

The remaining connection is deliberately explicit: the positive index of
`B - t A` must be identified with the number of normalized eigenvalues above
`t`.  That is a Sylvester-inertia lemma, rather than a nesting assertion about
the two independently normalized matrices.
-/

namespace ErdosProblems.Erdos1049.PaperR20

open Matrix Polynomial
open scoped BigOperators
-- `#s` is Mathlib's scoped notation for `Finset.card s`.
open scoped Finset

noncomputable section

/-- Threshold-count interlacing implies the usual non-strict interlacing of
two decreasing tuples.  Repetitions are retained: the counts use strict
thresholds, while the conclusion is non-strict. -/
theorem antitone_interlaces_of_card_gt_interlaces {n : ℕ}
    (large : Fin (n + 1) → ℝ) (small : Fin n → ℝ)
    (hlarge : Antitone large) (hsmall : Antitone small)
    (hcount : ∀ t : ℝ,
      #{j | t < small j} ≤ #{j | t < large j} ∧
      #{j | t < large j} ≤ #{j | t < small j} + 1) :
    ∀ i : Fin n, small i ≤ large i.castSucc ∧ large i.succ ≤ small i := by
  intro i
  constructor
  · by_contra hle
    have hlt : large i.castSucc < small i := lt_of_not_ge hle
    have hiSmall : i.val < #{j | large i.castSucc < small j} :=
      (Tuple.lt_card_gt_iff_apply_gt_of_antitone hsmall).2 hlt
    have hiLarge : ¬ i.val < #{j | large i.castSucc < large j} := by
      intro h
      have := (Tuple.lt_card_gt_iff_apply_gt_of_antitone hlarge (j := i.castSucc)).1
        (by rwa [Fin.val_castSucc])
      exact (lt_irrefl _ this)
    have hc := (hcount (large i.castSucc)).1
    omega
  · by_contra hle
    have hlt : small i < large i.succ := lt_of_not_ge hle
    have hiLarge : i.succ.val < #{j | small i < large j} :=
      (Tuple.lt_card_gt_iff_apply_gt_of_antitone hlarge).2 hlt
    have hiSmall : ¬ i.val < #{j | small i < small j} := by
      intro h
      have := (Tuple.lt_card_gt_iff_apply_gt_of_antitone hsmall).1 h
      exact (lt_irrefl _ this)
    have hc := (hcount (small i)).2
    simp only [Fin.val_succ] at hiLarge
    omega

/-- A positive-definite symmetric pencil is a nonzero scalar multiple of a
Hermitian characteristic polynomial.  Consequently this equality identifies
the complete root multisets, including every algebraic multiplicity. -/
theorem determinantPencil_roots_eq_normalized_eigenvalues
    {n : ℕ} {A B : Matrix (Fin n) (Fin n) ℝ}
    (hA : A.PosDef) (hB : B.IsHermitian) :
    ∃ (H : Matrix (Fin n) (Fin n) ℝ) (hH : H.IsHermitian),
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
  have hcongruence (x : ℝ) :
      x • A - B = Sᴴ * (x • (1 : Matrix (Fin n) (Fin n) ℝ) - H) * S := by
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
  refine ⟨H, hH, ?_⟩
  rw [hpoly, Polynomial.roots_C_mul]
  · exact hH.roots_charpoly_eq_eigenvalues₀
  · exact mul_ne_zero ((Matrix.isUnit_iff_isUnit_det S).mp hS).ne_zero
      ((Matrix.isUnit_iff_isUnit_det S).mp hS).ne_zero

/-- The exact original-coordinate information available for two consecutive
principal pencils: their positive indices interlace at every threshold and
both determinant polynomials carry their full normalized spectra as root
multisets.  No relation between the two normalization matrices is used. -/
theorem nested_pencils_inertia_and_root_multiplicity {n : ℕ}
    (A B : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ)
    (hA : A.PosDef) (hB : B.IsHermitian) :
    (∀ t : ℝ,
      _root_.sigPos
          (pencilQuadratic (A.submatrix Fin.castSucc Fin.castSucc)
            (B.submatrix Fin.castSucc Fin.castSucc) t) ≤
        _root_.sigPos (pencilQuadratic A B t) ∧
      _root_.sigPos (pencilQuadratic A B t) ≤
        _root_.sigPos
          (pencilQuadratic (A.submatrix Fin.castSucc Fin.castSucc)
            (B.submatrix Fin.castSucc Fin.castSucc) t) + 1) ∧
    (∃ (H : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ) (hH : H.IsHermitian),
      (determinantPencil A B).roots =
        Multiset.map (RCLike.ofReal ∘ hH.eigenvalues₀) Finset.univ.val) ∧
    (∃ (H : Matrix (Fin n) (Fin n) ℝ) (hH : H.IsHermitian),
      (determinantPencil (A.submatrix Fin.castSucc Fin.castSucc)
          (B.submatrix Fin.castSucc Fin.castSucc)).roots =
        Multiset.map (RCLike.ofReal ∘ hH.eigenvalues₀) Finset.univ.val) := by
  have hAprincipal : (A.submatrix Fin.castSucc Fin.castSucc).PosDef :=
    Matrix.PosDef.of_dotProduct_mulVec_pos (hA.1.submatrix Fin.castSucc) (by
      intro x hx
      have hy : Fin.snoc (α := fun _ => ℝ) x 0 ≠ 0 := by
        intro hy
        apply hx
        funext i
        have := congrFun hy i.castSucc
        simpa using this
      simpa only [Matrix.submatrix_apply, dotProduct, Matrix.mulVec,
        Fin.sum_univ_castSucc, Fin.snoc_last, Fin.snoc_castSucc, star_trivial,
        mul_zero, zero_mul, add_zero] using
          hA.dotProduct_mulVec_pos hy)
  have hBprincipal :
      (B.submatrix Fin.castSucc Fin.castSucc).IsHermitian := hB.submatrix Fin.castSucc
  exact ⟨principalPencil_sigPos_interlaces A B,
    determinantPencil_roots_eq_normalized_eigenvalues hA hB,
    determinantPencil_roots_eq_normalized_eigenvalues hAprincipal hBprincipal⟩

/-- Exact non-strict consecutive-rank interlacing for the roots of the
original nested symmetric definite pencils.  The displayed multiset
equalities record algebraic multiplicity; the ordered inequalities use the
antitone `eigenvalues₀` enumerations of those same multisets. -/
theorem nested_pencil_ordered_root_interlaces {n : ℕ}
    (A B : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ)
    (hA : A.PosDef) (hB : B.IsHermitian) :
    ∃ (Hlarge : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ)
        (hHlarge : Hlarge.IsHermitian)
        (Hsmall : Matrix (Fin n) (Fin n) ℝ)
        (hHsmall : Hsmall.IsHermitian),
      (determinantPencil A B).roots =
          Multiset.map (RCLike.ofReal ∘ hHlarge.eigenvalues₀) Finset.univ.val ∧
      (determinantPencil (A.submatrix Fin.castSucc Fin.castSucc)
          (B.submatrix Fin.castSucc Fin.castSucc)).roots =
          Multiset.map (RCLike.ofReal ∘ hHsmall.eigenvalues₀) Finset.univ.val ∧
      ∀ i : Fin n,
        hHsmall.eigenvalues₀ (Fin.cast (Fintype.card_fin n).symm i) ≤
            hHlarge.eigenvalues₀ (Fin.cast (Fintype.card_fin (n + 1)).symm i.castSucc) ∧
        hHlarge.eigenvalues₀ (Fin.cast (Fintype.card_fin (n + 1)).symm i.succ) ≤
            hHsmall.eigenvalues₀ (Fin.cast (Fintype.card_fin n).symm i) := by
  have hAprincipal : (A.submatrix Fin.castSucc Fin.castSucc).PosDef :=
    Matrix.PosDef.of_dotProduct_mulVec_pos (hA.1.submatrix Fin.castSucc) (by
      intro x hx
      have hy : Fin.snoc (α := fun _ => ℝ) x 0 ≠ 0 := by
        intro hy
        apply hx
        funext i
        have := congrFun hy i.castSucc
        simpa using this
      simpa only [Matrix.submatrix_apply, dotProduct, Matrix.mulVec,
        Fin.sum_univ_castSucc, Fin.snoc_last, Fin.snoc_castSucc, star_trivial,
        mul_zero, zero_mul, add_zero] using
          hA.dotProduct_mulVec_pos hy)
  have hBprincipal :
      (B.submatrix Fin.castSucc Fin.castSucc).IsHermitian := hB.submatrix Fin.castSucc
  obtain ⟨Hlarge, hHlarge, hcountLarge, hrootsLarge⟩ :=
    pencil_sigPos_eq_card_normalized_eigenvalues A B hA hB
  obtain ⟨Hsmall, hHsmall, hcountSmall, hrootsSmall⟩ :=
    pencil_sigPos_eq_card_normalized_eigenvalues
      (A.submatrix Fin.castSucc Fin.castSucc)
      (B.submatrix Fin.castSucc Fin.castSucc) hAprincipal hBprincipal
  refine ⟨Hlarge, hHlarge, Hsmall, hHsmall, hrootsLarge, hrootsSmall, ?_⟩
  have hcount_cast : ∀ {k m : ℕ} (h : m = k) (f : Fin k → ℝ) (t : ℝ),
      #{j : Fin m | t < f (Fin.cast h j)} = {i : Fin k | t < f i}.ncard := by
    intro k m h f t
    subst h
    rw [← Set.ncard_coe_finset]
    congr 1
    ext i
    simp
  have hanti_cast : ∀ {k m : ℕ} (h : m = k) (f : Fin k → ℝ), Antitone f →
      Antitone (fun j : Fin m => f (Fin.cast h j)) :=
    fun h _ hf => hf.comp_monotone (Fin.cast_strictMono h).monotone
  apply antitone_interlaces_of_card_gt_interlaces
    (fun j => hHlarge.eigenvalues₀ (Fin.cast (Fintype.card_fin (n + 1)).symm j))
    (fun j => hHsmall.eigenvalues₀ (Fin.cast (Fintype.card_fin n).symm j))
    (hanti_cast _ _ hHlarge.eigenvalues₀_antitone)
    (hanti_cast _ _ hHsmall.eigenvalues₀_antitone)
  intro t
  have hsig := principalPencil_sigPos_interlaces A B t
  rw [hcountLarge t, hcountSmall t] at hsig
  rw [hcount_cast (Fintype.card_fin n).symm, hcount_cast (Fintype.card_fin (n + 1)).symm]
  exact hsig

end

#print axioms nested_pencils_inertia_and_root_multiplicity
#print axioms nested_pencil_ordered_root_interlaces

end ErdosProblems.Erdos1049.PaperR20
