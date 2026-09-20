import Mathlib.LinearAlgebra.QuadraticForm.Signature
import Mathlib.Data.Real.Basic

/-!
# Positive inertia under restriction

The positive index of a real quadratic form cannot increase under restriction.
Restriction to a hyperplane can lower it by at most one.  This is the exact
linear-algebra input needed for interlacing of nested symmetric definite
matrix pencils; it is stated without choosing any normalization of the forms.
-/

namespace ErdosProblems.Erdos1049.PaperR20

open Module QuadraticMap

noncomputable section

variable {V : Type*} [AddCommGroup V] [Module ℝ V] [FiniteDimensional ℝ V]

/-- Restricting a quadratic form to a subspace cannot increase its positive
index. -/
theorem sigPos_restrict_le (Q : QuadraticForm ℝ V) (W : Submodule ℝ V) :
    _root_.sigPos (Q.restrict W) ≤ _root_.sigPos Q := by
  obtain ⟨U, hUdim, hUpos⟩ := _root_.exists_finrank_eq_sigPos_and_posDef (Q.restrict W)
  let f : U →ₗ[ℝ] V := W.subtype.comp U.subtype
  have hf : Function.Injective f := W.injective_subtype.comp U.injective_subtype
  let R : Submodule ℝ V := LinearMap.range f
  have hRdim : finrank ℝ R = finrank ℝ U := LinearMap.finrank_range_of_inj hf
  have hRpos : (Q.restrict R).PosDef := by
    rintro ⟨x, hx⟩ hx0
    rcases hx with ⟨y, rfl⟩
    have hy0 : y ≠ 0 := by
      intro hy
      apply hx0
      subst y
      rfl
    simpa [f] using hUpos y hy0
  rw [← hUdim, ← hRdim]
  exact _root_.le_sigPos_of_posDef Q hRpos

/-- Restriction to a codimension-one subspace changes the positive index by
at most one. -/
theorem sigPos_restrict_codim_one (Q : QuadraticForm ℝ V) (W : Submodule ℝ V)
    (hcodim : finrank ℝ W + 1 = finrank ℝ V) :
    _root_.sigPos (Q.restrict W) ≤ _root_.sigPos Q ∧
      _root_.sigPos Q ≤ _root_.sigPos (Q.restrict W) + 1 := by
  refine ⟨sigPos_restrict_le Q W, ?_⟩
  obtain ⟨P, hPdim, hPpos⟩ := _root_.exists_finrank_eq_sigPos_and_posDef Q
  let U : Submodule ℝ W := P.comap W.subtype
  have hUpos : ((Q.restrict W).restrict U).PosDef := by
    intro x hx
    have hxP : (⟨x.1.1, x.2⟩ : P) ≠ 0 := by
      intro hz
      apply hx
      apply Subtype.ext
      apply Subtype.ext
      exact congrArg (fun y : P => (y : V)) hz
    simpa [U] using hPpos ⟨x.1.1, x.2⟩ hxP
  have hUle : finrank ℝ U ≤ _root_.sigPos (Q.restrict W) :=
    _root_.le_sigPos_of_posDef (Q.restrict W) hUpos
  have hUdim : finrank ℝ U = finrank ℝ ↥(P ⊓ W : Submodule ℝ V) := by
    rw [← Submodule.finrank_map_subtype_eq W U]
    dsimp only [U]
    rw [Submodule.map_comap_subtype, inf_comm]
  have hsum := Submodule.finrank_sup_add_finrank_inf_eq P W
  have hsup : finrank ℝ ↥(P ⊔ W : Submodule ℝ V) ≤ finrank ℝ V := (P ⊔ W).finrank_le
  have hdim : finrank ℝ P + finrank ℝ W ≤
      finrank ℝ V + finrank ℝ ↥(P ⊓ W : Submodule ℝ V) := by
    rw [← hsum]
    exact Nat.add_le_add_right hsup _
  omega

end

end ErdosProblems.Erdos1049.PaperR20
