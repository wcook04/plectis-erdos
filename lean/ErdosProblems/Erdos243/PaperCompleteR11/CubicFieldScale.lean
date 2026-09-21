import Mathlib.FieldTheory.IntermediateField.Adjoin.Basic
import ErdosProblems.Erdos243.PaperCompleteR11.CubicFieldCoordinates
import ErdosProblems.Erdos243.PaperCompleteR11.CubicRationalScale

/-!
# Scale twelve from the actual irreducible cubic root field

Candidate source. Lean elaboration and the axiom audit are UNRUN.
The root field is the actual intermediate field ℚ(α). Its power basis,
dimension, rational coordinates and reduced scale parameter are constructed
from the irreducible polynomial and square-root hypotheses. No Chebotarev
prime-production result is needed for this algebraic implication; obtaining
the square-root hypothesis from reductions is a separate endpoint.
-/

namespace ErdosProblems.Erdos243.PaperCompleteR11

open Polynomial

noncomputable section

/-- A three-dimensional power basis is enough to compose the complete
algebraic scale argument. -/
theorem cubic_powerBasis_scale_twelve
    {K : Type*} [CommRing K] [Nontrivial K] [Algebra ℚ K]
    (pb : PowerBasis ℚ K) (hdim : pb.dim = 3)
    (m : ℕ) (c : ℚ) (hm : 0 < m) (hc : c = 1 ∨ c = -1)
    (hroot : pb.gen^3 = pb.gen - algebraMap ℚ K (6*c/(m : ℚ)))
    (hsquare : ∃ β : K, β^2 = pb.gen^2 - 1) : m = 12 := by
  obtain ⟨w, hw, heq⟩ := cubic_powerBasis_square_parameter pb hdim
    (6*c/(m : ℚ)) hroot hsquare
  exact cubic_scale_rational_classification m c w hm hc hw heq

/-- The actual paper implication: a square in ℚ(α), for an irreducible
T³−T+6c/m with c=±1, forces m=12. The ambient field may be arbitrary. -/
theorem cubic_root_field_scale_twelve
    {L : Type*} [Field L] [Algebra ℚ L]
    (m : ℕ) (c : ℚ) (hm : 0 < m) (hc : c = 1 ∨ c = -1)
    (α : L)
    (hirr : Irreducible (cubicScalePolynomial (6*c/(m : ℚ))))
    (hroot : α^3 = α - algebraMap ℚ L (6*c/(m : ℚ)))
    (hsquare : ∃ β : IntermediateField.adjoin ℚ ({α} : Set L),
      β^2 = (IntermediateField.AdjoinSimple.gen ℚ α)^2 - 1) : m = 12 := by
  let η : ℚ := 6*c/(m : ℚ)
  have heval : aeval α (cubicScalePolynomial η) = 0 := by
    simp only [cubicScalePolynomial, map_add, map_sub, map_pow,
      Polynomial.aeval_X, Polynomial.aeval_C]
    dsimp [η]
    linear_combination hroot
  have hint : IsIntegral ℚ α :=
    ⟨cubicScalePolynomial η, cubicScalePolynomial_monic η, heval⟩
  have hmin : cubicScalePolynomial η = minpoly ℚ α :=
    minpoly.eq_of_irreducible_of_monic hirr heval (cubicScalePolynomial_monic η)
  letI : Algebra ℚ (IntermediateField.adjoin ℚ ({α} : Set L)) :=
    (IntermediateField.adjoin ℚ ({α} : Set L)).algebra'
  let pb := IntermediateField.adjoin.powerBasis hint
  have hdim : pb.dim = 3 := by
    change (minpoly ℚ α).natDegree = 3
    rw [← hmin, cubicScalePolynomial_natDegree]
  have hgen : pb.gen^3 = pb.gen -
      algebraMap ℚ (IntermediateField.adjoin ℚ ({α} : Set L)) η := by
    apply Subtype.ext
    change α^3 = α - algebraMap ℚ L η
    exact hroot
  exact cubic_powerBasis_scale_twelve pb hdim m c hm hc hgen hsquare

/-- An ambient-field square root with explicit membership in ℚ(α) is the
same paper hypothesis, without requiring the caller to construct a subtype. -/
theorem cubic_scale_twelve_of_square_in_adjoin
    {L : Type*} [Field L] [Algebra ℚ L]
    (m : ℕ) (c : ℚ) (hm : 0 < m) (hc : c = 1 ∨ c = -1)
    (α β : L)
    (hirr : Irreducible (cubicScalePolynomial (6*c/(m : ℚ))))
    (hroot : α^3 = α - algebraMap ℚ L (6*c/(m : ℚ)))
    (hβmem : β ∈ IntermediateField.adjoin ℚ ({α} : Set L))
    (hβ : β^2 = α^2 - 1) : m = 12 := by
  apply cubic_root_field_scale_twelve m c hm hc α hirr hroot
  refine ⟨⟨β, hβmem⟩, ?_⟩
  apply Subtype.ext
  simpa using hβ

end
end ErdosProblems.Erdos243.PaperCompleteR11
