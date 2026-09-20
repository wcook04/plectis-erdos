import ErdosProblems.Erdos243.PaperCompleteR11.CubicFieldScale

/-!
# Erdős 243: literal classification of the scales

This is the exact whole-statement adapter for long-paper
`long243:res:scaletwelve`.  The sign is an integer `c ∈ {-1,1}`, the cubic is
`T^3-T+6c/m`, irreducibility is over `ℚ`, and the square root is required to
belong to `ℚ(α)`.
-/

noncomputable section

namespace ErdosProblems.Erdos243.PaperCompleteR20

open Polynomial
open ErdosProblems.Erdos243.PaperCompleteR11

/-- Literal long-paper `long243:res:scaletwelve`: the square condition in the
irreducible cubic root field forces the positive integral scale to be twelve. -/
theorem scale_twelve
    {L : Type*} [Field L] [Algebra ℚ L]
    (m : ℕ) (c : ℤ) (hm : 0 < m) (hc : c = 1 ∨ c = -1)
    (α β : L)
    (hirr : Irreducible
      (cubicScalePolynomial (6 * (c : ℚ) / (m : ℚ))))
    (hroot : α ^ 3 = α -
      algebraMap ℚ L (6 * (c : ℚ) / (m : ℚ)))
    (hβmem : β ∈ IntermediateField.adjoin ℚ ({α} : Set L))
    (hβ : β ^ 2 = α ^ 2 - 1) :
    m = 12 := by
  apply cubic_scale_twelve_of_square_in_adjoin m (c : ℚ) hm
    (by rcases hc with rfl | rfl <;> simp) α β hirr hroot hβmem hβ

/-- Equivalent existential spelling of “`α²-1` is a square in `ℚ(α)`”. -/
theorem scale_twelve_of_square_in_rootField
    {L : Type*} [Field L] [Algebra ℚ L]
    (m : ℕ) (c : ℤ) (hm : 0 < m) (hc : c = 1 ∨ c = -1)
    (α : L)
    (hirr : Irreducible
      (cubicScalePolynomial (6 * (c : ℚ) / (m : ℚ))))
    (hroot : α ^ 3 = α -
      algebraMap ℚ L (6 * (c : ℚ) / (m : ℚ)))
    (hsquare : ∃ β : L,
      β ∈ IntermediateField.adjoin ℚ ({α} : Set L) ∧
      β ^ 2 = α ^ 2 - 1) :
    m = 12 := by
  obtain ⟨β, hβmem, hβ⟩ := hsquare
  exact scale_twelve m c hm hc α β hirr hroot hβmem hβ

#print axioms ErdosProblems.Erdos243.PaperCompleteR20.scale_twelve
#print axioms ErdosProblems.Erdos243.PaperCompleteR20.scale_twelve_of_square_in_rootField

end ErdosProblems.Erdos243.PaperCompleteR20
