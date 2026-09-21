import ErdosProblems.Erdos1041.PaperTrinomial

/-!
# Erdős 1041: the whole all-degree monic-trinomial statement

The scalar Abel-control theorem already proves every root spoke, and the
geometric assembly already constructs the broken line with its exact
variation.  This file restores the outer universal quantifiers of the short
and long paper theorem in one declaration.
-/

noncomputable section

namespace ErdosProblems.Erdos1041.PaperTrinomialWholeR21

open Set
open ErdosProblems.Erdos1041.PaperCurve
open ErdosProblems.Erdos1041.PaperTrinomial

/-- Every zero of a Schur-stable monic trinomial has a safe radial segment,
and every distinct pair has the advertised continuous rectifiable broken-line
connection through the origin, with exact length `‖z₁‖ + ‖z₂‖ < 2`. -/
theorem all_degree_monic_trinomials_whole
    {n m : ℕ} (hm : 1 ≤ m) (hmn : m < n) {a b : ℂ}
    (hroots : ∀ z : ℂ, polynomialValue n m a b z = 0 → ‖z‖ < 1) :
    (∀ z : ℂ, polynomialValue n m a b z = 0 →
      ∀ t : ℝ, 0 ≤ t → t ≤ 1 →
        ‖polynomialValue n m a b ((t : ℂ) * z)‖ < 1) ∧
    ∀ z₁ z₂ : ℂ,
      polynomialValue n m a b z₁ = 0 →
      polynomialValue n m a b z₂ = 0 → z₁ ≠ z₂ →
      Continuous (hub z₁ 0 z₂) ∧
      hub z₁ 0 z₂ 0 = z₁ ∧ hub z₁ 0 z₂ 2 = z₂ ∧
      (∀ t ∈ Icc (0 : ℝ) 2,
        ‖polynomialValue n m a b (hub z₁ 0 z₂ t)‖ < 1) ∧
      BoundedVariationOn (hub z₁ 0 z₂) (Icc (0 : ℝ) 2) ∧
      (eVariationOn (hub z₁ 0 z₂) (Icc (0 : ℝ) 2)).toReal =
        ‖z₁‖ + ‖z₂‖ ∧
      (eVariationOn (hub z₁ 0 z₂) (Icc (0 : ℝ) 2)).toReal < 2 := by
  refine ⟨?_, ?_⟩
  · intro z hz t ht0 ht1
    exact all_spokes hm hmn hroots hz ht0 ht1
  · intro z₁ z₂ h₁ h₂ _hne
    exact complete_trinomial hm hmn hroots h₁ h₂

#print axioms all_degree_monic_trinomials_whole

end ErdosProblems.Erdos1041.PaperTrinomialWholeR21
