import ErdosProblems.Erdos257.PaperCompleteR8.AnalyticSeparationReturn
import ErdosProblems.Erdos257.PaperCompleteR8.ReverseStrengthenedHost
import ErdosProblems.Erdos257.PaperCompleteR8.WeightedHereditaryClaim

/-!
# Existential endpoints for the weighted and strengthened-cover classes

These are the complete existential statements of short-paper
`res:weighted-cover-incomparability` and `res:strict-mixed-supports`.
The reverse witness is `reverseHost`, constructed by a different row schedule
from the paper's printed bounded-mass fresh-prime construction. The theorem
proves the same existence claim; it does not formalise that particular
construction or its quantitative row bounds.

The union argument uses downward closure of each sufficient class. Its
irrationality conclusion comes from the common-scale mixed theorem, not from
adding irrational numbers. Universal Erdős Problem 257 remains open.

Check this module and its transitive imports with the pinned toolchain:
`python3 scripts/lean_fast_build.py --jobs 2
ErdosProblems.Erdos257.PaperCompleteR8.PaperIncomparabilityEndpoints`.
The two `#print axioms` commands below report the endpoint dependencies.
Source availability alone does not establish a public build or Comparator result.
-/

noncomputable section
namespace ErdosProblems.Erdos257.PaperCompleteR8
open ErdosProblems.Erdos257.PaperCompleteR7
open Erdos249257

/-- The full existential statement of `res:weighted-cover-incomparability`,
including divergence of the reciprocal sum on the cover-only witness. -/
theorem paper_weighted_cover_incomparability :
    ∃ E V : Set ℕ,
      E.Infinite ∧ V.Infinite ∧ 0 ∉ E ∧ 0 ∉ V ∧
      FinitePrimeWeighted 2 E ∧ ¬ HasStrengthenedPositiveCover E ∧
      HasStrengthenedPositiveCover V ∧
      (∀ b : ℕ, 2 ≤ b → ¬ FinitePrimeWeighted b V) ∧
      ¬ Summable (Set.indicator V (fun a : ℕ => (1 : ℝ) / a)) := by
  obtain ⟨E, hEi, hE0, hEw, _, hEc, _, _⟩ :=
    exists_weighted_not_strengthened_host
  exact ⟨E, reverseHost, hEi, reverseHost_infinite, hE0, reverseHost_positive,
    hEw, hEc, reverseHost_has_strengthened_cover,
    reverseHost_not_finitePrimeWeighted, reverseHost_reciprocal_not_summable⟩

/-- The full existential statement of `res:strict-mixed-supports`.
The union of the actual witnesses requires the mixed criterion: a cover of
the union would cover `E`, and a weighted witness for the union would
restrict to `V`. The mixed theorem gives every infinite subhost's
irrationality at every integer base at least two. -/
theorem paper_strict_mixed_supports :
    ∃ U : Set ℕ, U.Infinite ∧ 0 ∉ U ∧
      ¬ HasStrengthenedPositiveCover U ∧
      (∀ b : ℕ, 2 ≤ b → ¬ FinitePrimeWeighted b U) ∧
      (∀ A : Set ℕ, A ⊆ U → A.Infinite → ∀ b : ℕ, 2 ≤ b →
        Irrational (erdosSupportSeries b A)) := by
  obtain ⟨E, V, hEi, _, hE0, hV0, hEw, hEc, hVc, hVw, _⟩ :=
    paper_weighted_cover_incomparability
  refine ⟨E ∪ V, hEi.mono Set.subset_union_left, ?_, ?_, ?_, ?_⟩
  · rintro (hE | hV)
    · exact hE0 hE
    · exact hV0 hV
  · rintro ⟨C, hUC, hC⟩
    exact hEc ⟨C, fun a ha => hUC (Or.inl ha), hC⟩
  · intro b hb hUw
    exact hVw b hb (finitePrimeWeighted_subset b hb Set.subset_union_right hUw)
  · exact mixedSupportClaim E V hE0 hEw hVc

#print axioms paper_weighted_cover_incomparability
#print axioms paper_strict_mixed_supports

end ErdosProblems.Erdos257.PaperCompleteR8
end
