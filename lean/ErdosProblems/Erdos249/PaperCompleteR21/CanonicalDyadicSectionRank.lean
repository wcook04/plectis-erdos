import Erdos249257.TotientMahlerDefect

/-! Paper-form restatement of `prop:D4-inv`, the independence of the retained
dyadic family:

* the auxiliary canonical dyadic family at level `e` has `2^e + 1` indexed
  sections, and those sections are linearly independent over `ℚ`;
* for `e ≥ 1` the family is a basis for all sections through level `e` (it is
  independent and spans exactly that submodule, whose rank is `2^e + 1`);
* at `e = 0` the auxiliary family still carries both `φ(n)` and `φ(2n)`, so it
  is not the actual level-zero truncation, whose dimension is one.

No hypothesis on `S` appears anywhere below. -/
namespace ErdosProblems.Erdos249.PaperCompleteR21

open Erdos249257
open Module

/-- **The index count.**  The canonical family at level `e` has `2^e + 1`
indexed sections. -/
theorem card_canonical_dyadic_index (e : ℕ) :
    Fintype.card (TotientCanonicalIndex e) = 2 ^ e + 1 :=
  card_totientCanonicalIndex e

/-- **Independence.**  Those sections are linearly independent over `ℚ`. -/
theorem linearIndependent_canonical_dyadic_family (e : ℕ) :
    LinearIndependent ℚ (canonicalTotientKernelFamily e) :=
  linearIndependent_canonicalTotientKernelFamily e

/-- **A basis through level `e ≥ 1`.**  The canonical family is independent,
its span is the span of every dyadic section through level `e`, and that
span has rank `2^e + 1`. -/
theorem canonical_family_basis_through_level (e : ℕ) (he : 1 ≤ e) :
    LinearIndependent ℚ (canonicalTotientKernelFamily e) ∧
      Submodule.span ℚ (Set.range (canonicalTotientKernelFamily e)) =
        Submodule.span ℚ (Set.range (totientKernelThroughLevelFamily e)) ∧
      finrank ℚ
          (Submodule.span ℚ (Set.range (totientKernelThroughLevelFamily e))) =
        2 ^ e + 1 :=
  ⟨linearIndependent_canonicalTotientKernelFamily e,
    (span_totientKernelThroughLevelFamily_eq_canonical e he).symm,
    finrank_totientKernelThroughLevelFamily_eq e he⟩

/-- At `e = 0` the auxiliary family still contains both `φ(n)` and `φ(2n)`,
so it has two channels. -/
theorem canonical_level_zero_channels :
    canonicalTotientKernelFamily 0 (Sum.inl 0) =
        (fun n : ℕ => (Nat.totient n : ℚ)) ∧
      canonicalTotientKernelFamily 0 (Sum.inl 1) =
        (fun n : ℕ => (Nat.totient (2 * n) : ℚ)) ∧
      Fintype.card (TotientCanonicalIndex 0) = 2 := by
  refine ⟨?_, ?_, by simpa using card_totientCanonicalIndex 0⟩
  · funext n
    simp [canonicalTotientKernelFamily, totientKernelSeq]
  · funext n
    simp [canonicalTotientKernelFamily, totientKernelSeq, pow_one]

/-- The actual level-zero truncation is one-dimensional. -/
theorem finrank_throughLevel_zero_eq_one :
    finrank ℚ
      (Submodule.span ℚ (Set.range (totientKernelThroughLevelFamily 0))) = 1 := by
  have hrange : Set.range (totientKernelThroughLevelFamily 0)
      = {(fun n : ℕ => (Nat.totient n : ℚ))} := by
    ext f
    constructor
    · rintro ⟨⟨⟨j, hj⟩, ⟨r, hr⟩⟩, rfl⟩
      have hj0 : j = 0 := by omega
      subst hj0
      have hr0 : r = 0 := by simpa using hr
      subst hr0
      refine Set.mem_singleton_iff.mpr ?_
      funext n
      simp [totientKernelThroughLevelFamily, totientKernelSeq]
    · intro hf
      rw [Set.mem_singleton_iff] at hf
      subst hf
      refine ⟨⟨⟨0, by omega⟩, ⟨0, by positivity⟩⟩, ?_⟩
      funext n
      simp [totientKernelThroughLevelFamily, totientKernelSeq]
  rw [hrange]
  have hne : (fun n : ℕ => (Nat.totient n : ℚ)) ≠ 0 := by
    intro h
    have h1 := congrFun h 1
    simp at h1
  exact finrank_span_singleton hne

end ErdosProblems.Erdos249.PaperCompleteR21

#print axioms ErdosProblems.Erdos249.PaperCompleteR21.card_canonical_dyadic_index
#print axioms ErdosProblems.Erdos249.PaperCompleteR21.linearIndependent_canonical_dyadic_family
#print axioms ErdosProblems.Erdos249.PaperCompleteR21.canonical_family_basis_through_level
#print axioms ErdosProblems.Erdos249.PaperCompleteR21.canonical_level_zero_channels
#print axioms ErdosProblems.Erdos249.PaperCompleteR21.finrank_throughLevel_zero_eq_one
