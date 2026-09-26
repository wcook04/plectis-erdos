import Mathlib.Topology.Algebra.InfiniteSum.ENNReal
import Mathlib.Data.Finset.Lattice.Fold

/-!
# Finite unions of nonnegative weighted supports

This is the finite-union part of the proposed witness-logic construction.
It does not assert that any particular arithmetic block has the required
summability classification.
-/

noncomputable section
namespace ErdosProblems.Erdos257

/-- For a nonnegative weight, a series over the union of two supports is
summable exactly when the two component sums are. The supports may overlap. -/
theorem summable_indicator_union_iff
    (w : ℕ → ℝ) (hw : ∀ a, 0 ≤ w a) (A B : Set ℕ) :
    Summable (Set.indicator (A ∪ B) w) ↔
      Summable (Set.indicator A w) ∧ Summable (Set.indicator B w) := by
  classical
  have hnonneg (S : Set ℕ) : ∀ a, 0 ≤ Set.indicator S w a := by
    intro a
    by_cases h : a ∈ S <;> simp [h, hw a]
  have hsub (S T : Set ℕ) (hST : S ⊆ T) :
      ∀ a, Set.indicator S w a ≤ Set.indicator T w a := by
    intro a
    by_cases hs : a ∈ S
    · have ht : a ∈ T := hST hs
      simp [hs, ht]
    · by_cases ht : a ∈ T
      · simpa [hs, ht] using hw a
      · simp [hs, ht]
  constructor
  · intro h
    constructor
    · exact Summable.of_nonneg_of_le (hnonneg A)
        (hsub A (A ∪ B) (fun _ ha => Or.inl ha)) h
    · exact Summable.of_nonneg_of_le (hnonneg B)
        (hsub B (A ∪ B) (fun _ hb => Or.inr hb)) h
  · rintro ⟨hA, hB⟩
    apply Summable.of_nonneg_of_le (hnonneg (A ∪ B)) ?_ (hA.add hB)
    intro a
    by_cases ha : a ∈ A <;> by_cases hb : a ∈ B
    all_goals simp [ha, hb, hw a]

/-- The support selected by a finite family of blocks. -/
def finiteBlockHost {ι : Type*} (B : ι → Set ℕ) (H : Finset ι) : Set ℕ :=
  {a | ∃ i ∈ H, a ∈ B i}

/-- Overlapping blocks cause no problem: a nonnegative weighted series over
their finite union converges exactly when every block series converges. -/
theorem summable_finiteBlockHost_iff {ι : Type*} [DecidableEq ι]
    (w : ℕ → ℝ) (hw : ∀ a, 0 ≤ w a) (B : ι → Set ℕ) (H : Finset ι) :
    Summable (Set.indicator (finiteBlockHost B H) w) ↔
      ∀ i ∈ H, Summable (Set.indicator (B i) w) := by
  classical
  induction H using Finset.induction_on with
  | empty =>
      simp [finiteBlockHost]
  | @insert i H hi ih =>
      have hset : finiteBlockHost B (insert i H) = B i ∪ finiteBlockHost B H := by
        ext a
        change (∃ j, j ∈ insert i H ∧ a ∈ B j) ↔
          a ∈ B i ∨ ∃ j, j ∈ H ∧ a ∈ B j
        constructor
        · rintro ⟨j, hj, hBj⟩
          rcases Finset.mem_insert.mp hj with rfl | hj
          · exact Or.inl hBj
          · exact Or.inr ⟨j, hj, hBj⟩
        · rintro (hBi | ⟨j, hj, hBj⟩)
          · exact ⟨i, Finset.mem_insert_self i H, hBi⟩
          · exact ⟨j, Finset.mem_insert_of_mem hj, hBj⟩
      rw [hset, summable_indicator_union_iff w hw, ih]
      constructor
      · rintro ⟨hBi, hrest⟩ j hj
        rcases Finset.mem_insert.mp hj with rfl | hj
        · exact hBi
        · exact hrest j hj
      · intro h
        exact ⟨h i (Finset.mem_insert_self i H),
          fun j hj => h j (Finset.mem_insert_of_mem hj)⟩

/-- An upward-closed rule on subsets of a finite prime set is determined by
which complements of forbidden sets a proposed witness meets. This version
uses all forbidden sets; discarding nonmaximal ones is a later simplification. -/
theorem upward_rule_iff_hits_forbidden
    (E P : Finset ℕ) (U : Finset ℕ → Prop)
    (hUp : ∀ S T : Finset ℕ, S ⊆ T → U S → U T)
    (hPE : P ⊆ E) :
    U P ↔ ∀ M : Finset ℕ, M ⊆ E → ¬ U M →
      (P ∩ (E \ M)).Nonempty := by
  classical
  constructor
  · intro hP M hME hnot
    by_contra hn
    have hsub : P ⊆ M := by
      intro p hp
      by_contra hpM
      have hpEM : p ∈ E \ M :=
        Finset.mem_sdiff.mpr ⟨hPE hp, hpM⟩
      exact hn ⟨p, Finset.mem_inter.mpr ⟨hp, hpEM⟩⟩
    exact hnot (hUp P M hsub hP)
  · intro hhit
    by_contra hP
    obtain ⟨p, hp⟩ := hhit P hPE hP
    have hpP : p ∈ P := (Finset.mem_inter.mp hp).1
    have hpnotP : p ∉ P := (Finset.mem_sdiff.mp (Finset.mem_inter.mp hp).2).2
    exact hpnotP hpP

/-- The finite union implementing a rule from blocks for the complements of
its forbidden sets. This definition supplies no arithmetic block theorem. -/
def ruleBlockHost (E : Finset ℕ) (U : Finset ℕ → Prop)
    (B : Finset ℕ → Set ℕ) : Set ℕ := by
  classical
  exact finiteBlockHost (fun M => B (E \ M))
    (E.powerset.filter (fun M => ¬ U M))

/-- Once each clause block has its stated summability classification, the
explicit finite union realizes the complete upward-closed rule. The clause
classification is an explicit hypothesis, not a claimed arithmetic result. -/
theorem summable_ruleBlockHost_iff
    (w : ℕ → ℝ) (hw : ∀ a, 0 ≤ w a)
    (E P : Finset ℕ) (U : Finset ℕ → Prop) (B : Finset ℕ → Set ℕ)
    (hUp : ∀ S T : Finset ℕ, S ⊆ T → U S → U T) (hPE : P ⊆ E)
    (hblock : ∀ M : Finset ℕ, M ⊆ E → ¬ U M →
      (Summable (Set.indicator (B (E \ M)) w) ↔
        (P ∩ (E \ M)).Nonempty)) :
    Summable (Set.indicator (ruleBlockHost E U B) w) ↔ U P := by
  classical
  rw [ruleBlockHost, summable_finiteBlockHost_iff w hw,
    upward_rule_iff_hits_forbidden E P U hUp hPE]
  simp only [Finset.mem_filter, Finset.mem_powerset]
  constructor
  · intro h M hME hM
    exact (hblock M hME hM).mp (h M ⟨hME, hM⟩)
  · intro h M hM
    exact (hblock M hM.1 hM.2).mpr (h M hM.1 hM.2)

#print axioms summable_indicator_union_iff
#print axioms summable_finiteBlockHost_iff
#print axioms upward_rule_iff_hits_forbidden
#print axioms summable_ruleBlockHost_iff

end ErdosProblems.Erdos257
end
