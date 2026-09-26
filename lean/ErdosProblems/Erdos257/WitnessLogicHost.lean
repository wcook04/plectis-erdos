import ErdosProblems.Erdos257.WitnessLogic
import ErdosProblems.Erdos257.WitnessBlockSummability
import ErdosProblems.Erdos257.WitnessBlockReciprocal

/-!
# One host realising a finite monotone witness rule

Fix a finite set `E` of primes and an upward-closed rule `U` on finite sets
of primes with `U E` true and `U ∅` false. The host is the finite union of
the clause supports `witnessClauseSupport (E \ M)`, one for each forbidden
`M ⊆ E`. For every base `b ≥ 2` and every finite prime set `P`, including
primes outside `E`, the canonical weighted series on this one host converges
exactly when `U (P ∩ E)` holds, and its ordinary reciprocal sum diverges.
The irrationality consequence is in `WitnessLogicIrrational`.

The block classification is the proved theorem
`summable_primeWeightedTerm_witnessClauseSupport_iff`; nothing about the
arithmetic blocks is assumed here.
-/

noncomputable section
namespace ErdosProblems.Erdos257
open ErdosProblems.Erdos257.PaperCompleteR7

/-- The constructed host for the rule `U` on the prime set `E`. -/
def witnessLogicHost (E : Finset ℕ) (U : Finset ℕ → Prop) : Set ℕ :=
  ruleBlockHost E U witnessClauseSupport

theorem mem_ruleBlockHost {E : Finset ℕ} {U : Finset ℕ → Prop}
    {B : Finset ℕ → Set ℕ} {a : ℕ} (h : a ∈ ruleBlockHost E U B) :
    ∃ M : Finset ℕ, M ⊆ E ∧ ¬ U M ∧ a ∈ B (E \ M) := by
  classical
  simp only [ruleBlockHost, finiteBlockHost, Set.mem_setOf_eq,
    Finset.mem_filter, Finset.mem_powerset] at h
  obtain ⟨M, ⟨hME, hM⟩, ha⟩ := h
  exact ⟨M, hME, hM, ha⟩

/-- Summability over the rule host is summability over every clause block. -/
theorem summable_ruleBlockHost_iff_blocks
    (w : ℕ → ℝ) (hw : ∀ a, 0 ≤ w a)
    (E : Finset ℕ) (U : Finset ℕ → Prop) (B : Finset ℕ → Set ℕ) :
    Summable (Set.indicator (ruleBlockHost E U B) w) ↔
      ∀ M : Finset ℕ, M ⊆ E → ¬ U M →
        Summable (Set.indicator (B (E \ M)) w) := by
  classical
  rw [ruleBlockHost, summable_finiteBlockHost_iff w hw]
  simp only [Finset.mem_filter, Finset.mem_powerset]
  exact ⟨fun h M hME hM => h M ⟨hME, hM⟩, fun h M hM => h M hM.1 hM.2⟩

/-- Every forbidden set misses some prime of `E`, so its clause is nonempty. -/
theorem forbidden_clause_nonempty (E M : Finset ℕ) (U : Finset ℕ → Prop)
    (hUp : ∀ S T : Finset ℕ, S ⊆ T → U S → U T) (hUE : U E) (hM : ¬ U M) :
    (E \ M).Nonempty := by
  rw [Finset.nonempty_iff_ne_empty]
  intro h
  exact hM (hUp E M (Finset.sdiff_eq_empty_iff_subset.mp h) hUE)

/-- **Witness-logic classification.** For every base `b ≥ 2` and every finite
prime set `P`, the canonical weighted series on the one host converges exactly
when `U (P ∩ E)`. Primes of `P` outside `E` never change the verdict. -/
theorem summable_primeWeightedTerm_witnessLogicHost_iff
    (E : Finset ℕ) (hE : ∀ p ∈ E, Nat.Prime p)
    (U : Finset ℕ → Prop) (hUp : ∀ S T : Finset ℕ, S ⊆ T → U S → U T)
    (hUE : U E) (b : ℕ) (hb : 2 ≤ b)
    (P : Finset ℕ) (hP : ∀ p ∈ P, Nat.Prime p) :
    Summable (Set.indicator (witnessLogicHost E U) (primeWeightedTerm b P)) ↔
      U (P ∩ E) := by
  refine summable_ruleBlockHost_iff (primeWeightedTerm b P)
    (clause_primeWeightedTerm_nonneg b hb P hP) E (P ∩ E) U witnessClauseSupport
    hUp Finset.inter_subset_right ?_
  intro M hME hM
  have hCn := forbidden_clause_nonempty E M U hUp hUE hM
  have hC : ∀ p ∈ E \ M, Nat.Prime p := fun p hp => hE p (Finset.mem_sdiff.mp hp).1
  have hset : P ∩ E ∩ (E \ M) = P ∩ (E \ M) := by
    rw [Finset.inter_assoc, Finset.inter_eq_right.mpr Finset.sdiff_subset]
  rw [hset]
  exact summable_primeWeightedTerm_witnessClauseSupport_iff b hb (E \ M) P hCn hC hP

/-- The host contains no zero: each clause element is a positive multiple. -/
theorem zero_not_mem_witnessLogicHost
    (E : Finset ℕ) (hE : ∀ p ∈ E, Nat.Prime p) (U : Finset ℕ → Prop) :
    0 ∉ witnessLogicHost E U := by
  intro h
  obtain ⟨M, _, _, k, _, m, hm, _, _, h0⟩ := mem_ruleBlockHost h
  have hD : 0 < (E \ M).prod id :=
    clause_product_pos (E \ M) (fun p hp => hE p (Finset.mem_sdiff.mp hp).1)
  have : 0 < (E \ M).prod id ^ k * m := Nat.mul_pos (Nat.pow_pos hD) hm
  omega

/-- The ordinary reciprocal sum over the host diverges whenever `U ∅` fails. -/
theorem not_summable_reciprocal_witnessLogicHost
    (E : Finset ℕ) (hE : ∀ p ∈ E, Nat.Prime p)
    (U : Finset ℕ → Prop) (hUp : ∀ S T : Finset ℕ, S ⊆ T → U S → U T)
    (hUE : U E) (hU0 : ¬ U ∅) :
    ¬ Summable (Set.indicator (witnessLogicHost E U) (fun a : ℕ => (1 : ℝ) / a)) := by
  intro hs
  have hs' := (summable_ruleBlockHost_iff_blocks (fun a : ℕ => (1 : ℝ) / a)
    (fun a => one_div_nonneg.mpr (Nat.cast_nonneg a)) E U witnessClauseSupport).mp
    hs ∅ (Finset.empty_subset E) hU0
  rw [Finset.sdiff_empty] at hs'
  have hEn : E.Nonempty := by
    simpa [Finset.sdiff_empty] using forbidden_clause_nonempty E ∅ U hUp hUE hU0
  exact not_summable_reciprocal_witnessClauseSupport E hEn hE hs'

#print axioms summable_primeWeightedTerm_witnessLogicHost_iff
#print axioms not_summable_reciprocal_witnessLogicHost

end ErdosProblems.Erdos257
end
