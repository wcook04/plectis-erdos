import ErdosProblems.Erdos257.WitnessLogicHost
import ErdosProblems.Erdos257.PaperCompleteR8.WeightedReturn

/-!
# Irrationality on a witness-logic host

The full witness `E` has finite weighted mass at base two on the host of
`WitnessLogicHost`, so the checked weighted theorem makes every infinite
subset irrational in every base, although the host's reciprocal sum diverges.
-/

noncomputable section
namespace ErdosProblems.Erdos257
open Erdos249257
open ErdosProblems.Erdos257.PaperCompleteR7

/-- Every infinite subset of the host has irrational support series in every
base `b ≥ 2`, through the full witness `E` at base two and the checked
weighted theorem. -/
theorem witnessLogicHost_allBase_irrational
    (E : Finset ℕ) (hE : ∀ p ∈ E, Nat.Prime p)
    (U : Finset ℕ → Prop) (hUp : ∀ S T : Finset ℕ, S ⊆ T → U S → U T)
    (hUE : U E) (hU0 : ¬ U ∅) :
    ∀ A : Set ℕ, A ⊆ witnessLogicHost E U → A.Infinite →
      ∀ b : ℕ, 2 ≤ b → Irrational (erdosSupportSeries b A) := by
  have hEn : E.Nonempty := by
    simpa [Finset.sdiff_empty] using forbidden_clause_nonempty E ∅ U hUp hUE hU0
  have hW : FinitePrimeWeighted 2 (witnessLogicHost E U) :=
    ⟨E, hEn, hE, (summable_primeWeightedTerm_witnessLogicHost_iff E hE U hUp hUE
      2 le_rfl E hE).mpr (by simpa [Finset.inter_self] using hUE)⟩
  exact PaperCompleteR8.divisibilityWeightedClaim.2 _
    (zero_not_mem_witnessLogicHost E hE U) hW

/-- **Finite monotone witness logic is realisable.** For each finite prime set
`E` and each nonconstant upward-closed rule `U`, one host `H` without zero has:
weighted summability at every base `b ≥ 2` and every finite prime witness `P`
exactly when `U (P ∩ E)`; a divergent reciprocal sum; and irrational support
series for every infinite subset in every base. -/
theorem finite_monotone_witness_rule_realised
    (E : Finset ℕ) (hE : ∀ p ∈ E, Nat.Prime p)
    (U : Finset ℕ → Prop) (hUp : ∀ S T : Finset ℕ, S ⊆ T → U S → U T)
    (hUE : U E) (hU0 : ¬ U ∅) :
    ∃ H : Set ℕ, 0 ∉ H ∧
      (∀ b : ℕ, 2 ≤ b → ∀ P : Finset ℕ, (∀ p ∈ P, Nat.Prime p) →
        (Summable (Set.indicator H (primeWeightedTerm b P)) ↔ U (P ∩ E))) ∧
      ¬ Summable (Set.indicator H (fun a : ℕ => (1 : ℝ) / a)) ∧
      (∀ A : Set ℕ, A ⊆ H → A.Infinite →
        ∀ b : ℕ, 2 ≤ b → Irrational (erdosSupportSeries b A)) :=
  ⟨witnessLogicHost E U, zero_not_mem_witnessLogicHost E hE U,
    fun b hb P hP => summable_primeWeightedTerm_witnessLogicHost_iff E hE U hUp hUE b hb P hP,
    not_summable_reciprocal_witnessLogicHost E hE U hUp hUE hU0,
    witnessLogicHost_allBase_irrational E hE U hUp hUE hU0⟩

#print axioms finite_monotone_witness_rule_realised

end ErdosProblems.Erdos257
end
