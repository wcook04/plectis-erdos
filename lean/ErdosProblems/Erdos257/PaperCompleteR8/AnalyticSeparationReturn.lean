import ErdosProblems.Erdos257.PaperCompleteR8.DyadicHostSeparation
import ErdosProblems.Erdos257.PaperCompleteR8.CoverClassTransport
import ErdosProblems.Erdos257.PaperCompleteR8.CoverScalarGauge
import ErdosProblems.Erdos257.PaperCompleteR7.TailGluing

/-! # Paper-facing return: weighted separation and the original cover predicate
-/
noncomputable section
namespace ErdosProblems.Erdos257.PaperCompleteR8
open Erdos249257
open ErdosProblems.Erdos257.PaperCompleteR7

/-- A_W satisfies the literal weighted criterion but fails the literal
strengthened-cover predicate, not just a differently typed obstruction. -/
theorem exists_weighted_not_strengthened_host :
    ∃ A : Set ℕ, A.Infinite ∧ 0 ∉ A ∧ FinitePrimeWeighted 2 A ∧
      ¬ Summable (Set.indicator A (fun a : ℕ => (1 : ℝ) / a)) ∧
      ¬ HasStrengthenedPositiveCover A ∧ IsEmpty (LogBudgetCover A) ∧
      (∀ B : Set ℕ, B ⊆ A → B.Infinite → ∀ b : ℕ, 2 ≤ b →
        Irrational (erdosSupportSeries b B)) := by
  obtain ⟨A, hinf, hzero, hw, hrec, hn, hirr⟩ :=
    exists_weighted_host_outside_every_logBudgetCover
  exact ⟨A, hinf, hzero, hw, hrec,
    not_hasStrengthenedPositiveCover_of_isEmpty A hn, hn, hirr⟩

/-- The constructed weighted obstruction can still be synchronised with any
actual strengthened-cover host. This does not assume A-star exists. -/
theorem exists_weighted_obstruction_with_mixed_heredity :
    ∃ A : Set ℕ, A.Infinite ∧ 0 ∉ A ∧ FinitePrimeWeighted 2 A ∧
      IsEmpty (LogBudgetCover A) ∧
      (∀ V : Set ℕ, HasStrengthenedPositiveCover V →
        ∀ B : Set ℕ, B ⊆ A ∪ V → B.Infinite → ∀ b : ℕ, 2 ≤ b →
          Irrational (erdosSupportSeries b B)) := by
  obtain ⟨A, hinf, hzero, hw, hrec, hn, hirr⟩ :=
    exists_weighted_host_outside_every_logBudgetCover
  refine ⟨A, hinf, hzero, hw, hn, ?_⟩
  intro V hV B hB hBi b hb
  exact mixedSupportClaim A V hzero hw hV B hB hBi b hb

end ErdosProblems.Erdos257.PaperCompleteR8
end
