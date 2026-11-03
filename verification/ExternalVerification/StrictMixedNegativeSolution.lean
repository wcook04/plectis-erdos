/- Copyright (c) 2026 Will Cook. Released under Apache 2.0. -/
import ErdosProblems.Erdos257.PaperCompleteR7.AnalyticTargets

/-! Deliberately mismatching control: the desired conclusion is assumed.
Comparator must reject this implication as different from the existential
challenge. This file supplies no evidence for the corollary.
-/
namespace ErdosProblems.Erdos257.PaperCompleteR8
open ErdosProblems.Erdos257.PaperCompleteR7 Erdos249257

theorem exists_strict_mixed_support_host
    (h : ∃ U : Set ℕ, U.Infinite ∧ 0 ∉ U ∧
      ¬ HasStrengthenedPositiveCover U ∧
      (∀ b : ℕ, 2 ≤ b → ¬ FinitePrimeWeighted b U) ∧
      (∀ A : Set ℕ, A ⊆ U → A.Infinite → ∀ b : ℕ, 2 ≤ b →
        Irrational (erdosSupportSeries b A))) :
    ∃ U : Set ℕ, U.Infinite ∧ 0 ∉ U ∧
      ¬ HasStrengthenedPositiveCover U ∧
      (∀ b : ℕ, 2 ≤ b → ¬ FinitePrimeWeighted b U) ∧
      (∀ A : Set ℕ, A ⊆ U → A.Infinite → ∀ b : ℕ, 2 ≤ b →
        Irrational (erdosSupportSeries b A)) := h

end ErdosProblems.Erdos257.PaperCompleteR8
