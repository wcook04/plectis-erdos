import ErdosProblems.Erdos257.PaperCompleteR8.WeightedReturn

/-!
# Fixed-base hereditary weighted support

This exposes the hereditary fixed-base clause of the paper directly.  The
only extra step beyond the checked weighted theorem is restriction of the
nonnegative weighted summability witness to a subset.
-/
noncomputable section
namespace ErdosProblems.Erdos257.PaperCompleteR8
open Erdos249257
open ErdosProblems.Erdos257.PaperCompleteR7

/-- Restrict a weighted summability witness to a smaller support. -/
theorem finitePrimeWeighted_subset
    (b : ℕ) (hb : 2 ≤ b) {H A : Set ℕ} (hAH : A ⊆ H)
    (hH : FinitePrimeWeighted b H) : FinitePrimeWeighted b A := by
  classical
  obtain ⟨P, hPn, hP, hs⟩ := hH
  refine ⟨P, hPn, hP, Summable.of_nonneg_of_le
    (fun a => Set.indicator_nonneg (fun a _ => primeWeightedTerm_nonneg b hb P a) a) ?_ hs⟩
  intro a
  by_cases ha : a ∈ A
  · simp only [Set.indicator_of_mem ha, Set.indicator_of_mem (hAH ha), le_refl]
  · rw [Set.indicator_of_notMem ha]
    exact Set.indicator_nonneg (fun a _ => primeWeightedTerm_nonneg b hb P a) a

/-- Every infinite subset of a fixed-base weighted support has irrational
support series in that same base. -/
theorem finitePrimeWeighted_fixedBase_hereditary
    (b : ℕ) (H : Set ℕ) (hb : 2 ≤ b) (hH0 : 0 ∉ H)
    (hH : FinitePrimeWeighted b H) :
    ∀ A : Set ℕ, A ⊆ H → A.Infinite →
      Irrational (erdosSupportSeries b A) := by
  intro A hAH hA
  exact weighted_irrational_of_mean_target weightedDyadicMeanTarget b A hb
    (fun h0 => hH0 (hAH h0)) (finitePrimeWeighted_subset b hb hAH hH) hA

end ErdosProblems.Erdos257.PaperCompleteR8
end
