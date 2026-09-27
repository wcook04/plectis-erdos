-- SPDX-FileCopyrightText: 2026 Will Cook
-- SPDX-License-Identifier: Apache-2.0
import ErdosProblems.Erdos249.PaperCompleteR21.ExcludedCofactorEstimate
import ErdosProblems.Erdos249.TypeBReturnV8.PeripheralFiniteBridge

/-!
# Erdős #249: the pivot decorrelation from two of its clauses

`DTWPivotResidualDecorrelation` (`FirstHarmonicPivot`, demand `G064` of the demand ledger)
asks, for every `h`, for parameters at which the two depth conditions and the four clauses of
`PivotBudgetAt` hold together, and it implies the irrationality of `∑ φ(n) / 2 ^ n`. The finite
bridge `pivotBudgetAt_of_peripheral_estimates` reduces three of the clauses to a uniform
fibre-mean bound, a count of bad bases and a count of non-supplier bases.

At the minimal depth, with `s = 26` and `η = 1/1000`, two proofs that do not mention the
decorrelation supply most of this. `prop_dickman` gives the two depth conditions and, for all
large `X`, fewer than `8X/25` non-supplier bases, with no hypothesis. The argument graph's
frontier of `prop_badcof` showed that its proof uses the prime number theorem only through a
dyadic prime count, which Chebyshev's bound supplies:
`excluded_budget_one_thousandth_of_chebyshev` gives fewer than `X/100` bad bases for all large
`X`, with no hypothesis. The two theorems below state what remains: the fibre means and the
centred correlation.
-/

open Filter

namespace ErdosProblems.Erdos249.PaperCompleteR21

open Erdos249257.TotientTailPeriodKiller
open ErdosProblems.Erdos249.PaperCompleteR21.ExcludedCofactor

/-- The bad-base clause, read off the excluded-cofactor count. -/
theorem card_pivotBadBases_le_of_count (h X : ℕ)
    (hcount : ((((pivotSupplierBases X (minimalDepth h 26 X) 26).filter
        (fun N => pivotCofactor N (minimalDepth h 26 X) 26
          ∈ excludedCofactorSet (1 / 1000))).card : ℕ) : ℝ) < (1 / 100 : ℝ) * X) :
    ((pivotBadBases X (minimalDepth h 26 X) 26 (1 / 1000 : ℝ)).card : ℝ)
      ≤ (1 / 100 : ℝ) * X := by
  rw [← filter_excluded_eq_pivotBadBases]
  exact hcount.le

/-- **The decorrelation from its fibre-mean and centred clauses.** At the minimal depth, with
`s = 26` and `η = 1/1000`, `prop_dickman` supplies the depth conditions and the non-supplier
count and `excluded_budget_one_thousandth_of_chebyshev` the bad-base count. -/
theorem dtw_of_fiberMean_and_centered
    (hmean : ∀ h : ℕ, 0 < h → ∀ᶠ X : ℕ in atTop,
      ∀ N ∈ pivotGoodBases X (minimalDepth h 26 X) 26 (1 / 1000 : ℝ),
        ‖pivotFiberMean h X (minimalDepth h 26 X) 26
            (pivotCofactor N (minimalDepth h 26 X) 26)‖ ≤ (1 / 100 : ℝ))
    (hcentered : ∀ h : ℕ, 0 < h → ∀ A : ℕ, ∃ X : ℕ, max A 1 ≤ X ∧
      (pivotCenteredCorrelation h X (minimalDepth h 26 X) 26 (1 / 1000 : ℝ)).re
        ≤ (14 / 25 : ℝ) * X) :
    DTWPivotResidualDecorrelation := by
  intro h hh
  refine ⟨26, by norm_num, (1 / 1000 : ℝ), by norm_num, by norm_num, ?_⟩
  intro X₀
  obtain ⟨A₁, hA₁⟩ := eventually_atTop.mp (hmean h hh)
  obtain ⟨A₂, hA₂⟩ := eventually_atTop.mp (excluded_budget_one_thousandth_of_chebyshev h 26)
  obtain ⟨A₃, hA₃⟩ := eventually_atTop.mp (prop_dickman h 26).2.2.2.2.2
  obtain ⟨X, hX, hc⟩ := hcentered h hh (max X₀ (max A₁ (max A₂ A₃)))
  simp only [max_le_iff] at hX
  obtain ⟨⟨hX₀, hXA₁, hXA₂, hXA₃⟩, hX1⟩ := hX
  have hadm : h ≤ minimalDepth h 26 X - 26 ∧
      16 * (2 * X + h + minimalDepth h 26 X + 2) ≤ 2 ^ minimalDepth h 26 X :=
    ((prop_dickman h 26).1 X).1
  refine ⟨X, minimalDepth h 26 X, max_le hX₀ hX1, hadm.1, hadm.2, ?_⟩
  refine pivotBudgetAt_of_peripheral_estimates h X (minimalDepth h 26 X) 26 (1 / 1000 : ℝ)
    hc (hA₁ X hXA₁) ?_ ?_
  · exact card_pivotBadBases_le_of_count h X (hA₂ X hXA₂).1
  · have hnon := (hA₃ X hXA₃).2
    simpa [filter_not_mem_pivotSupplierBases] using hnon.le

/-- **The irrationality of `∑ φ(n) / 2 ^ n` from the fibre means and the centred
correlation**, at the minimal depth with `s = 26` and `η = 1/1000`. -/
theorem irrational_totient_series_of_fiberMean_and_centered
    (hmean : ∀ h : ℕ, 0 < h → ∀ᶠ X : ℕ in atTop,
      ∀ N ∈ pivotGoodBases X (minimalDepth h 26 X) 26 (1 / 1000 : ℝ),
        ‖pivotFiberMean h X (minimalDepth h 26 X) 26
            (pivotCofactor N (minimalDepth h 26 X) 26)‖ ≤ (1 / 100 : ℝ))
    (hcentered : ∀ h : ℕ, 0 < h → ∀ A : ℕ, ∃ X : ℕ, max A 1 ≤ X ∧
      (pivotCenteredCorrelation h X (minimalDepth h 26 X) 26 (1 / 1000 : ℝ)).re
        ≤ (14 / 25 : ℝ) * X) :
    Irrational (∑' n : ℕ, (Nat.totient n : ℝ) / 2 ^ n) :=
  irrational_totient_series_of_pivotResidualDecorrelation
    (dtw_of_fiberMean_and_centered hmean hcentered)

end ErdosProblems.Erdos249.PaperCompleteR21

#print axioms ErdosProblems.Erdos249.PaperCompleteR21.dtw_of_fiberMean_and_centered
#print axioms ErdosProblems.Erdos249.PaperCompleteR21.irrational_totient_series_of_fiberMean_and_centered
