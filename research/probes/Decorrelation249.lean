import ErdosProblems.Erdos249.PaperCompleteR21.ExcludedCofactorEstimate
import ErdosProblems.Erdos249.TypeBReturnV8.PeripheralFiniteBridge

/-! # #249: the pivot decorrelation from two of its clauses

`DTWPivotResidualDecorrelation` (demand `G064`) asks, for every `h`, for parameters at which
the four clauses of `PivotBudgetAt` hold together with the two depth conditions. At the minimal
depth, with `s = 26` and `η = 1/1000`, `prop_dickman` supplies the depth conditions and the
non-supplier count, and `excluded_budget_one_thousandth_of_chebyshev` (Chebyshev in place of the
prime number theorem) the bad-base count. Two clauses remain: the fibre means and the centred
correlation. -/

open Filter

namespace ProbeDecorrelation249

open Erdos249257.TotientTailPeriodKiller
open ErdosProblems.Erdos249.PaperCompleteR21
open ErdosProblems.Erdos249.PaperCompleteR21.ExcludedCofactor

theorem nonSupplier_filter_eq (X L s : ℕ) :
    (Finset.Ico X (2 * X)).filter (fun N => N ∉ pivotSupplierBases X L s)
      = pivotNonSupplierBases X L s := by
  unfold pivotNonSupplierBases pivotSupplierBases
  refine Finset.filter_congr fun N hN => ?_
  simp [Finset.mem_filter, hN]

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
  · have hbad := (hA₂ X hXA₂).1
    simpa [filter_excluded_eq_pivotBadBases] using hbad.le
  · have hnon := (hA₃ X hXA₃).2
    simpa [nonSupplier_filter_eq] using hnon.le

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

end ProbeDecorrelation249

#print axioms ProbeDecorrelation249.dtw_of_fiberMean_and_centered
#print axioms ProbeDecorrelation249.irrational_totient_series_of_fiberMean_and_centered
