import ErdosProblems.Erdos249.PaperCompleteR21.ExcludedCofactorEstimate
import ErdosProblems.Erdos249.TypeBReturnV8.PeripheralFiniteBridge

/-!
# The centred clause is the first-harmonic gap on the good bases

On the good bases the first harmonic factors as `W_N = r_N z_N` (residual times pivot
phase), so its sum splits exactly as the centred correlation plus the fibre-mean
contribution. When every fibre mean is at most `1/100`, the centred clause
`Re C ≤ 14X/25` therefore follows from the good-base gap `Re ∑_{good} W_N ≤ 11X/20`, and
implies the good-base gap at `57X/100`: the two conditions differ by at most `X/100`.
-/

namespace ErdosProblems.Erdos249.PaperCompleteR21

open Erdos249257.TotientTailPeriodKiller
open Finset Filter

/-- The good-base first harmonic is the centred correlation plus the fibre-mean
contribution. -/
theorem goodBase_sum_eq_centered_add_mean (h X L s : ℕ) (η : ℝ) :
    (∑ N ∈ pivotGoodBases X L s η, windowFirstExp h N L) =
      pivotCenteredCorrelation h X L s η + pivotFiberMeanContribution h X L s η := by
  rw [pivotCenteredCorrelation, pivotFiberMeanContribution, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro N _
  rw [windowFirstExp_eq_pivotResidualAt_mul_phase]
  ring

/-- With fibre means at most `1/100`, the good-base gap at `11X/20` gives the centred
clause. -/
theorem centered_re_le_of_goodBase_gap {h X L s : ℕ} {η : ℝ}
    (hmean : ∀ N ∈ pivotGoodBases X L s η,
      ‖pivotFiberMean h X L s (pivotCofactor N L s)‖ ≤ (1 / 100 : ℝ))
    (hgap : (∑ N ∈ pivotGoodBases X L s η, windowFirstExp h N L).re ≤ (11 / 20 : ℝ) * X) :
    (pivotCenteredCorrelation h X L s η).re ≤ (14 / 25 : ℝ) * X := by
  have hsplit := congrArg Complex.re (goodBase_sum_eq_centered_add_mean h X L s η)
  rw [Complex.add_re] at hsplit
  have hfm := norm_pivotFiberMeanContribution_le_of_uniform h X L s η (1 / 100)
    (by norm_num) hmean
  have hre := (abs_le.mp (le_trans (Complex.abs_re_le_norm _) hfm)).1
  linarith

/-- Conversely the centred clause gives the good-base gap at `57X/100`: on the good bases
the centred clause says nothing more than the first-harmonic gap does. -/
theorem goodBase_gap_of_centered_re_le {h X L s : ℕ} {η : ℝ}
    (hmean : ∀ N ∈ pivotGoodBases X L s η,
      ‖pivotFiberMean h X L s (pivotCofactor N L s)‖ ≤ (1 / 100 : ℝ))
    (hc : (pivotCenteredCorrelation h X L s η).re ≤ (14 / 25 : ℝ) * X) :
    (∑ N ∈ pivotGoodBases X L s η, windowFirstExp h N L).re ≤ (57 / 100 : ℝ) * X := by
  have hsplit := congrArg Complex.re (goodBase_sum_eq_centered_add_mean h X L s η)
  rw [Complex.add_re] at hsplit
  have hfm := norm_pivotFiberMeanContribution_le_of_uniform h X L s η (1 / 100)
    (by norm_num) hmean
  have hre := (abs_le.mp (le_trans (Complex.abs_re_le_norm _) hfm)).2
  linarith

/-- At the minimal depth with `s = 26` and `η = 1/1000`: eventual fibre means and a cofinal
good-base gap at `11X/20` give the cofinal centred clause that
`dtw_of_fiberMean_and_centered` asks for. -/
theorem centered_of_fiberMean_and_goodBase_gap
    (hmean : ∀ h : ℕ, 0 < h → ∀ᶠ X : ℕ in atTop,
      ∀ N ∈ pivotGoodBases X (minimalDepth h 26 X) 26 (1 / 1000 : ℝ),
        ‖pivotFiberMean h X (minimalDepth h 26 X) 26
            (pivotCofactor N (minimalDepth h 26 X) 26)‖ ≤ (1 / 100 : ℝ))
    (hgap : ∀ h : ℕ, 0 < h → ∀ A : ℕ, ∃ X : ℕ, max A 1 ≤ X ∧
      (∑ N ∈ pivotGoodBases X (minimalDepth h 26 X) 26 (1 / 1000 : ℝ),
        windowFirstExp h N (minimalDepth h 26 X)).re ≤ (11 / 20 : ℝ) * X) :
    ∀ h : ℕ, 0 < h → ∀ A : ℕ, ∃ X : ℕ, max A 1 ≤ X ∧
      (pivotCenteredCorrelation h X (minimalDepth h 26 X) 26 (1 / 1000 : ℝ)).re
        ≤ (14 / 25 : ℝ) * X := by
  intro h hh A
  obtain ⟨A₁, hA₁⟩ := eventually_atTop.mp (hmean h hh)
  obtain ⟨X, hX, hg⟩ := hgap h hh (max A A₁)
  have hmax : max (max A A₁) 1 ≤ X := hX
  refine ⟨X, le_trans (max_le_max (le_max_left A A₁) le_rfl) hmax, ?_⟩
  have hA₁X : A₁ ≤ X := le_trans (le_trans (le_max_right A A₁) (le_max_left _ _)) hmax
  exact centered_re_le_of_goodBase_gap (hA₁ X hA₁X) hg

end ErdosProblems.Erdos249.PaperCompleteR21

#print axioms ErdosProblems.Erdos249.PaperCompleteR21.goodBase_sum_eq_centered_add_mean
#print axioms ErdosProblems.Erdos249.PaperCompleteR21.centered_re_le_of_goodBase_gap
#print axioms ErdosProblems.Erdos249.PaperCompleteR21.goodBase_gap_of_centered_re_le
#print axioms ErdosProblems.Erdos249.PaperCompleteR21.centered_of_fiberMean_and_goodBase_gap
