-- SPDX-FileCopyrightText: 2026 Will Cook
-- SPDX-License-Identifier: Apache-2.0
import ErdosProblems.ArgumentGraph.Results.Erdos249
import ErdosProblems.Erdos249.PaperCompleteR21.FiberMeanOfPrimeNumberTheorem

/-!
# Erdős #249: the first-harmonic route, given the prime number theorem

`Results/Erdos249.lean` reduces `DTWPivotResidualDecorrelation`, at the minimal depth with
`s = 26` and `η = 1/1000`, to two clauses: a uniform bound on the fibre means and the centred
correlation. `fiberMean_le_of_primeNumberTheorem` proves the first from the prime number
theorem.

The second is the first-harmonic gap on the good bases. There the first harmonic factors as the
residual times the pivot phase, so its sum over the good bases is the centred correlation plus
the fibre-mean contribution (`goodBase_sum_eq_centered_add_mean`). With every fibre mean at most
`1/100` the two conditions differ by at most `X/100` either way: the good-base gap at `11X/20`
gives the centred clause (`centered_re_le_of_goodBase_gap`), and the centred clause gives the
good-base gap at `57X/100` (`goodBase_gap_of_centered_re_le`).

Hence, given the prime number theorem, the irrationality of `∑ φ(n)/2^n` follows once, for every
`h ≥ 1`, there are arbitrarily large `X` at which the real part of the first harmonic summed over
the good bases is at most `11X/20`
(`irrational_totient_series_of_primeNumberTheorem_and_goodBase_gap`). The non-supplier and bad
bases, about a third of `[X, 2X)`, are handled unconditionally by `prop_dickman` and Chebyshev's
bound.
-/

open Filter

namespace ErdosProblems.Erdos249.PaperCompleteR21

open Erdos249257.TotientTailPeriodKiller
open ErdosProblems.Erdos251.PaperR11.PrimeSource (PrimeNumberTheorem)
open Finset

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

/-- Conversely the centred clause gives the good-base gap at `57X/100`: on the good bases the
centred clause asks for nothing beyond the first-harmonic gap. -/
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
good-base gap at `11X/20` give the cofinal centred clause of `dtw_of_fiberMean_and_centered`. -/
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

/-- **The decorrelation from the prime number theorem and the centred clause.** -/
theorem dtw_of_primeNumberTheorem_and_centered (hPNT : PrimeNumberTheorem)
    (hcentered : ∀ h : ℕ, 0 < h → ∀ A : ℕ, ∃ X : ℕ, max A 1 ≤ X ∧
      (pivotCenteredCorrelation h X (minimalDepth h 26 X) 26 (1 / 1000 : ℝ)).re
        ≤ (14 / 25 : ℝ) * X) :
    DTWPivotResidualDecorrelation :=
  dtw_of_fiberMean_and_centered (fiberMean_le_of_primeNumberTheorem hPNT) hcentered

/-- **The irrationality of `∑ φ(n) / 2 ^ n` from the prime number theorem and the centred
clause.** -/
theorem irrational_totient_series_of_primeNumberTheorem_and_centered (hPNT : PrimeNumberTheorem)
    (hcentered : ∀ h : ℕ, 0 < h → ∀ A : ℕ, ∃ X : ℕ, max A 1 ≤ X ∧
      (pivotCenteredCorrelation h X (minimalDepth h 26 X) 26 (1 / 1000 : ℝ)).re
        ≤ (14 / 25 : ℝ) * X) :
    Irrational (∑' n : ℕ, (Nat.totient n : ℝ) / 2 ^ n) :=
  irrational_totient_series_of_pivotResidualDecorrelation
    (dtw_of_primeNumberTheorem_and_centered hPNT hcentered)

/-- **The irrationality of `∑ φ(n) / 2 ^ n` from the prime number theorem and a first-harmonic
gap on the good bases**: for every `h ≥ 1`, arbitrarily large `X` at which the real part of the
first harmonic summed over the good bases is at most `11X/20`. -/
theorem irrational_totient_series_of_primeNumberTheorem_and_goodBase_gap
    (hPNT : PrimeNumberTheorem)
    (hgap : ∀ h : ℕ, 0 < h → ∀ A : ℕ, ∃ X : ℕ, max A 1 ≤ X ∧
      (∑ N ∈ pivotGoodBases X (minimalDepth h 26 X) 26 (1 / 1000 : ℝ),
        windowFirstExp h N (minimalDepth h 26 X)).re ≤ (11 / 20 : ℝ) * X) :
    Irrational (∑' n : ℕ, (Nat.totient n : ℝ) / 2 ^ n) :=
  irrational_totient_series_of_primeNumberTheorem_and_centered hPNT
    (centered_of_fiberMean_and_goodBase_gap (fiberMean_le_of_primeNumberTheorem hPNT) hgap)

end ErdosProblems.Erdos249.PaperCompleteR21

#print axioms ErdosProblems.Erdos249.PaperCompleteR21.goodBase_sum_eq_centered_add_mean
#print axioms ErdosProblems.Erdos249.PaperCompleteR21.centered_re_le_of_goodBase_gap
#print axioms ErdosProblems.Erdos249.PaperCompleteR21.goodBase_gap_of_centered_re_le
#print axioms ErdosProblems.Erdos249.PaperCompleteR21.dtw_of_primeNumberTheorem_and_centered
#print axioms ErdosProblems.Erdos249.PaperCompleteR21.irrational_totient_series_of_primeNumberTheorem_and_goodBase_gap
