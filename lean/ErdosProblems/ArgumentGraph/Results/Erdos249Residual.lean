-- SPDX-FileCopyrightText: 2026 Will Cook
-- SPDX-License-Identifier: Apache-2.0
import ErdosProblems.ArgumentGraph.Residualise
import ErdosProblems.ArgumentGraph.Results.Erdos249Route

/-!
# Erdős #249: the first-harmonic route found by residualisation

`residualise` (`ErdosProblems.ArgumentGraph.Residualise`) searches for a proof of a demand from
the readings of given suppliers and adds a theorem stating the demand from the clauses it could
not supply, once the kernel accepts it. The demand here is `DTWPivotResidualDecorrelation`
(demand `G064`), from which the irrationality of `∑ φ(n)/2^n` follows. The composition written
by hand for it, `dtw_of_fiberMean_and_centered` (`Results/Erdos249.lean`), is not among the
suppliers.

* `dtw_residual`: from `prop_dickman`, `excluded_budget_one_thousandth_of_chebyshev` and
  `pivotBudgetAt_of_peripheral_estimates`, the search fixes the depth `L = minimalDepth h s X`
  and `η = 1/1000`, and leaves: some `s > 0` such that for every `h > 0` the centred clause and the
  fibre-mean clause hold together for arbitrarily large `X`
  (`dtw_of_joint_fiberMean_and_centered`). The two clauses the hand-written composition assumes
  imply this at `s = 26` (`joint_of_fiberMean_and_centered`); they ask for the fibre means at
  every large `X`.
* `dtw_residual_gen2`: with `fiberMean_le_of_primeNumberTheorem` among the suppliers the
  fibre-mean clause is supplied and `s = 26` is fixed by it. What is left is the prime number
  theorem and, for every `h > 0`, the centred clause for arbitrarily large `X`
  (`irrational_totient_series_of_primeNumberTheorem_and_frequent_centered`).

Both certificates are regenerated when this module is built, so a change in the search that
changes either statement breaks the theorems below. They say what the decorrelation needs. The
irrationality needs less: the good-base gap alone gives it, with no fibre-mean bound and no
prime number theorem (`Results/Erdos249Endpoint.lean`).
-/

open Filter

namespace ErdosProblems.Erdos249.PaperCompleteR21

open Erdos249257.TotientTailPeriodKiller
open ErdosProblems.Erdos249.PaperCompleteR21.ExcludedCofactor
open ErdosProblems.Erdos251.PaperR11.PrimeSource (PrimeNumberTheorem)

residualise dtw_residual for DTWPivotResidualDecorrelation
  using prop_dickman excluded_budget_one_thousandth_of_chebyshev
    pivotBudgetAt_of_peripheral_estimates
  with filter_excluded_eq_pivotBadBases filter_not_mem_pivotSupplierBases

residualise dtw_residual_gen2 for DTWPivotResidualDecorrelation
  using prop_dickman excluded_budget_one_thousandth_of_chebyshev
    pivotBudgetAt_of_peripheral_estimates fiberMean_le_of_primeNumberTheorem
  with filter_excluded_eq_pivotBadBases filter_not_mem_pivotSupplierBases

/-- **The decorrelation from the joint clause the residualiser leaves**: for some `s > 0`, for
every `h > 0`, arbitrarily large `X` at which the centred clause and the fibre-mean clause hold
together. -/
theorem dtw_of_joint_fiberMean_and_centered (s : ℕ) (hs : 0 < s)
    (hjoint : ∀ h : ℕ, 0 < h → ∃ᶠ X in atTop,
      (pivotCenteredCorrelation h X (minimalDepth h s X) s (1 / 1000 : ℝ)).re
          ≤ (14 / 25 : ℝ) * X ∧
        ∀ N ∈ pivotGoodBases X (minimalDepth h s X) s (1 / 1000 : ℝ),
          ‖pivotFiberMean h X (minimalDepth h s X) s
              (pivotCofactor N (minimalDepth h s X) s)‖ ≤ (1 / 100 : ℝ)) :
    DTWPivotResidualDecorrelation :=
  dtw_residual s (fun _ _ => hs) hjoint

/-- The two clauses `dtw_of_fiberMean_and_centered` assumes imply the joint clause at `s = 26`:
the residualiser's interface asks for no more than the hand-written one. -/
theorem joint_of_fiberMean_and_centered
    (hmean : ∀ h : ℕ, 0 < h → ∀ᶠ X : ℕ in atTop,
      ∀ N ∈ pivotGoodBases X (minimalDepth h 26 X) 26 (1 / 1000 : ℝ),
        ‖pivotFiberMean h X (minimalDepth h 26 X) 26
            (pivotCofactor N (minimalDepth h 26 X) 26)‖ ≤ (1 / 100 : ℝ))
    (hcentered : ∀ h : ℕ, 0 < h → ∀ A : ℕ, ∃ X : ℕ, max A 1 ≤ X ∧
      (pivotCenteredCorrelation h X (minimalDepth h 26 X) 26 (1 / 1000 : ℝ)).re
        ≤ (14 / 25 : ℝ) * X) :
    ∀ h : ℕ, 0 < h → ∃ᶠ X in atTop,
      (pivotCenteredCorrelation h X (minimalDepth h 26 X) 26 (1 / 1000 : ℝ)).re
          ≤ (14 / 25 : ℝ) * X ∧
        ∀ N ∈ pivotGoodBases X (minimalDepth h 26 X) 26 (1 / 1000 : ℝ),
          ‖pivotFiberMean h X (minimalDepth h 26 X) 26
              (pivotCofactor N (minimalDepth h 26 X) 26)‖ ≤ (1 / 100 : ℝ) := by
  intro h hh
  have hfreq : ∃ᶠ X in atTop,
      (pivotCenteredCorrelation h X (minimalDepth h 26 X) 26 (1 / 1000 : ℝ)).re
        ≤ (14 / 25 : ℝ) * X := by
    rw [Filter.frequently_atTop]
    intro A
    obtain ⟨X, hX, hc⟩ := hcentered h hh A
    exact ⟨X, le_trans (le_max_left _ _) hX, hc⟩
  exact hfreq.and_eventually (hmean h hh)

/-- **The irrationality of `∑ φ(n) / 2 ^ n` from the prime number theorem and the centred clause
for arbitrarily large `X`**, the second-generation residual. -/
theorem irrational_totient_series_of_primeNumberTheorem_and_frequent_centered
    (hPNT : PrimeNumberTheorem)
    (hc : ∀ h : ℕ, 0 < h → ∃ᶠ X in atTop,
      (pivotCenteredCorrelation h X (minimalDepth h 26 X) 26 (1 / 1000 : ℝ)).re
        ≤ (14 / 25 : ℝ) * X) :
    Irrational (∑' n : ℕ, (Nat.totient n : ℝ) / 2 ^ n) :=
  irrational_totient_series_of_pivotResidualDecorrelation (dtw_residual_gen2 hc fun _ _ => hPNT)

end ErdosProblems.Erdos249.PaperCompleteR21

#print axioms ErdosProblems.Erdos249.PaperCompleteR21.dtw_residual
#print axioms ErdosProblems.Erdos249.PaperCompleteR21.dtw_residual_gen2
#print axioms ErdosProblems.Erdos249.PaperCompleteR21.dtw_of_joint_fiberMean_and_centered
#print axioms ErdosProblems.Erdos249.PaperCompleteR21.joint_of_fiberMean_and_centered
#print axioms ErdosProblems.Erdos249.PaperCompleteR21.irrational_totient_series_of_primeNumberTheorem_and_frequent_centered
