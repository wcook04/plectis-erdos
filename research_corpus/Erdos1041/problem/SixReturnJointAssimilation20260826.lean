import Mathlib.Tactic

/-!
# Erdős 1041: scalar kernels from the six-return joint assimilation

The analytic and geometric theorems are proved in the companion Markdown
source.  This module checks the new algebraic fan-in introduced by the local
assimilation: retaining singleton leaf area strictly strengthens the returned
lifetime budget, the improved spectral convexity constant propagates through
a finite sum, and the critical-pole dispersion term gives nonnegative combined
charge once the conditional trace estimate is supplied.
-/

namespace ErdosProblems.Erdos1041.SixReturnJointAssimilation20260826

/-- Decomposing the returned full-FE maximum produces a positive excess charge
on every nontrivial node, in addition to the singleton leaf charge. -/
theorem fullEnergyChargedLifetimeBudget
    {lifetime nodeExcess leafCharge degree : ℝ}
    (hbudget :
      2 * lifetime + nodeExcess + leafCharge / 2 < degree / 2) :
    lifetime + nodeExcess / 2 + leafCharge / 4 < degree / 4 := by
  linarith

/-- The leaf-charged lifetime inequality is exactly the returned lifetime
budget plus one quarter of the singleton entrance energy. -/
theorem leafChargedLifetimeBudget
    {lifetime nodeExcess leafCharge degree : ℝ}
    (hexcess : 0 ≤ nodeExcess)
    (hbudget :
      2 * lifetime + nodeExcess + leafCharge / 2 < degree / 2) :
    lifetime + leafCharge / 4 < degree / 4 := by
  linarith

/-- A positive singleton charge makes the new lifetime budget strictly
stronger than the uncharged `lifetime < degree / 4` conclusion. -/
theorem leafChargedLifetime_strictImprovement
    {lifetime leafCharge degree : ℝ}
    (hleaf : 0 < leafCharge)
    (hbudget : lifetime + leafCharge / 4 < degree / 4) :
    lifetime < degree / 4 := by
  linarith

/-- Finite aggregation of the improved scalar spectral estimate.  The
ordinary proof supplies `sq i <= 2*M*phi i` with only one power of `M`; this
lemma checks that no further dimension factor is introduced at fan-in. -/
theorem spectralDeviation_sum_le
    {ι : Type*} [Fintype ι]
    (sq phi : ι → ℝ) {M budget : ℝ}
    (hpoint : ∀ i, sq i ≤ 2 * M * phi i)
    (hphi : ∑ i, phi i ≤ budget)
    (hM : 0 ≤ M) :
    ∑ i, sq i ≤ 2 * M * budget := by
  calc
    ∑ i, sq i ≤ ∑ i, 2 * M * phi i :=
      Finset.sum_le_sum fun i _ => hpoint i
    _ = 2 * M * ∑ i, phi i := by rw [Finset.mul_sum]
    _ ≤ 2 * M * budget := by
      exact mul_le_mul_of_nonneg_left hphi (mul_nonneg (by norm_num) hM)

/-- The conditional critical-pole trace bound yields the quantitative
dispersion credit in the combined charge. -/
theorem criticalPoleTrace_charge
    {treeLength radius multiplicity dispersion : ℝ}
    (htrace :
      treeLength ≤
        2 * radius * multiplicity - dispersion / (2 * radius)) :
    dispersion / (2 * radius) ≤
      2 * radius * multiplicity - treeLength := by
  linarith

/-- Nonnegative critical dispersion closes the returned component charge once
the critical-pole trace estimate is available. -/
theorem criticalPoleTrace_charge_nonneg
    {treeLength radius multiplicity dispersion : ℝ}
    (hradius : 0 < radius)
    (hdispersion : 0 ≤ dispersion)
    (htrace :
      treeLength ≤
        2 * radius * multiplicity - dispersion / (2 * radius)) :
    0 ≤ 2 * radius * multiplicity - treeLength := by
  have hcredit := criticalPoleTrace_charge htrace
  have hden : 0 < 2 * radius := by positivity
  have : 0 ≤ dispersion / (2 * radius) := div_nonneg hdispersion hden.le
  linarith

end ErdosProblems.Erdos1041.SixReturnJointAssimilation20260826
