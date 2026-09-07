import ErdosProblems.Erdos1041.TiedNewtonFaceEvenSymmetricDiameter
import Mathlib.Tactic

/-!
# Erdős #1041: asymmetric diameter-tube kernel

The ordinary theorem obtains the two hypotheses below from finite coefficient
sums on the inner and outer cutoff regions.  Lean checks that either bound is
enough to preserve strict real-axis negativity, and verifies the rational
three-odd-mode witness budgets.
-/

namespace ErdosProblems.Erdos1041.TiedNewtonFaceAsymmetricDiameterTube

theorem inner_domination_neg
    {lead evenPart b perturb budget : ℝ}
    (hlead : 0 ≤ lead) (heven : evenPart ≤ 0)
    (hperturb : |perturb| ≤ budget) (hbudget : b + budget < 0) :
    -lead + evenPart + b + perturb < 0 := by
  have hp : perturb ≤ |perturb| := le_abs_self perturb
  linarith

theorem outer_domination_neg
    {lead evenPart b perturb : ℝ}
    (heven : evenPart ≤ 0) (hb : b < 0)
    (hperturb : |perturb| ≤ lead) :
    -lead + evenPart + b + perturb < 0 := by
  have hp : perturb ≤ |perturb| := le_abs_self perturb
  linarith

theorem two_region_domination_neg
    {lead evenPart b perturb budget : ℝ}
    (hlead : 0 ≤ lead) (heven : evenPart ≤ 0) (hb : b < 0)
    (hbudget : b + budget < 0)
    (hregions : |perturb| ≤ budget ∨ |perturb| ≤ lead) :
    -lead + evenPart + b + perturb < 0 := by
  rcases hregions with hinner | houter
  · exact inner_domination_neg hlead heven hinner hbudget
  · exact outer_domination_neg heven hb houter

theorem two_region_uniform_upper
    {lead evenPart b perturb budget : ℝ}
    (hlead : 0 ≤ lead) (heven : evenPart ≤ 0) (hbudget : 0 ≤ budget)
    (hregions : |perturb| ≤ budget ∨ |perturb| ≤ lead) :
    -lead + evenPart + b + perturb ≤ b + budget := by
  have hp : perturb ≤ |perturb| := le_abs_self perturb
  rcases hregions with hinner | houter <;> linarith

theorem rationalWitness_innerBudget :
    (2 : ℝ) / 100 + 8 / 100 + 32 / 100 = 21 / 50 ∧
      (21 : ℝ) / 50 < 1 := by
  norm_num

theorem rationalWitness_outerBudget :
    (1 / 32 + 1 / 8 + 1 / 2 : ℝ) / 100 = 21 / 3200 ∧
      (21 : ℝ) / 3200 ≤ 1 := by
  norm_num

theorem diameter_length_eq_two_mul
    {R : ℝ} (hR : 0 ≤ R) : |R - (-R)| = 2 * R :=
  TiedNewtonFaceEvenSymmetricDiameter.diameter_length_eq_two_mul hR

end ErdosProblems.Erdos1041.TiedNewtonFaceAsymmetricDiameterTube
