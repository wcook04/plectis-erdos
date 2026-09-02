import ErdosProblems.Erdos1041.TiedNewtonFaceAsymmetricDiameterTube
import Mathlib.Tactic

/-!
# Erdős #1041: complex rotated-diameter kernel

The ordinary theorem applies the monomial bound below to a finite coefficient
sum on a rotated line.  The two-region real domination is inherited from the
asymmetric-tube module.
-/

namespace ErdosProblems.Erdos1041.TiedNewtonFaceComplexDiameterTube

theorem realPart_le_norm (z : ℂ) : z.re ≤ ‖z‖ :=
  (le_abs_self z.re).trans (Complex.abs_re_le_norm z)

theorem rotatedMonomial_re_le
    (c u : ℂ) (t : ℝ) (j : ℕ) (hu : ‖u‖ = 1) :
    (c * (((t : ℂ) * u) ^ j)).re ≤ ‖c‖ * |t| ^ j := by
  calc
    (c * (((t : ℂ) * u) ^ j)).re
        ≤ ‖c * (((t : ℂ) * u) ^ j)‖ := realPart_le_norm _
    _ = ‖c‖ * |t| ^ j := by
      rw [norm_mul, norm_pow, norm_mul, Complex.norm_real, hu]
      simp [Real.norm_eq_abs]

theorem uniformMargin_of_twoRegion
    {lead evenPart b perturb budget : ℝ}
    (hlead : 0 ≤ lead) (heven : evenPart ≤ 0) (hbudget : 0 ≤ budget)
    (hregions : |perturb| ≤ budget ∨ |perturb| ≤ lead) :
    -lead + evenPart + b + perturb ≤ b + budget :=
  TiedNewtonFaceAsymmetricDiameterTube.two_region_uniform_upper
    hlead heven hbudget hregions

theorem witnessBudgets :
    (2 / 50 + 8 / 50 : ℝ) = 1 / 5 ∧
      ((1 / 8 + 1 / 2) / 50 : ℝ) = 1 / 80 ∧
      (-1 : ℝ) + 1 / 5 = -4 / 5 := by
  norm_num

end ErdosProblems.Erdos1041.TiedNewtonFaceComplexDiameterTube
