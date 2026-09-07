import Mathlib.Tactic
import Mathlib.Analysis.Real.Pi.Bounds

/-!
# Erdős #1041: scalar kernel for the AGG3 psh tangent cone

The analytic companion `AggregateN3PshUniformityClosure.md` proves that the
first tangent of the cubic arm aggregate is subharmonic and applies a
one-dimensional Wronskian comparison.  This module checks the exact scalar
fan-in used by that argument.  It does not formalize plurisubharmonicity,
distributional limits, uniform inverse-branch asymptotics, or the calculus
maximum principle.
-/

namespace ErdosProblems.Erdos1041.AggregateN3PshUniformity

/-- Pulling `D(phi)` back by the cubic phase `phi = -3 theta` multiplies its
second angular derivative by nine. -/
theorem cubicPhase_tangent_coefficient (D Dpp : ℝ) :
    -2 * D + 9 * (-2 * Dpp) = -2 * (D + 9 * Dpp) := by
  ring

/-- Nonnegative curvature of the subharmonic first tangent gives the exact
phase inequality used by the ordinary analytic proof. -/
theorem phase_curvature_of_tangent_nonneg {D Dpp tangentCurvature : ℝ}
    (hcurv : tangentCurvature = -2 * (D + 9 * Dpp))
    (hnonneg : 0 ≤ tangentCurvature) :
    Dpp + D / 9 ≤ 0 := by
  rw [hcurv] at hnonneg
  nlinarith

/-- Algebraic Wronskian derivative after inserting the comparison equation
`q'' = -q/9`.  The analytic companion supplies the derivative rules. -/
theorem wronskian_derivative_kernel (y ypp q qpp : ℝ)
    (hq : qpp = -q / 9) :
    ypp * q - y * qpp = q * (ypp + y / 9) := by
  rw [hq]
  ring

/-- The comparison operator has frequency `1/3`, strictly below the first
Dirichlet frequency on an interval of length at most `pi`. -/
theorem phase_spectral_gap : (1 / 9 : ℝ) < 1 := by
  norm_num

/-- The elementary wall coefficient used in the phase-uniform lower bound is
strictly positive. -/
theorem wall_elementary_lower_bound_pos :
    0 < (3 * Real.pi - 8) / 16 := by
  have hpi : (3 : ℝ) < Real.pi := Real.pi_gt_three
  nlinarith

/-- Twice the elementary wall bound is the coefficient in the exact
`2 |s| D(phi)` deficit normalization. -/
theorem doubled_wall_lower_bound :
    2 * ((3 * Real.pi - 8) / 16) = (3 * Real.pi - 8) / 8 := by
  ring

end ErdosProblems.Erdos1041.AggregateN3PshUniformity
