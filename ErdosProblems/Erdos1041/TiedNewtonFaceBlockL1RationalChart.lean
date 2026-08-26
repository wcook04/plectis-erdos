import ErdosProblems.Erdos1041.TiedNewtonFaceBlockL1RationalRescue

/-!
# Erdős #1041: perturbation kernel for the rational block-L1 chart

The companion note upgrades the strict sextic rescue to an explicit
two-parameter coefficient box.  This module checks the uniform perturbation
estimate and the endpoint arithmetic used by the chart certificate.
-/

namespace ErdosProblems.Erdos1041.TiedNewtonFaceBlockL1RationalChart

noncomputable section

def rho : ℝ := 1 / 192
def epsilon : ℝ := -(5997001 / 1000000000)
def aLower : ℝ := -(577 / 192)
def aUpper : ℝ := -(575 / 192)
def bUpper : ℝ := epsilon + rho
def radius : ℝ := 5 / 4
def controllingRadius : ℝ := 20577415197 / 3931840000000

theorem rho_pos : 0 < rho := by
  norm_num [rho]

theorem parameter_signs : aUpper < 0 ∧ bUpper < 0 := by
  norm_num [aUpper, bUpper, epsilon, rho]

/-- `1/192` is the largest reciprocal-integer radius below the controlling
arm threshold for this fixed template. -/
theorem reciprocalIntegerRadius_sharp :
    rho < controllingRadius ∧ controllingRadius < 1 / 191 := by
  norm_num [rho, controllingRadius]

/-- An exact per-control sensitivity budget and a `rho`-box in the two
coefficients preserve strict negativity. -/
theorem perturbed_control_neg
    {base sens deltaA deltaB : ℝ}
    (hbudget : base + rho * |sens| + rho < 0)
    (hA : |deltaA| ≤ rho)
    (hB : |deltaB| ≤ rho) :
    base + deltaA * sens + deltaB < 0 := by
  have hsa : 0 ≤ |sens| := abs_nonneg sens
  have hprod : |deltaA * sens| ≤ rho * |sens| := by
    rw [abs_mul]
    exact mul_le_mul_of_nonneg_right hA hsa
  have hterm : deltaA * sens ≤ rho * |sens| :=
    le_trans (le_abs_self (deltaA * sens)) hprod
  have hdeltaB : deltaB ≤ rho :=
    le_trans (le_abs_self deltaB) hB
  linarith

/-- The critical-value formula has real part `b` when the squared critical
point is purely imaginary. -/
theorem criticalValue_realPart
    (a b y : ℝ) :
    Complex.re ((b : ℂ) + ((2 * a / 3 : ℝ) : ℂ) * (y * Complex.I)) = b := by
  simp

def worstTailV (r : ℝ) : ℝ := -r ^ 6 - (aLower / 2) * r ^ 2 + bUpper

theorem derivativeBracket_at_radius_neg :
    -6 * radius ^ 4 - aLower = -(4471 / 384) ∧
      -(4471 / 384 : ℝ) < 0 := by
  norm_num [radius, aLower]

theorem worstTailV_at_radius :
    worstTailV radius = -(11741335383 / 8000000000) ∧
      -(11741335383 / 8000000000 : ℝ) < 0 := by
  norm_num [worstTailV, radius, aLower, bUpper, epsilon, rho]

/-- Algebraic form of the uniform `v`-tail derivative. -/
theorem worstTailV_derivative_factor (r : ℝ) :
    -6 * r ^ 5 - aLower * r = r * (-6 * r ^ 4 - aLower) := by
  ring

end

end ErdosProblems.Erdos1041.TiedNewtonFaceBlockL1RationalChart
