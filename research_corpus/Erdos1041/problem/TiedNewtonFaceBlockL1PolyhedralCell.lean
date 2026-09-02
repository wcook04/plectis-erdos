import ErdosProblems.Erdos1041.TiedNewtonFaceBlockL1RationalChart

/-!
# Erdős #1041: exact consumer kernel for the block-L1 polyhedral chart

The companion note eliminates all coefficient inequalities for one fixed
hub/end/cutoff template.  This module checks the generic affine-cell consumer,
the tail endpoint identity, and the derivative/critical-value kernels.
-/

namespace ErdosProblems.Erdos1041.TiedNewtonFaceBlockL1PolyhedralCell

noncomputable section

def radius : ℝ := 5 / 4
def aMin : ℝ := -(1875 / 128)
def v6T : ℝ := -(15625 / 4096)
def v6S : ℝ := -(25 / 32)

def armControl (T S a b : ℝ) : ℝ := T + a * S + b
def tailV (a b r : ℝ) : ℝ := -r ^ 6 - (a / 2) * r ^ 2 + b

theorem cell_control_neg
    {T S a b : ℝ} (h : b < -T - a * S) :
    armControl T S a b < 0 := by
  dsimp [armControl]
  linarith

theorem aMin_eq_derivative_threshold : aMin = -6 * radius ^ 4 := by
  norm_num [aMin, radius]

theorem tailV_cutoff_eq_v6Control (a b : ℝ) :
    tailV a b radius = armControl v6T v6S a b := by
  norm_num [tailV, armControl, radius, v6T, v6S]
  ring

theorem tail_derivativeBracket_neg
    {a r : ℝ} (ha : aMin < a) (hr4 : radius ^ 4 ≤ r ^ 4) :
    -6 * r ^ 4 - a < 0 := by
  rw [aMin_eq_derivative_threshold] at ha
  nlinarith

theorem tailV_derivative_factor (a r : ℝ) :
    -6 * r ^ 5 - a * r = r * (-6 * r ^ 4 - a) := by
  ring

theorem criticalValue_realPart (a b y : ℝ) :
    Complex.re ((b : ℂ) + ((2 * a / 3 : ℝ) : ℂ) * (y * Complex.I)) = b := by
  simp

theorem topology_parameter_signs
    {a b : ℝ} (ha : a < 0) (hb : b < 0) : a ≠ 0 ∧ b < 0 := by
  constructor
  · linarith
  · exact hb

end

end ErdosProblems.Erdos1041.TiedNewtonFaceBlockL1PolyhedralCell
