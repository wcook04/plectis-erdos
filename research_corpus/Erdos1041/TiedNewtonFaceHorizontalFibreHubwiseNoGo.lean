import Mathlib.Data.Complex.Basic
import Mathlib.Tactic

/-!
# Erdős #1041: hubwise horizontal-fibre sign no-go

This module checks the finite algebraic and sign kernel for
`Q(z)=15z+5z²-z⁵`.  The companion note owns the analytic continuation of
the two inverse branches and the passage from their asymptotic sectors to the
horizontal-fibre defect.
-/

namespace ErdosProblems.Erdos1041.TiedNewtonFaceHorizontalFibreHubwiseNoGo

noncomputable section

def q (z : ℂ) : ℂ := 15 * z + 5 * z ^ 2 - z ^ 5
def qDeriv (z : ℂ) : ℂ := 15 + 10 * z - 5 * z ^ 4
def qSecond (z : ℂ) : ℂ := 10 - 20 * z ^ 3

theorem derivative_factorization (z : ℂ) :
    qDeriv z = -5 * (z + 1) * (z ^ 3 - z ^ 2 + z - 3) := by
  dsimp [qDeriv]
  ring

theorem negative_hub_data :
    q (-1) = -9 ∧ qDeriv (-1) = 0 ∧ qSecond (-1) = 30 := by
  norm_num [q, qDeriv, qSecond]

theorem cubic_derivative_positive (x : ℝ) : 0 < 3*x^2 - 2*x + 1 := by
  nlinarith [sq_nonneg (3*x-1)]

theorem cubic_root_value {z : ℂ} (hz : z^3-z^2+z-3=0) :
    q z = 3*z*(z+4) := by
  dsimp [q]
  have h5 : z^5 = 3*z+2*z^2 := by
    linear_combination (z^2+z) * hz
  rw [h5]
  ring

theorem real_cubic_root_value_positive {r : ℝ}
    (_hr : r^3-r^2+r-3=0) (hr1 : 1 < r) :
    0 < 3*r*(r+4) := by
  positivity

theorem real_cubic_root_lt_eight_fifths {r : ℝ}
    (hr : r^3-r^2+r-3=0) : r < 8/5 := by
  by_contra h
  have hra : 8/5 ≤ r := le_of_not_gt h
  have hfactor :
      r^3-r^2+r-3 - (17/125) =
        (r-8/5) * (r^2+(3/5)*r+49/25) := by ring
  have hquad : 0 < r^2+(3/5)*r+49/25 := by
    have hr0 : 0 ≤ r := by linarith
    positivity
  rw [hr] at hfactor
  nlinarith

theorem real_critical_value_lt_twenty_seven {r : ℝ}
    (hr : r^3-r^2+r-3=0) (hr1 : 1 < r) :
    3*r*(r+4) < 27 := by
  have hrU := real_cubic_root_lt_eight_fifths hr
  nlinarith

/-- If the remaining critical values are a conjugate pair, trace zero puts
their common real part strictly above the leftmost value `-9`. -/
theorem conjugate_critical_real_part_above_hub {qr w : ℝ}
    (hqr : qr < 27) (htrace : -9 + qr + 2*w = 0) : -9 < w := by
  linarith

/-- A nonreal root of the critical cubic cannot have real critical value.
The ordinary proof applies this with `x=Re z`, `y=Im z`. -/
theorem nonreal_critical_value_kernel {x y : ℝ}
    (hy : y ≠ 0)
    (hcRe : x^3 - 3*x*y^2 - x^2 + y^2 + x - 3 = 0)
    (hcIm : 3*x^2*y - y^3 - 2*x*y + y = 0) :
    y * (2*x+4) ≠ 0 := by
  intro hreal
  have hx : x = -2 := by
    rcases mul_eq_zero.mp hreal with h | h
    · exact (hy h).elim
    · linarith
  have hy17 : y^2 = 17 := by
    rw [hx] at hcIm
    have : y * (17-y^2) = 0 := by
      nlinarith
    rcases mul_eq_zero.mp this with h | h
    · exact (hy h).elim
    · nlinarith
  rw [hx] at hcRe
  nlinarith

def modelRe (x y : ℝ) : ℝ := 15*x + 5*(x^2-y^2) -
  (x^5-10*x^3*y^2+5*x*y^4)
def modelIm (x y : ℝ) : ℝ := 15*y + 10*x*y -
  (5*x^4*y-10*x^2*y^3+y^5)

theorem imaginary_axis_formula (y : ℝ) :
    modelRe 0 y = -5*y^2 ∧ modelIm 0 y = 15*y-y^5 := by
  constructor <;> simp [modelRe, modelIm]

theorem imaginary_crossing_equation {y : ℝ} (hy : y ≠ 0)
    (hreal : 15*y-y^5=0) : y^4=15 := by
  have := mul_left_cancel₀ hy
    (show y * y^4 = y * 15 by nlinarith)
  nlinarith

theorem crossing_below_hub : -5 * Real.sqrt 15 < (-9 : ℝ) := by
  have hs : 0 ≤ Real.sqrt 15 := Real.sqrt_nonneg 15
  have hs2 : (Real.sqrt 15)^2 = 15 := by norm_num
  nlinarith

def crossingDerivativeRe (_a : ℝ) : ℝ := -60
def crossingDerivativeIm (a : ℝ) : ℝ := 10*a

theorem reciprocal_crossing_real_negative (a : ℝ) :
    crossingDerivativeRe a /
      (crossingDerivativeRe a ^ 2 + crossingDerivativeIm a ^ 2) < 0 := by
  dsimp [crossingDerivativeRe, crossingDerivativeIm]
  have hden : 0 < (-60 : ℝ)^2 + (10*a)^2 := by positivity
  exact div_neg_of_neg_of_pos (by norm_num) hden

/-- The lower bound contributed by the two conjugate fifth-root directions. -/
def projectionDefect : ℝ := (Real.sqrt 5 - 1) / 2

theorem projectionDefect_positive : 0 < projectionDefect := by
  have hs : 0 ≤ Real.sqrt 5 := Real.sqrt_nonneg 5
  have hs2 : (Real.sqrt 5)^2 = 5 := by norm_num
  dsimp [projectionDefect]
  nlinarith

theorem fifth_root_projection_identity :
    2 * ((Real.sqrt 5 - 1) / 4) = projectionDefect := by
  dsimp [projectionDefect]
  ring

end

end ErdosProblems.Erdos1041.TiedNewtonFaceHorizontalFibreHubwiseNoGo
