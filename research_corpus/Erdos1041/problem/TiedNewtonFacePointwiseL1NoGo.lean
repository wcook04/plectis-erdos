import Mathlib.Tactic

/-!
# Erdős #1041: rational kernel for the pointwise full-fibre L1 no-go

The companion note constructs a degree-six polynomial whose critical values
are strictly in the left half-plane and computes an exact fibre speed sum
larger than six.  This module checks the rational bounds used to compare the
radical expression with six.  The polynomial factorization and inverse-branch
calculus remain ordinary mathematics.
-/

namespace ErdosProblems.Erdos1041.TiedNewtonFacePointwiseL1NoGo

noncomputable section

def x : ℝ := 1001 / 1000
def a0 : ℝ := 31748 / 10000
def d1 : ℝ := 20031 / 10000
def d2 : ℝ := 44759 / 10000

theorem epsilon_pos : 0 < x ^ 3 + 3 * x - 4 := by
  norm_num [x]

/-- `a0` is a strict rational lower bound for the positive cube root of 32. -/
theorem a0_cube_lt_thirtyTwo : a0 ^ 3 < 32 := by
  norm_num [a0]

/-- Squaring verifies the first positive denominator upper bound. -/
theorem firstDenominator_sq_lt_d1_sq :
    x * (x ^ 2 + 1) ^ 2 < d1 ^ 2 := by
  norm_num [x, d1]

/-- Taking fourth powers verifies the second positive denominator bound. -/
theorem secondDenominator_fourth_lt_d2_fourth :
    (x ^ 2 + 3) * ((x ^ 2 + 1) * (x ^ 2 + 4)) ^ 2 < d2 ^ 4 := by
  norm_num [x, d2]

/-- The final lower estimate is already strictly larger than six. -/
theorem rational_lower_sum_gt_six :
    6 < 2 * a0 / d1 + 4 * a0 / d2 := by
  norm_num [a0, d1, d2]

/-- Monotonicity adapter from the three strict radical bounds to the final
speed inequality. -/
theorem totalSpeed_gt_six_of_bounds
    {a firstDenominator secondDenominator : ℝ}
    (ha : a0 < a)
    (hfirstPos : 0 < firstDenominator)
    (hfirst : firstDenominator < d1)
    (hsecondPos : 0 < secondDenominator)
    (hsecond : secondDenominator < d2) :
    6 < 2 * a / firstDenominator + 4 * a / secondDenominator := by
  have ha0Pos : 0 < a0 := by norm_num [a0]
  have hd1Pos : 0 < d1 := by norm_num [d1]
  have hd2Pos : 0 < d2 := by norm_num [d2]
  have hcross1 : a0 * firstDenominator < a * d1 := by
    calc
      a0 * firstDenominator < a0 * d1 :=
        mul_lt_mul_of_pos_left hfirst ha0Pos
      _ < a * d1 := mul_lt_mul_of_pos_right ha hd1Pos
  have hcross2 : a0 * secondDenominator < a * d2 := by
    calc
      a0 * secondDenominator < a0 * d2 :=
        mul_lt_mul_of_pos_left hsecond ha0Pos
      _ < a * d2 := mul_lt_mul_of_pos_right ha hd2Pos
  have hterm1 : 2 * a0 / d1 < 2 * a / firstDenominator := by
    apply (div_lt_div_iff₀ hd1Pos hfirstPos).2
    nlinarith
  have hterm2 : 4 * a0 / d2 < 4 * a / secondDenominator := by
    apply (div_lt_div_iff₀ hd2Pos hsecondPos).2
    nlinarith
  nlinarith [rational_lower_sum_gt_six]

end

end ErdosProblems.Erdos1041.TiedNewtonFacePointwiseL1NoGo
