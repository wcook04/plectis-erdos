import Mathlib.Tactic

/-!
# Erdős #1041: scalar kernel for the complete four-point free-point theorem

The analytic companion `FreePointZeroInsertionFP4Matching.md` proves `FP₄`
by a central/outer dichotomy at squared radius `21/25`.  This module checks
the reusable algebraic kernel of the outer argument: the three-variable
pair-product estimate, monotonicity in the largest squared radius, and the
exact positive radical slack at the sole stationary point.  The logarithmic
energy identity, exponential Taylor bounds, Hölder step, and calculus fan-in
remain ordinary analytic mathematics in the companion note.
-/

namespace ErdosProblems.Erdos1041.FreePointFP4Complete

/-- For three real variables, the sum of pair products is at most one third
of the square of their sum.  This is the exact symmetric estimate used after
separating the largest squared radius from the other three. -/
theorem three_mul_pairProduct_le_sum_sq (x y z : ℝ) :
    3 * (x * y + x * z + y * z) ≤ (x + y + z) ^ 2 := by
  nlinarith [sq_nonneg (x - y), sq_nonneg (x - z), sq_nonneg (y - z)]

/-- The derivative numerator of the outer radial majorant is strictly
positive in the largest-radius variable once `a ≥ 21/25`. -/
theorem outer_radius_derivative_numerator_pos {a s : ℝ}
    (ha : (21 / 25 : ℝ) ≤ a) (hs : 0 ≤ s) :
    0 < 5 * a + (5 * a - 7) * s + (11 / 3) * s ^ 2 := by
  have hprod : 0 ≤ (a - 21 / 25) * (1 + s) :=
    mul_nonneg (by linarith) (by linarith)
  have hsq : 0 ≤ (55 * s - 21) ^ 2 := sq_nonneg (55 * s - 21)
  nlinarith

/-- The unique nonnegative stationary point of the one-variable outer
majorant satisfies its exact quadratic equation. -/
theorem outer_stationary_equation :
    let s₀ : ℝ := (-27 + 3 * Real.sqrt 473) / 50
    625 * s₀ ^ 2 + 675 * s₀ - 882 = 0 := by
  dsimp
  have hsqrt : (Real.sqrt (473 : ℝ)) ^ 2 = 473 := by norm_num
  nlinarith

/-- The stationary point lies in the physical interval for the sum of the
three smaller squared radii. -/
theorem outer_stationary_mem_interval :
    let s₀ : ℝ := (-27 + 3 * Real.sqrt 473) / 50
    0 < s₀ ∧ s₀ < 3 := by
  dsimp
  have hsqrt_nonneg : 0 ≤ Real.sqrt (473 : ℝ) := Real.sqrt_nonneg _
  have hsqrt_sq : (Real.sqrt (473 : ℝ)) ^ 2 = 473 := by norm_num
  constructor <;> nlinarith

/-- Exact integer comparison behind the strict squared slack at the outer
stationary point. -/
theorem outer_stationary_radical_numerator_pos :
    0 < (160789265544645 : ℝ)
      - 7334791379487 * Real.sqrt 473 := by
  have hsqrt_nonneg : 0 ≤ Real.sqrt (473 : ℝ) := Real.sqrt_nonneg _
  have hsqrt_sq : (Real.sqrt (473 : ℝ)) ^ 2 = 473 := by norm_num
  have hsq :
      (7334791379487 * Real.sqrt (473 : ℝ)) ^ 2
        < (160789265544645 : ℝ) ^ 2 := by
    rw [mul_pow, hsqrt_sq]
    norm_num
  nlinarith

/-- The exact positive value of `3456 - X²D³` at the stationary point,
in the radical normal form used by the analytic proof. -/
theorem outer_stationary_squared_slack_pos :
    0 < (32157853108929 : ℝ) / 61035156250
      - 7334791379487 * Real.sqrt 473 / 305175781250 := by
  have h := outer_stationary_radical_numerator_pos
  nlinarith

end ErdosProblems.Erdos1041.FreePointFP4Complete
