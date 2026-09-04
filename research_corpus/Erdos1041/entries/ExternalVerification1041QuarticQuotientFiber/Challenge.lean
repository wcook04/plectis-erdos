import Mathlib

namespace Erdos249257.ExternalVerification1041QuarticQuotientFiber

/-- The density of a power-map root lift along an offset line is bounded by
the density on the corresponding line through the origin. -/
theorem rootLift_kernel_le_axis {alpha d x : ℝ}
    (halpha : alpha ≤ 1) (hx : 0 < x) :
    (Real.sqrt (d ^ 2 + x ^ 2)) ^ (alpha - 1) ≤ x ^ (alpha - 1) := by
  sorry

/-- Exact primitive of the axis majorant; positivity of `alpha` is the local
integrability condition at a chord crossing the origin. -/
theorem rootLift_axis_integral {alpha A : ℝ}
    (halpha : 0 < alpha) (hA : 0 ≤ A) :
    alpha * (∫ x in (0 : ℝ)..A, x ^ (alpha - 1)) = A ^ alpha := by
  sorry

/-- Two powered endpoint moduli strictly below one have total budget below
the Erdős #1041 threshold two. -/
theorem rootLift_endpoint_budget_lt_two {alpha a b : ℝ}
    (halpha : 0 < alpha)
    (ha0 : 0 ≤ a) (ha1 : a < 1)
    (hb0 : 0 ≤ b) (hb1 : b < 1) :
    a ^ alpha + b ^ alpha < 2 := by
  sorry

/-- Any lifted path controlled by the two powered endpoint moduli is strictly
shorter than two. -/
theorem rootLift_length_lt_two_of_le_endpoint_budget
    {alpha a b length : ℝ}
    (halpha : 0 < alpha)
    (ha0 : 0 ≤ a) (ha1 : a < 1)
    (hb0 : 0 ≤ b) (hb1 : b < 1)
    (hlength : length ≤ a ^ alpha + b ^ alpha) :
    length < 2 := by
  sorry

end Erdos249257.ExternalVerification1041QuarticQuotientFiber
