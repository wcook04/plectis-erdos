import Mathlib
import ErdosProblems.Erdos1041.QuarticQuotientFiberCase

namespace Erdos249257.ExternalVerification1041QuarticQuotientFiber

theorem rootLift_kernel_le_axis {alpha d x : ℝ}
    (halpha : alpha ≤ 1) (hx : 0 < x) :
    (Real.sqrt (d ^ 2 + x ^ 2)) ^ (alpha - 1) ≤ x ^ (alpha - 1) :=
  ErdosProblems.Erdos1041.rootLift_kernel_le_axis halpha hx

theorem rootLift_axis_integral {alpha A : ℝ}
    (halpha : 0 < alpha) (hA : 0 ≤ A) :
    alpha * (∫ x in (0 : ℝ)..A, x ^ (alpha - 1)) = A ^ alpha :=
  ErdosProblems.Erdos1041.rootLift_axis_integral halpha hA

theorem rootLift_endpoint_budget_lt_two {alpha a b : ℝ}
    (halpha : 0 < alpha)
    (ha0 : 0 ≤ a) (ha1 : a < 1)
    (hb0 : 0 ≤ b) (hb1 : b < 1) :
    a ^ alpha + b ^ alpha < 2 :=
  ErdosProblems.Erdos1041.rootLift_endpoint_budget_lt_two
    halpha ha0 ha1 hb0 hb1

theorem rootLift_length_lt_two_of_le_endpoint_budget
    {alpha a b length : ℝ}
    (halpha : 0 < alpha)
    (ha0 : 0 ≤ a) (ha1 : a < 1)
    (hb0 : 0 ≤ b) (hb1 : b < 1)
    (hlength : length ≤ a ^ alpha + b ^ alpha) :
    length < 2 :=
  ErdosProblems.Erdos1041.rootLift_length_lt_two_of_le_endpoint_budget
    halpha ha0 ha1 hb0 hb1 hlength

end Erdos249257.ExternalVerification1041QuarticQuotientFiber
