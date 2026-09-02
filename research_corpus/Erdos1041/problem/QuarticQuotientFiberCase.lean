import Mathlib

/-!
# Erdős #1041: the power-map chord-lift metric kernel

The analytic companion proves Erdős #1041 for every translated cyclic lift
`P((z-h)^q)` of a monic quartic `P`, `q>=2`.  It combines Pendyala's attributed
four-point radial lemma with one new metric input: a straight chord in the
quotient has a `q`-th-root lift whose length is at most the sum of the
`1/q`-powers of the endpoint moduli.

In arclength coordinates on the chord's supporting line, the lift density is
`alpha * (sqrt (d^2+x^2))^(alpha-1)`, where `alpha=1/q`.  Since the exponent is
nonpositive, this is bounded by `alpha*x^(alpha-1)` on either half-line, whose
integral is exactly `x^alpha`.  This file kernel-checks those two load-bearing
real inequalities and their strict endpoint-budget consumer.

The covering-space construction of a continuous root lift (split at zero when
necessary), and Pendyala's finite four-point lemma, remain ordinary analytic
inputs in the companion note; neither is postulated as an axiom here.
-/

namespace ErdosProblems.Erdos1041

/-- The `q`-th-root lift density is largest when the supporting line passes
through the origin.  This is the pointwise kernel behind the chord-lift bound. -/
theorem rootLift_kernel_le_axis {alpha d x : ℝ}
    (halpha : alpha ≤ 1) (hx : 0 < x) :
    (Real.sqrt (d ^ 2 + x ^ 2)) ^ (alpha - 1) ≤ x ^ (alpha - 1) := by
  have hxle : x ≤ Real.sqrt (d ^ 2 + x ^ 2) := by
    apply Real.le_sqrt_of_sq_le
    nlinarith [sq_nonneg d]
  exact Real.rpow_le_rpow_of_nonpos hx hxle (sub_nonpos.mpr halpha)

/-- Exact primitive of the axis majorant.  The hypothesis `alpha>0` is exactly
the local integrability condition at a chord crossing the origin. -/
theorem rootLift_axis_integral {alpha A : ℝ}
    (halpha : 0 < alpha) (hA : 0 ≤ A) :
    alpha * (∫ x in (0 : ℝ)..A, x ^ (alpha - 1)) = A ^ alpha := by
  rw [integral_rpow (Or.inl (by linarith : -1 < alpha - 1))]
  rw [show alpha - 1 + 1 = alpha by ring, Real.zero_rpow halpha.ne']
  field_simp [halpha.ne']
  ring

/-- Endpoint moduli strictly below one turn the chord-lift upper bound into the
strict constant-two budget required by Erdős #1041. -/
theorem rootLift_endpoint_budget_lt_two {alpha a b : ℝ}
    (halpha : 0 < alpha)
    (ha0 : 0 ≤ a) (ha1 : a < 1)
    (hb0 : 0 ≤ b) (hb1 : b < 1) :
    a ^ alpha + b ^ alpha < 2 := by
  have ha : a ^ alpha < 1 := Real.rpow_lt_one ha0 ha1 halpha
  have hb : b ^ alpha < 1 := Real.rpow_lt_one hb0 hb1 halpha
  linarith

/-- Abstract fan-in used after constructing a lifted quotient chord: any path
whose length is bounded by the two powered endpoint moduli is strictly shorter
than two. -/
theorem rootLift_length_lt_two_of_le_endpoint_budget
    {alpha a b length : ℝ}
    (halpha : 0 < alpha)
    (ha0 : 0 ≤ a) (ha1 : a < 1)
    (hb0 : 0 ≤ b) (hb1 : b < 1)
    (hlength : length ≤ a ^ alpha + b ^ alpha) :
    length < 2 := by
  exact lt_of_le_of_lt hlength
    (rootLift_endpoint_budget_lt_two halpha ha0 ha1 hb0 hb1)

end ErdosProblems.Erdos1041
