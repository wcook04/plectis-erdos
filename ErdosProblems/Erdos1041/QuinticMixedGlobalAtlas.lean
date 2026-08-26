import ErdosProblems.Erdos1041.QuinticEqualityTetrahedron
import Mathlib.Tactic

/-!
# Erdős #1041: certificate kernel for the global quintic mixed atlas

The companion checker covers the normalized coefficient boundary for
`Re (A z + B z² - z⁵)` by finitely many rational stereographic boxes.  This
module kernel-checks the reusable implications consumed by those data:
nonpositive Bernstein controls imply a nonpositive chord, upper coefficient
boxes imply safe sparse ray tails, stereographic coordinates lie on the unit
circle, and the explicit local linear margin absorbs the certified quadratic
remainder throughout the equality-tetrahedron ball.
-/

namespace ErdosProblems.Erdos1041.QuinticMixedGlobalAtlas

/-- A weighted sum is nonpositive when every coefficient is nonpositive and
every weight is nonnegative.  Bernstein chord certificates are instances. -/
theorem weightedSum_nonpos {n : ℕ} (coefficient weight : Fin n → ℝ)
    (hc : ∀ i, coefficient i ≤ 0) (hw : ∀ i, 0 ≤ weight i) :
    ∑ i, coefficient i * weight i ≤ 0 := by
  exact Finset.sum_nonpos fun i _ ↦ mul_nonpos_of_nonpos_of_nonneg (hc i) (hw i)

/-- Box form of the Bernstein implication: it is enough to bound each actual
control by a certified nonpositive upper control. -/
theorem bernsteinUpperControls_nonpos {n : ℕ}
    (actual upper weight : Fin n → ℝ)
    (hactual : ∀ i, actual i ≤ upper i)
    (hupper : ∀ i, upper i ≤ 0)
    (hweight : ∀ i, 0 ≤ weight i) :
    ∑ i, actual i * weight i ≤ 0 := by
  apply weightedSum_nonpos actual weight
  · intro i
    exact (hactual i).trans (hupper i)
  · exact hweight

/-- Rational stereographic coordinates parameterize the unit circle. -/
theorem stereographic_unit (t : ℝ) :
    ((1 - t ^ 2) / (1 + t ^ 2)) ^ 2 +
      (2 * t / (1 + t ^ 2)) ^ 2 = 1 := by
  have hden : 1 + t ^ 2 ≠ 0 := by nlinarith [sq_nonneg t]
  field_simp
  ring

/-- Near the top of the unit circle, the inward normal displacement is
quadratic in the tangent coordinate. -/
theorem unitCircle_normal_le_tangent_sq {normal tangent : ℝ}
    (hnormal : 0 ≤ normal) (hunit : normal ^ 2 + tangent ^ 2 = 1) :
    0 ≤ 1 - normal ∧ 1 - normal ≤ tangent ^ 2 := by
  constructor
  · nlinarith [sq_nonneg (normal - 1)]
  · have hfactor : tangent ^ 2 = (1 - normal) * (1 + normal) := by
      nlinarith
    rw [hfactor]
    nlinarith

/-- Completing the square on a nondegenerate double contact.  The hypothesis
`L² + 4 κ r² ≤ 25 κ` packages the exact connector-by-connector interval
audit: `L` controls the moving-coefficient cross term and `r²` controls the
unit-circle normal value. -/
theorem chordShift_plus_normal_le {delta q kappa L r base cross normal : ℝ}
    (hkappa : 0 < kappa)
    (hbase : base ≤ -kappa * q ^ 2)
    (hcross : cross ≤ L * delta * q)
    (hnormal : normal ≤ r ^ 2 * delta ^ 2)
    (hconstant : L ^ 2 + 4 * kappa * r ^ 2 ≤ 25 * kappa) :
    base + cross + normal ≤ (25 / 4 : ℝ) * delta ^ 2 := by
  have hsquare : 0 ≤ (2 * kappa * q - L * delta) ^ 2 := sq_nonneg _
  nlinarith [mul_nonneg (le_of_lt hkappa) (sq_nonneg delta)]

/-- Interval upper bounds for both Fourier projections can be fed directly
to the endpoint sparse-ray certificate. -/
theorem ray_of_upper_endpoint {a b aUpper bUpper r x : ℝ}
    (ha : a ≤ aUpper) (hb : b ≤ bUpper)
    (hr : 0 ≤ r) (hx : 1 ≤ x)
    (hbUpper : r ^ 2 * bUpper ≤ 0)
    (hendpoint : r * aUpper + r ^ 2 * bUpper - r ^ 5 ≤ 0) :
    r * a * x + r ^ 2 * b * x ^ 2 - r ^ 5 * x ^ 5 ≤ 0 := by
  have hlinear : r * a ≤ r * aUpper := mul_le_mul_of_nonneg_left ha hr
  have hr2 : 0 ≤ r ^ 2 := sq_nonneg r
  have hquadratic : r ^ 2 * b ≤ r ^ 2 * bUpper :=
    mul_le_mul_of_nonneg_left hb hr2
  have hr5 : 0 ≤ r ^ 5 := pow_nonneg hr 5
  have hc : -(r ^ 5) ≤ 0 := neg_nonpos.mpr hr5
  have hsum : r * aUpper + r ^ 2 * bUpper + -(r ^ 5) ≤ 0 := by
    linarith
  have hactual :=
    ErdosProblems.Erdos1041.QuinticCanonicalMixedSlice.sparseRay_nonpos_of_endpoint
      hbUpper hc hsum hx
  have hx0 : 0 ≤ x := le_trans (by norm_num) hx
  have hx2 : 0 ≤ x ^ 2 := sq_nonneg x
  nlinarith [mul_le_mul_of_nonneg_right hlinear hx0,
    mul_le_mul_of_nonneg_right hquadratic hx2]

/-- The positive-quadratic sparse ray uses the decreasing-quartic condition,
again only at interval upper projections. -/
theorem ray_of_upper_quarticDrop {a b aUpper bUpper r x : ℝ}
    (ha : a ≤ aUpper) (hb : b ≤ bUpper)
    (hr : 0 ≤ r) (hx : 1 ≤ x)
    (hendpoint : r * aUpper + r ^ 2 * bUpper - r ^ 5 ≤ 0)
    (hdrop : r ^ 2 * bUpper - 4 * r ^ 5 ≤ 0) :
    r * a * x + r ^ 2 * b * x ^ 2 - r ^ 5 * x ^ 5 ≤ 0 := by
  have hlinear : r * a ≤ r * aUpper := mul_le_mul_of_nonneg_left ha hr
  have hr2 : 0 ≤ r ^ 2 := sq_nonneg r
  have hquadratic : r ^ 2 * b ≤ r ^ 2 * bUpper :=
    mul_le_mul_of_nonneg_left hb hr2
  have hr5 : 0 ≤ r ^ 5 := pow_nonneg hr 5
  have hc : -(r ^ 5) ≤ 0 := neg_nonpos.mpr hr5
  have hsum : r * aUpper + r ^ 2 * bUpper + -(r ^ 5) ≤ 0 := by
    linarith
  have hdrop' : r ^ 2 * bUpper + 4 * -(r ^ 5) ≤ 0 := by
    linarith
  have hupper :=
    ErdosProblems.Erdos1041.QuinticCanonicalMixedSlice.sparseRay_nonpos_of_quartic_drop
      hc hsum hdrop' hx
  have hx0 : 0 ≤ x := le_trans (by norm_num) hx
  have hx2 : 0 ≤ x ^ 2 := sq_nonneg x
  nlinarith [mul_le_mul_of_nonneg_right hlinear hx0,
    mul_le_mul_of_nonneg_right hquadratic hx2]

/-- The explicit equality-ball constants used by the atlas: a first-order
margin `59/1000` beats a quadratic error coefficient `8` throughout the
declared radius `17/2500`. -/
theorem equalityBall_margin {delta linear remainder : ℝ}
    (hdelta : 0 < delta) (hradius : delta ≤ (17 : ℝ) / 2500)
    (hlinear : linear ≤ -((59 : ℝ) / 1000) * delta)
    (hremainder : remainder ≤ 8 * delta ^ 2) :
    linear + remainder < 0 := by
  nlinarith

end ErdosProblems.Erdos1041.QuinticMixedGlobalAtlas
