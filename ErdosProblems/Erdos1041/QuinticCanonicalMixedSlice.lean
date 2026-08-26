import Mathlib.Tactic

/-!
# Erdős #1041: the canonical quintic mixed slice

The analytic certificate for `Re (u z + I z^2 - z^5)` has two tangent
connectors separated by the sharp amplitude `u_*^3 = 27/320`.  This module
kernel-checks the load-bearing algebra: a double-contact chord is nonpositive
when its residual convex quadratic is nonpositive at both endpoints, the two
sparse ray-tail criteria, and monotone transfer of a connector to one side of
the transition amplitude.

The exact fifth-cyclotomic substitutions and factor coefficients are replayed
symbolically by the companion checker.  They instantiate these general
lemmas without any numerical tolerance.
-/

namespace ErdosProblems.Erdos1041.QuinticCanonicalMixedSlice

/-- A convex quadratic which is nonpositive at both endpoints is nonpositive
on the full unit interval. -/
theorem convexQuadratic_nonpos {a b c t : ℝ}
    (ha : 0 ≤ a) (hc : c ≤ 0) (hsum : a + b + c ≤ 0)
    (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    a * t ^ 2 + b * t + c ≤ 0 := by
  have htm : 0 ≤ 1 - t := sub_nonneg.mpr ht1
  have hcurve : 0 ≤ a * t * (1 - t) := by positivity
  have hsecant :
      a * t ^ 2 + b * t + c ≤ (1 - t) * c + t * (a + b + c) := by
    nlinarith
  have hleft : (1 - t) * c ≤ 0 := mul_nonpos_of_nonneg_of_nonpos htm hc
  have hright : t * (a + b + c) ≤ 0 :=
    mul_nonpos_of_nonneg_of_nonpos ht0 hsum
  linarith

/-- Multiplying the preceding quadratic by a double-contact square preserves
nonpositivity.  This is the exact shape of both critical chords. -/
theorem doubleContactChord_nonpos {t₀ a b c t : ℝ}
    (ha : 0 ≤ a) (hc : c ≤ 0) (hsum : a + b + c ≤ 0)
    (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    (t - t₀) ^ 2 * (a * t ^ 2 + b * t + c) ≤ 0 := by
  exact mul_nonpos_of_nonneg_of_nonpos (sq_nonneg (t - t₀))
    (convexQuadratic_nonpos ha hc hsum ht0 ht1)

/-- A positive linear ray term is absorbed by nonpositive quadratic and
quintic terms once their sum is already nonpositive at radius one. -/
theorem sparseRay_nonpos_of_endpoint {a b c x : ℝ}
    (hb : b ≤ 0) (hc : c ≤ 0)
    (hsum : a + b + c ≤ 0) (hx : 1 ≤ x) :
    a * x + b * x ^ 2 + c * x ^ 5 ≤ 0 := by
  have hx0 : 0 ≤ x := le_trans (by norm_num) hx
  have hx2 : x ≤ x ^ 2 := by nlinarith
  have hx4 : 1 ≤ x ^ 4 := one_le_pow₀ hx
  have hx5 : x ≤ x ^ 5 := by
    calc
      x = x * 1 := by ring
      _ ≤ x * x ^ 4 := mul_le_mul_of_nonneg_left hx4 hx0
      _ = x ^ 5 := by ring
  have hb' : b * x ^ 2 ≤ b * x := mul_le_mul_of_nonpos_left hx2 hb
  have hc' : c * x ^ 5 ≤ c * x := mul_le_mul_of_nonpos_left hx5 hc
  have hscale : x * (a + b + c) ≤ 0 :=
    mul_nonpos_of_nonneg_of_nonpos hx0 hsum
  nlinarith

/-- The only ray with a positive quadratic term is controlled by factoring
out `x`: its residual quartic is decreasing after radius one. -/
theorem sparseRay_nonpos_of_quartic_drop {a b c x : ℝ}
    (hc : c ≤ 0) (hsum : a + b + c ≤ 0)
    (hdrop : b + 4 * c ≤ 0) (hx : 1 ≤ x) :
    a * x + b * x ^ 2 + c * x ^ 5 ≤ 0 := by
  have hx0 : 0 ≤ x := le_trans (by norm_num) hx
  have h2 : 1 ≤ x ^ 2 := one_le_pow₀ hx
  have h3 : 1 ≤ x ^ 3 := one_le_pow₀ hx
  have hsum4 : 4 ≤ x ^ 3 + x ^ 2 + x + 1 := by nlinarith
  have hbracket : b + c * (x ^ 3 + x ^ 2 + x + 1) ≤ 0 := by
    have hc' : c * (x ^ 3 + x ^ 2 + x + 1) ≤ c * 4 :=
      mul_le_mul_of_nonpos_left hsum4 hc
    linarith
  have hxm : 0 ≤ x - 1 := sub_nonneg.mpr hx
  have hdelta :
      b * (x - 1) + c * (x ^ 4 - 1) ≤ 0 := by
    have hid : x ^ 4 - 1 = (x - 1) * (x ^ 3 + x ^ 2 + x + 1) := by ring
    rw [hid]
    nlinarith [mul_nonpos_of_nonneg_of_nonpos hxm hbracket]
  have hresidual : a + b * x + c * x ^ 4 ≤ 0 := by nlinarith
  calc
    a * x + b * x ^ 2 + c * x ^ 5 = x * (a + b * x + c * x ^ 4) := by ring
    _ ≤ 0 := mul_nonpos_of_nonneg_of_nonpos hx0 hresidual

/-- If the coefficient projection on a connector is nonnegative, decreasing
the first-mode amplitude preserves its certificate. -/
theorem transfer_down_of_nonneg_projection {u u₀ p base : ℝ}
    (hu : u ≤ u₀) (hp : 0 ≤ p) (hbase : base ≤ 0) :
    base + (u - u₀) * p ≤ 0 := by
  have hdu : u - u₀ ≤ 0 := sub_nonpos.mpr hu
  exact add_nonpos hbase (mul_nonpos_of_nonpos_of_nonneg hdu hp)

/-- If the coefficient projection is nonpositive, increasing the first-mode
amplitude preserves its certificate. -/
theorem transfer_up_of_nonpos_projection {u u₀ p base : ℝ}
    (hu : u₀ ≤ u) (hp : p ≤ 0) (hbase : base ≤ 0) :
    base + (u - u₀) * p ≤ 0 := by
  have hdu : 0 ≤ u - u₀ := sub_nonneg.mpr hu
  exact add_nonpos hbase (mul_nonpos_of_nonneg_of_nonpos hdu hp)

/-- The two tangent connectors cover every nonnegative amplitude once their
opposite projection signs and their base certificates are known. -/
theorem twoConnector_amplitude_cover {u u₀ leftProjection rightProjection
    leftBase rightBase : ℝ}
    (hpLeft : 0 ≤ leftProjection) (hpRight : rightProjection ≤ 0)
    (hLeft : leftBase ≤ 0) (hRight : rightBase ≤ 0) :
    (leftBase + (u - u₀) * leftProjection ≤ 0) ∨
      (rightBase + (u - u₀) * rightProjection ≤ 0) := by
  rcases le_total u u₀ with hu | hu
  · exact Or.inl (transfer_down_of_nonneg_projection hu hpLeft hLeft)
  · exact Or.inr (transfer_up_of_nonpos_projection hu hpRight hRight)

/-- The right-hand cyclotomic scaling has exactly the same sharp transition
amplitude as the left-hand connector. -/
theorem rightScaling_transitionCube {w : ℝ}
    (hw : w ^ 4 - 20 * w ^ 2 + 80 = 0) :
    (3 * w ^ 2 / 80) ^ 3 * (15 - w ^ 2) = (27 : ℝ) / 320 := by
  ring_nf at hw ⊢
  linear_combination (-27 * (w ^ 4 + 5 * w ^ 2 + 20) / 512000) * hw

end ErdosProblems.Erdos1041.QuinticCanonicalMixedSlice
