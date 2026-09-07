import Mathlib.Tactic

/-!
# Erdős 1041: scalar kernel for the `p = 1` carrier-attachment no-go

For the regular quartic with radius `99/100`, the root-to-origin radial arm is
safe, but the dual product for any common weighted `L1` carrier exceeds one at
the midpoint parameter.  The companion ordinary proof derives the carrier
duality and identifies the exact factor checked here.

This eliminates a containment certificate, not the radial arm, COVER, or the
parent theorem.
-/

namespace ErdosProblems.Erdos1041.PowerMeanCarrierAttachmentNoGo

theorem sqrt_two_gt_seven_fifths :
    (7 / 5 : ℝ) < Real.sqrt 2 := by
  have hs0 : 0 ≤ Real.sqrt 2 := Real.sqrt_nonneg 2
  have hs2 : (Real.sqrt 2) ^ 2 = 2 := by norm_num
  nlinarith

/-- The exact dual product at parameter `1/2` is already above the unit level. -/
theorem quartic_half_dual_product_gt_one :
    (1 : ℝ) <
      (99 / 100 : ℝ) ^ 4 * (3 * (3 + 2 * Real.sqrt 2) / 16) := by
  have hx : 0 < (99 / 100 : ℝ) ^ 4 := by positivity
  have hcoeff :
      (87 / 80 : ℝ) < 3 * (3 + 2 * Real.sqrt 2) / 16 := by
    nlinarith [sqrt_two_gt_seven_fifths]
  have hbase :
      (1 : ℝ) < (99 / 100 : ℝ) ^ 4 * (87 / 80 : ℝ) := by
    norm_num
  have hmul := mul_lt_mul_of_pos_left hcoeff hx
  nlinarith

/-- Along a regular-quartic radial arm the polynomial modulus is strictly below
one away from the root endpoint.  This is the scalar form
`|z^4-r^4| = r^4(1-s^4)` for `0 ≤ s < 1`. -/
theorem quartic_radial_value_lt_one {s : ℝ}
    (hs0 : 0 ≤ s) (hs1 : s < 1) :
    (99 / 100 : ℝ) ^ 4 * (1 - s ^ 4) < 1 := by
  have hs_le : s ≤ 1 := le_of_lt hs1
  have hs2 : s ^ 2 ≤ 1 := by nlinarith [sq_nonneg (s - 1), sq_nonneg s]
  have hs4 : s ^ 4 ≤ 1 := by
    nlinarith [sq_nonneg (s ^ 2 - 1), sq_nonneg (s ^ 2)]
  have hr : (99 / 100 : ℝ) ^ 4 < 1 := by norm_num
  have hr0 : 0 ≤ (99 / 100 : ℝ) ^ 4 := by positivity
  nlinarith [mul_nonneg hr0 (sub_nonneg.mpr hs4)]

end ErdosProblems.Erdos1041.PowerMeanCarrierAttachmentNoGo
