import Mathlib

/-!
# Scalar kernel for the symmetric two-level saddle wall

The analytic companion `SymmetricTwoLevelWallFamily.md` computes the canonical
inverse-ray factors of `(z^m-a^m)(z^m+b^m)`.  This module checks the quartic
shape-slack identities and the exact rational counterexample to the discarded
total-three-arm threshold.
-/

namespace ErdosProblems.Erdos1041.SymmetricTwoLevelWall

/-- Exact slack for one lower/upper pair in the quartic wall family. -/
theorem quartic_pair_slack_identity (r : ℝ) :
    2 * (1 + r ^ 2) - r * (1 + r) ^ 2 =
      (1 - r) * (r ^ 2 + r + 2) := by
  ring

/-- The normalized lower/upper wall pair is at most one for `0 ≤ r ≤ 1`. -/
theorem quartic_pair_square_le_one {r : ℝ} (hr0 : 0 ≤ r) (hr1 : r ≤ 1) :
    r * (1 + r) ^ 2 ≤ 2 * (1 + r ^ 2) := by
  have hshape : 0 ≤ r ^ 2 + r + 2 := by
    positivity
  have hslack : 0 ≤ (1 - r) * (r ^ 2 + r + 2) :=
    mul_nonneg (sub_nonneg.mpr hr1) hshape
  nlinarith [quartic_pair_slack_identity r]

/-- Exact slack for the complete three-critical-point quartic AP product. -/
theorem quartic_full_product_slack_identity (r : ℝ) :
    4 * (1 + r ^ 2) ^ 2 - r * (1 + r) ^ 4 =
      (1 - r) * (r ^ 4 + r ^ 3 + 7 * r ^ 2 + 3 * r + 4) := by
  ring

/-- The complete quartic admissible-product square is at most one. -/
theorem quartic_full_product_square_le_one {r : ℝ}
    (hr0 : 0 ≤ r) (hr1 : r ≤ 1) :
    r * (1 + r) ^ 4 ≤ 4 * (1 + r ^ 2) ^ 2 := by
  have hshape : 0 ≤ r ^ 4 + r ^ 3 + 7 * r ^ 2 + 3 * r + 4 := by
    positivity
  have hslack :
      0 ≤ (1 - r) * (r ^ 4 + r ^ 3 + 7 * r ^ 2 + 3 * r + 4) :=
    mul_nonneg (sub_nonneg.mpr hr1) hshape
  nlinarith [quartic_full_product_slack_identity r]

/-- At `r=9/10` the fourth-power form of the total-three-arm threshold fails. -/
theorem quartic_three_arm_threshold_fourth_power_gap :
    (1 + 2 * (9 / 10 : ℝ)) ^ 4 -
        32 * (9 / 10 : ℝ) * (1 + (9 / 10 : ℝ) ^ 2) =
      5836 / 625 := by
  norm_num

/-- Hence the discarded total-three-arm threshold is not universal. -/
theorem quartic_three_arm_threshold_false :
    32 * (9 / 10 : ℝ) * (1 + (9 / 10 : ℝ) ^ 2) <
      (1 + 2 * (9 / 10 : ℝ)) ^ 4 := by
  norm_num

end ErdosProblems.Erdos1041.SymmetricTwoLevelWall
