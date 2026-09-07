import Mathlib.Tactic

/-!
# Erdős 1041: seventh-return sextic scalar kernel

The companion note proves the complex root-of-unity selection theorem.  This
module checks its load-bearing scalar consequences and the exact counterexample
that prevents conflating the low and paired sextic models.
-/

namespace ErdosProblems.Erdos1041.SeventhReturnSexticAssimilation20260826

/-- The unpaired low ray is positive at the boundary data used by the invalid
model splice. -/
theorem low_ray_boundary_witness :
    (-(3 / 8 : ℚ)) * (1 / 2) + (1 / 2) ^ 2 - (1 / 2) ^ 6 = 3 / 64 := by
  norm_num

/-- The paired ray at the same scalar data is strictly negative. -/
theorem paired_ray_boundary_witness :
    (-(3 / 8 : ℚ)) * ((1 / 2) - (1 / 2) ^ 5) +
        ((1 / 2) ^ 2 - (1 / 2) ^ 4) - (1 / 2) ^ 6 = -(1 / 256) := by
  norm_num

/-- The parameterized Nyquist threshold cancels the worst noncubic chord
Lipschitz rise. -/
theorem nyquist_threshold_cancels
    {alpha C sqrtThree : ℝ}
    (h : 4 * (alpha + 8) ≤ 3 * sqrtThree * C) :
    alpha + 8 ≤ C * (3 * sqrtThree / 4) := by
  linarith

/-- The selected endpoint margin is positive throughout the normalized
all-amplitude chart. -/
theorem endpoint_margin_pos
    {alpha sqrtThree : ℝ} (ha : alpha ≤ 1) (hs : sqrtThree < 2) :
    0 < (3 - alpha - sqrtThree) / 3 := by
  linarith

/-- Once the cubic slope dominates the noncubic Lipschitz rise, the endpoint
margin propagates across the whole chord. -/
theorem chord_margin_of_slope_cancellation
    {value margin slope cubicSlope d : ℝ}
    (hvalue : value ≤ -margin + slope * d)
    (hcubic : cubicSlope ≤ -slope * d) :
    value + cubicSlope ≤ -margin := by
  linarith

/-- The return's fixed radius `1/64` is valid up to cubic amplitude `512`, not
only `470`. -/
theorem fixed_radius_valid_through_512
    {C : ℝ} (hC0 : 0 ≤ C) (hC : C ≤ 512) :
    8 * C * (1 / 64 : ℝ) ^ 2 ≤ 1 ∧
      8 * (1 / 64 : ℝ) ^ 5 ≤ 1 := by
  constructor <;> norm_num <;> nlinarith

end ErdosProblems.Erdos1041.SeventhReturnSexticAssimilation20260826
