/-
Copyright (c) 2026 Will Cook. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Will Cook
-/
import Mathlib

/-!
# Trusted challenge for the Erdős #1049 rational-base contour

This Mathlib-only interface redeclares the trigamma series `ψ₁`, the thirteen
interval contributions summing to `J`, the constants `C₁ = 1091/2` and
`C₀ = 266 - (3/π²)(225 - J)` of Zudilin's `(14,12,14;27)` forms, the
rational-base threshold `θ* = C₀ / C₁`, and the parameter region cut out by
`log b / log a < θ*`.

Six statements are recorded: the two-sided bound `81/200 < θ* < 1/2`, the
exclusion of `3 / 2` from the region, the membership of every positive power of
`31 / 4`, and the two intermediate constants `J ≥ 77.6` and `C₀ > 88371/400`.

Membership in this region is a statement about parameters.  It is the
hypothesis consumed by the ordinary proof note attached to these forms.  No
theorem here formalises an analytic step of that note and none asserts anything
about the arithmetic nature of `F(a/b) = ∑_{m≥1} 1/((a/b)^m - 1)`, so the
package does not solve Erdős Problem 1049.
-/

namespace Erdos249257.ExternalVerification1049RationalBaseContour

/-- The trigamma series `ψ₁(x) = ∑_{k≥0} 1/(k+x)²`. -/
noncomputable def trigammaSeries (x : ℝ) : ℝ := ∑' k : ℕ, 1 / ((k : ℝ) + x) ^ 2

/-- One interval's contribution `ψ₁(u) - ψ₁(v)`. -/
noncomputable def zudilinJTerm (u v : ℝ) : ℝ := trigammaSeries u - trigammaSeries v

/-- `J = ∑_{i=1}^{13} (ψ₁(uᵢ) - ψ₁(vᵢ))` over the thirteen printed intervals
`[uᵢ, vᵢ)` on which Zudilin's step function `ω` equals `1`. -/
noncomputable def zudilinJ : ℝ :=
  zudilinJTerm (1 / 14) (1 / 12) + zudilinJTerm (1 / 7) (1 / 6) +
    zudilinJTerm (3 / 14) (1 / 4) + zudilinJTerm (2 / 7) (1 / 3) +
    zudilinJTerm (5 / 14) (2 / 5) + zudilinJTerm (3 / 7) (7 / 15) +
    zudilinJTerm (1 / 2) (8 / 15) + zudilinJTerm (4 / 7) (3 / 5) +
    zudilinJTerm (9 / 14) (2 / 3) + zudilinJTerm (5 / 7) (11 / 15) +
    zudilinJTerm (11 / 14) (4 / 5) + zudilinJTerm (6 / 7) (13 / 15) +
    zudilinJTerm (13 / 14) (14 / 15)

/-- `C₁ = (α₀+α₁+α₂)β - (α₁²+α₂²+β²)/2 = 1091/2`. -/
noncomputable def zudilinC1 : ℝ := 1091 / 2

/-- `C₀ = α₁²/2 + α₀α₁ + (β-α₂)(α₂-α₁) - (3/π²)(m² - J)` with `m = 15`. -/
noncomputable def zudilinC0 : ℝ := 266 - 3 / Real.pi ^ 2 * (225 - zudilinJ)

/-- The rational-base threshold `θ* = C₀ / C₁`. -/
noncomputable def zudilinContour : ℝ := zudilinC0 / zudilinC1

/-- The parameter region of reduced bases `a / b` with `log b / log a < θ*`. -/
def ZudilinContourRegion (a b : ℕ) : Prop :=
  Real.log b / Real.log a < zudilinContour

/-- The rational cutoff `81/200` is strictly below the threshold. -/
theorem eightyOne_twoHundredths_lt_zudilinContour :
    (81 : ℝ) / 200 < zudilinContour := by
  sorry

/-- The threshold is strictly below `1/2`. -/
theorem zudilinContour_lt_half : zudilinContour < 1 / 2 := by
  sorry

/-- `3 / 2` lies outside the contour region.  This is a boundary of this family
of forms.  It asserts nothing about the arithmetic nature of `F(3/2)`. -/
theorem threeHalves_outside_zudilinContourRegion :
    ¬ ZudilinContourRegion 3 2 := by
  sorry

/-- Every positive power of `31 / 4` lies in the contour region. -/
theorem thirtyoneFour_power_mem_zudilinContourRegion (r : ℕ) (hr : 0 < r) :
    ZudilinContourRegion (31 ^ r) (4 ^ r) := by
  sorry

/-- The thirteen `k = 0` trigamma terms already give `J ≥ 77.6`. -/
theorem zudilinJ_ge : (776 : ℝ) / 10 ≤ zudilinJ := by
  sorry

/-- `C₀ > 88371/400 = (81/200) · C₁`. -/
theorem zudilinC0_gt : (88371 : ℝ) / 400 < zudilinC0 := by
  sorry

end Erdos249257.ExternalVerification1049RationalBaseContour
