import Mathlib

/-!
# Erdős #1041: centroid-hub algebra

For five planar roots, this module checks the two algebraic identities behind
the canonical centroid hub.  The variance identity puts the centroid inside
the unit lemniscate after the standard AM--GM step.  The pair-budget theorem
shows that variance below five forces two centroid distances to sum below two.
No spoke-containment hypothesis is introduced here.
-/

namespace ErdosProblems.Erdos1041

/-- The exact five-point planar variance identity, written in real coordinates
so that no complex-norm normalization is hidden. -/
theorem fivePoint_centroid_variance_identity
    (x0 y0 x1 y1 x2 y2 x3 y3 x4 y4 : ℝ) :
    let hx := (x0 + x1 + x2 + x3 + x4) / 5
    let hy := (y0 + y1 + y2 + y3 + y4) / 5
    ((x0 - hx) ^ 2 + (y0 - hy) ^ 2) +
        ((x1 - hx) ^ 2 + (y1 - hy) ^ 2) +
        ((x2 - hx) ^ 2 + (y2 - hy) ^ 2) +
        ((x3 - hx) ^ 2 + (y3 - hy) ^ 2) +
        ((x4 - hx) ^ 2 + (y4 - hy) ^ 2) =
      (x0 ^ 2 + y0 ^ 2) + (x1 ^ 2 + y1 ^ 2) +
        (x2 ^ 2 + y2 ^ 2) + (x3 ^ 2 + y3 ^ 2) +
        (x4 ^ 2 + y4 ^ 2) - 5 * (hx ^ 2 + hy ^ 2) := by
  dsimp
  ring

/-- Five open-unit-disk points have centroid variance strictly below five. -/
theorem fivePoint_centroid_variance_lt_five
    {x0 y0 x1 y1 x2 y2 x3 y3 x4 y4 : ℝ}
    (h0 : x0 ^ 2 + y0 ^ 2 < 1)
    (h1 : x1 ^ 2 + y1 ^ 2 < 1)
    (h2 : x2 ^ 2 + y2 ^ 2 < 1)
    (h3 : x3 ^ 2 + y3 ^ 2 < 1)
    (h4 : x4 ^ 2 + y4 ^ 2 < 1) :
    let hx := (x0 + x1 + x2 + x3 + x4) / 5
    let hy := (y0 + y1 + y2 + y3 + y4) / 5
    ((x0 - hx) ^ 2 + (y0 - hy) ^ 2) +
        ((x1 - hx) ^ 2 + (y1 - hy) ^ 2) +
        ((x2 - hx) ^ 2 + (y2 - hy) ^ 2) +
        ((x3 - hx) ^ 2 + (y3 - hy) ^ 2) +
        ((x4 - hx) ^ 2 + (y4 - hy) ^ 2) < 5 := by
  have hvariance := fivePoint_centroid_variance_identity
    x0 y0 x1 y1 x2 y2 x3 y3 x4 y4
  dsimp at hvariance ⊢
  rw [hvariance]
  have hcentroid :
      0 ≤ 5 *
        (((x0 + x1 + x2 + x3 + x4) / 5) ^ 2 +
          ((y0 + y1 + y2 + y3 + y4) / 5) ^ 2) := by positivity
  linarith

/-- If five nonnegative centroid distances have square-sum below five, some
two have total distance below two.  This is the quintic scalar heart of the
centroid ellipse budget. -/
theorem fiveDistances_exists_pair_sum_lt_two
    {d0 d1 d2 d3 d4 : ℝ}
    (hd0 : 0 ≤ d0) (hd1 : 0 ≤ d1) (hd2 : 0 ≤ d2)
    (hd3 : 0 ≤ d3) (hd4 : 0 ≤ d4)
    (hsum : d0 ^ 2 + d1 ^ 2 + d2 ^ 2 + d3 ^ 2 + d4 ^ 2 < 5) :
    d0 + d1 < 2 ∨ d0 + d2 < 2 ∨ d0 + d3 < 2 ∨ d0 + d4 < 2 ∨
      d1 + d2 < 2 ∨ d1 + d3 < 2 ∨ d1 + d4 < 2 ∨
      d2 + d3 < 2 ∨ d2 + d4 < 2 ∨ d3 + d4 < 2 := by
  by_contra h
  push Not at h
  rcases h with ⟨h01, h02, h03, h04, h12, h13, h14, h23, h24, h34⟩
  have htotal : 5 ≤ d0 + d1 + d2 + d3 + d4 := by linarith
  have htotalSq :
      25 ≤ (d0 + d1 + d2 + d3 + d4) ^ 2 := by nlinarith
  have hdiffs :
      0 ≤ (d0 - d1) ^ 2 + (d0 - d2) ^ 2 + (d0 - d3) ^ 2 +
        (d0 - d4) ^ 2 + (d1 - d2) ^ 2 + (d1 - d3) ^ 2 +
        (d1 - d4) ^ 2 + (d2 - d3) ^ 2 + (d2 - d4) ^ 2 +
        (d3 - d4) ^ 2 := by positivity
  have hvariance :
      5 * (d0 ^ 2 + d1 ^ 2 + d2 ^ 2 + d3 ^ 2 + d4 ^ 2) -
          (d0 + d1 + d2 + d3 + d4) ^ 2 =
        (d0 - d1) ^ 2 + (d0 - d2) ^ 2 + (d0 - d3) ^ 2 +
          (d0 - d4) ^ 2 + (d1 - d2) ^ 2 + (d1 - d3) ^ 2 +
          (d1 - d4) ^ 2 + (d2 - d3) ^ 2 + (d2 - d4) ^ 2 +
          (d3 - d4) ^ 2 := by ring
  have hcauchy :
      (d0 + d1 + d2 + d3 + d4) ^ 2 ≤
        5 * (d0 ^ 2 + d1 ^ 2 + d2 ^ 2 + d3 ^ 2 + d4 ^ 2) := by
    linarith
  nlinarith

end ErdosProblems.Erdos1041
