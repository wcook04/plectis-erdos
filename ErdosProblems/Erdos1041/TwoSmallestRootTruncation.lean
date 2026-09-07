import Mathlib

/-!
# Erdős #1041: the two-smallest-root truncation kernel

The analytic companion chooses roots of moduli `r ≤ q`, joins the first root
to radius `r` on the second root ray, and then follows that ray to the second
root.  The two selected root factors are at most `(r+q)²/4` on both pieces.
Every other factor is bounded by `1 + q`.

This module checks the load-bearing scalar inequalities, their multiplicative
fan-in, and the strict constant-two length conclusion.  It does not postulate
the complex path theorem as an axiom.
-/

namespace ErdosProblems.Erdos1041

/-- On the common-radius chord, put `x = r t`.  The triangle inequality gives
the two selected factors the majorant `2x(q+r-2x)`, and this is at most
`(q+r)²/4`.  Four times the defect is the square `(q+r-4x)²`. -/
theorem twoSmallest_chord_twoFactor_bound
    {r q x : ℝ} :
    2 * x * (q + r - 2 * x) ≤ (q + r) ^ 2 / 4 := by
  nlinarith [sq_nonneg (q + r - 4 * x)]

/-- The version consumed after bounding the angular separation by two. -/
theorem twoSmallest_chord_selected_factor
    {r q x d selected : ℝ}
    (hx : 0 ≤ x) (hxr : x ≤ r) (hrq : r ≤ q)
    (hd2 : d ≤ 2)
    (hselected : selected ≤ x * d * (q + r - 2 * x)) :
    selected ≤ (q + r) ^ 2 / 4 := by
  have hgap : 0 ≤ q + r - 2 * x := by linarith
  have hxd : x * d ≤ x * 2 :=
    mul_le_mul_of_nonneg_left hd2 hx
  have hmajor : x * d * (q + r - 2 * x) ≤
      2 * x * (q + r - 2 * x) := by
    nlinarith [mul_le_mul_of_nonneg_right hxd hgap]
  exact hselected.trans (hmajor.trans twoSmallest_chord_twoFactor_bound)

/-- On the outer radial arm the two selected factors are bounded by
`(q-x)(x+r) ≤ (q+r)²/4`.  Four times the defect is
`(q-r-2x)²`. -/
theorem twoSmallest_arm_twoFactor_bound
    {r q x : ℝ} :
    (q - x) * (x + r) ≤ (q + r) ^ 2 / 4 := by
  nlinarith [sq_nonneg (q - r - 2 * x)]

/-- Strong multiplicative fan-in with an arbitrary supplied bound for the
remaining root factors.  This is the form used by the individual-radius
criterion in the analytic companion. -/
theorem twoSmallest_factor_budget_of_tail
    {r q selected tail B : ℝ}
    (hr0 : 0 ≤ r)
    (hq : 0 < q)
    (hselected : selected ≤ (r + q) ^ 2 / 4)
    (htail0 : 0 ≤ tail)
    (htail : tail ≤ B)
    (hbudget : ((r + q) ^ 2 / 4) * B < 1) :
    selected * tail < 1 := by
  have hscale0 : 0 ≤ (r + q) ^ 2 / 4 := by positivity
  have hfirst : selected * tail ≤ ((r + q) ^ 2 / 4) * tail :=
    mul_le_mul_of_nonneg_right hselected htail0
  have hsecond : ((r + q) ^ 2 / 4) * tail ≤
      ((r + q) ^ 2 / 4) * B :=
    mul_le_mul_of_nonneg_left htail hscale0
  exact lt_of_le_of_lt (hfirst.trans hsecond) hbudget

/-- Uniform multiplicative fan-in when each remaining root is strictly inside
the unit disk, so its factor is strictly below `1+q`. -/
theorem twoSmallest_factor_budget
    {n : ℕ} {r q selected tail : ℝ}
    (hr0 : 0 ≤ r)
    (hq : 0 < q)
    (hselected : selected ≤ (r + q) ^ 2 / 4)
    (htail0 : 0 ≤ tail)
    (htail : tail < (1 + q) ^ (n - 2))
    (hbudget : ((r + q) ^ 2 / 4) * (1 + q) ^ (n - 2) ≤ 1) :
    selected * tail < 1 := by
  have hrqpos : 0 < r + q := by linarith
  have hscale : 0 < (r + q) ^ 2 / 4 := by positivity
  have hfirst : selected * tail ≤ ((r + q) ^ 2 / 4) * tail :=
    mul_le_mul_of_nonneg_right hselected htail0
  have hstrict : ((r + q) ^ 2 / 4) * tail <
      ((r + q) ^ 2 / 4) * (1 + q) ^ (n - 2) :=
    mul_lt_mul_of_pos_left htail hscale
  exact lt_of_lt_of_le (lt_of_le_of_lt hfirst hstrict) hbudget

/-- The broken path has length at most `r*d + (q-r)`, where the angular chord
has `d ≤ 2`.  Since both selected roots are strictly inside the unit disk, the
length is strictly below two. -/
theorem twoSmallest_path_length_lt_two
    {r q d length : ℝ}
    (hr0 : 0 ≤ r) (hrq : r ≤ q) (hq1 : q < 1)
    (hd : d ≤ 2)
    (hlength : length ≤ r * d + (q - r)) :
    length < 2 := by
  have hrd : r * d ≤ r * 2 :=
    mul_le_mul_of_nonneg_left hd hr0
  linarith

/-- The degree-five threshold is the scalar inequality
`q²(1+q)³ ≤ 1`. -/
theorem quintic_twoSmallest_factor_budget
    {r q selected tail : ℝ}
    (hr0 : 0 ≤ r)
    (hq : 0 < q)
    (hselected : selected ≤ (r + q) ^ 2 / 4)
    (htail0 : 0 ≤ tail)
    (htail : tail < (1 + q) ^ 3)
    (hbudget : ((r + q) ^ 2 / 4) * (1 + q) ^ 3 ≤ 1) :
    selected * tail < 1 := by
  simpa using twoSmallest_factor_budget (n := 5) hr0 hq hselected
    htail0 htail hbudget

end ErdosProblems.Erdos1041
