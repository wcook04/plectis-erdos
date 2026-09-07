/-
Copyright (c) 2026 Will Cook. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Will Cook
-/
import Mathlib

/-!
# Trusted challenge for the Erdős #1049 weight indicator

The weight attached to the Zudilin cone at parameters `(12, 13, 14, 15)` is

`ω(x) = max 0 (max (⌊14x⌋ + ⌊13x⌋ - ⌊12x⌋ - ⌊15x⌋) (2⌊14x⌋ - ⌊13x⌋ - ⌊15x⌋))`.

The theorem states that on `[0, 1)` this integer weight takes only the values
`0` and `1`, and that it equals `1` exactly on an explicit union of thirteen
left-closed right-open intervals.  The statement quantifies over every real
point of `[0, 1)`; it is not a check at sampled points.

This is one lemma of the rational-base construction.  It supplies no
irrationality conclusion and it does not settle Erdős Problem 1049.
-/

namespace Erdos249257.ExternalVerification1049OmegaIndicator

/-- The Zudilin cone weight at the parameters `12, 13, 14, 15`. -/
noncomputable def omegaWeight (x : ℝ) : ℤ :=
  max 0 (max (⌊14 * x⌋ + ⌊13 * x⌋ - ⌊12 * x⌋ - ⌊15 * x⌋)
    (2 * ⌊14 * x⌋ - ⌊13 * x⌋ - ⌊15 * x⌋))

/-- The thirteen half-open intervals on which the weight is one. -/
def InOmegaSupport (x : ℝ) : Prop :=
  ((1 : ℝ) / 14 ≤ x ∧ x < (1 : ℝ) / 12) ∨
  ((1 : ℝ) / 7 ≤ x ∧ x < (1 : ℝ) / 6) ∨
  ((3 : ℝ) / 14 ≤ x ∧ x < (1 : ℝ) / 4) ∨
  ((2 : ℝ) / 7 ≤ x ∧ x < (1 : ℝ) / 3) ∨
  ((5 : ℝ) / 14 ≤ x ∧ x < (2 : ℝ) / 5) ∨
  ((3 : ℝ) / 7 ≤ x ∧ x < (7 : ℝ) / 15) ∨
  ((1 : ℝ) / 2 ≤ x ∧ x < (8 : ℝ) / 15) ∨
  ((4 : ℝ) / 7 ≤ x ∧ x < (3 : ℝ) / 5) ∨
  ((9 : ℝ) / 14 ≤ x ∧ x < (2 : ℝ) / 3) ∨
  ((5 : ℝ) / 7 ≤ x ∧ x < (11 : ℝ) / 15) ∨
  ((11 : ℝ) / 14 ≤ x ∧ x < (4 : ℝ) / 5) ∨
  ((6 : ℝ) / 7 ≤ x ∧ x < (13 : ℝ) / 15) ∨
  ((13 : ℝ) / 14 ≤ x ∧ x < (14 : ℝ) / 15)

/-- The weight is a `{0, 1}` indicator, and its support is exactly the
displayed thirteen-interval set, at every real point of `[0, 1)`. -/
theorem omegaWeight_indicator (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x < 1) :
    (omegaWeight x = 0 ∨ omegaWeight x = 1) ∧
      (omegaWeight x = 1 ↔ InOmegaSupport x) := by
  sorry

end Erdos249257.ExternalVerification1049OmegaIndicator
