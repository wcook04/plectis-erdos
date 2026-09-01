/-
Copyright (c) 2026 Will Cook. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Will Cook
-/
import Mathlib

/-!
# Trusted challenge for the all-base reciprocal-summable support theorem

This module restates one source-independent proposition.  The support is an
arbitrary infinite subset of the positive exponents (the zero term is
harmlessly normalised by real division), and its reciprocal mass is assumed
summable. Under exactly those hypotheses, its reciprocal-power support series
is irrational at every integer base at least two.

The challenge deliberately exposes only the final irrationality theorem.  It
does not expose the shifted-atom close-return or binary-to-radix displacement
lemmas as separate results, cover reciprocal-divergent supports, or solve
universal Erdős #257.
-/

namespace Erdos249257.ExternalVerification257ReciprocalSupport

noncomputable section

/-- The reciprocal support summand, with exponent zero normalised to zero. -/
noncomputable def supportReciprocalTerm (A : Set ℕ) (a : ℕ) : ℝ :=
  Set.indicator A (fun a : ℕ => (1 : ℝ) / (a : ℝ)) a

/-- The reciprocal-power subseries at base b supported on A. -/
noncomputable def supportPowerSeries (b : ℕ) (A : Set ℕ) : ℝ :=
  ∑' a : ℕ, Set.indicator A
    (fun a : ℕ => (1 : ℝ) / ((b : ℝ) ^ a - 1)) a

/-- Every infinite reciprocal-summable support gives an irrational
reciprocal-power subseries at every integer base at least two. -/
theorem irrational_supportPowerSeries_of_summable_reciprocal
    (b : ℕ) (A : Set ℕ) (hb : 2 ≤ b) (hA : A.Infinite)
    (hsum : Summable (supportReciprocalTerm A)) :
    Irrational (supportPowerSeries b A) := by
  sorry

end

end Erdos249257.ExternalVerification257ReciprocalSupport
