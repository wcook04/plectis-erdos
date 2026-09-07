/-
Copyright (c) 2026 Will Cook. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Will Cook
-/
import Mathlib

/-!
# Trusted challenge for the original-coordinate bounded product defect in Erdős #243

One source-independent proposition, stated in the original coordinates of the
problem.  Let `a` be a strictly increasing sequence of positive integers whose
reciprocal series converges to a rational value `p / q`, and whose growth
satisfies `a (n+1) / a n ^ 2 → 1`.  Write `P n = ∏_{j < n} a j` and

  `productDefect a n = P n / a n * (a n ^ 2 / a (n+1) - 1)`.

If `productDefect a n` is bounded above from some index onward, then `a`
satisfies the Sylvester recurrence `a (n+1) = a n ^ 2 - a n + 1` eventually.

The rational value of the series is carried by an explicit integer numerator `p`
and positive natural denominator `q`, and the finite upper limit is carried by
an eventual upper bound, which is its equivalent division-free form.

Boundary.  The hypothesis is a bounded product defect.  Erdős #243 asks for the
same conclusion with no such bound, and that remains open: nothing here supplies
the missing bound for an arbitrary sequence, and no part of this file settles
the parent problem.
-/

namespace Erdos249257.ExternalVerification243OriginalCoordinateBoundedDefect

open Filter

/-- The prefix product `∏_{j < n} a j`. -/
def prefixProduct (a : ℕ → ℕ) (n : ℕ) : ℕ :=
  ∏ j ∈ Finset.range n, a j

/-- The original-coordinate product defect `P n / a n * (a n ^ 2 / a (n+1) - 1)`. -/
noncomputable def productDefect (a : ℕ → ℕ) (n : ℕ) : ℝ :=
  (prefixProduct a n : ℝ) / (a n : ℝ) *
    ((a n : ℝ) ^ 2 / (a (n + 1) : ℝ) - 1)

/-- **Original-coordinate bounded defect.**  A rational reciprocal sum, quadratic
growth, and an eventually bounded product defect force the Sylvester recurrence
from some index onward. -/
theorem original_coordinate_bounded_defect
    (a : ℕ → ℕ) (ha : StrictMono a) (hpos : ∀ n, 0 < a n)
    (p : ℤ) (q : ℕ) (hq : 0 < q)
    (hs : HasSum (fun n ↦ 1 / (a n : ℝ)) ((p : ℝ) / (q : ℝ)))
    (hgrowth : Tendsto (fun n ↦ (a (n + 1) : ℝ) / (a n : ℝ) ^ 2)
      atTop (nhds 1))
    (hupper : ∃ M : ℝ, ∃ N, ∀ n, N ≤ n → productDefect a n ≤ M) :
    ∃ N, ∀ n, N ≤ n →
      (a (n + 1) : ℤ) = (a n : ℤ) ^ 2 - (a n : ℤ) + 1 := by
  sorry

end Erdos249257.ExternalVerification243OriginalCoordinateBoundedDefect
