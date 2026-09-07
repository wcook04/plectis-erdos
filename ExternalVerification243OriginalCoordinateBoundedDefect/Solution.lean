/-
Copyright (c) 2026 Will Cook. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Will Cook
-/
import Mathlib
import ErdosProblems.Erdos243.PaperCompleteR7.ProductDefect

/-!
# Source transport for the original-coordinate bounded product defect in Erdős #243

The local `prefixProduct` and `productDefect` repeat the corpus definitions
verbatim, so each agrees with its corpus counterpart by `rfl` and the challenge
statement transports directly.
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

theorem prefixProduct_eq (a : ℕ → ℕ) (n : ℕ) :
    prefixProduct a n = ErdosProblems.Erdos243.PaperCompleteR7.prefixProduct a n :=
  rfl

theorem productDefect_eq (a : ℕ → ℕ) (n : ℕ) :
    productDefect a n = ErdosProblems.Erdos243.PaperCompleteR7.productDefect a n :=
  rfl

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
  refine ErdosProblems.Erdos243.PaperCompleteR7.original_coordinate_bounded_defect
    a ha hpos p q hq hs hgrowth ?_
  simpa only [productDefect_eq] using hupper

end Erdos249257.ExternalVerification243OriginalCoordinateBoundedDefect
