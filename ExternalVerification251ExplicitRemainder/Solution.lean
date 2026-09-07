/-
Copyright (c) 2026 Will Cook. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Will Cook
-/
import Mathlib
import ErdosProblems.Erdos251.PaperTailBoundsR7

/-!
# Source transport for the explicit remainder bound in Erdős #251

Every definition below unfolds to the corresponding source definition, so the
compared theorem is a transport of
`ErdosProblems.Erdos251.PaperR7.explicit_remainder_certificate`.
-/

open ErdosProblems.Erdos251
open ErdosProblems.Erdos251.PaperR7

namespace Erdos249257.ExternalVerification251ExplicitRemainder

/-- Zero-based consecutive prime gap. -/
noncomputable def gap (n : ℕ) : ℕ :=
  Nat.nth Nat.Prime (n + 1) - Nat.nth Nat.Prime n

/-- The complete real tail of the gap series after index `N`. -/
noncomputable def tail (N : ℕ) : ℝ :=
  ∑' j : ℕ, (gap (N + j + 1) : ℝ) / 2 ^ (j + 1)

/-- The `h`-shift of the tail. -/
noncomputable def shift (h N : ℕ) : ℝ :=
  tail (N + h) - tail N

/-- A real number is integral when it is the cast of an integer. -/
def IsIntegral (x : ℝ) : Prop :=
  ∃ z : ℤ, x = z

/-- The finite signed window of length `L`. -/
noncomputable def window (h N L : ℕ) : ℝ :=
  ∑ j ∈ Finset.range L,
    ((gap (N + h + j + 1) : ℝ) - gap (N + j + 1)) / 2 ^ (j + 1)

/-- Euclidean distance to the integers. -/
noncomputable def intDist (x : ℝ) : ℝ :=
  Metric.infDist x (Set.range (fun z : ℤ => (z : ℝ)))

/-- The quartic majorant polynomial of the displayed remainder. -/
def quartic (x : ℝ) : ℝ :=
  x ^ 4 + 8 * x ^ 3 + 36 * x ^ 2 + 104 * x + 150

/-- The explicit remainder bound, with the printed constant 1250. -/
noncomputable def explicitRemainder (h N L : ℕ) : ℝ :=
  1250 / 2 ^ L * (quartic ((N : ℝ) + h + L + 2) + quartic ((N : ℝ) + L + 2))

theorem gap_eq (n : ℕ) : gap n = primeGap0 n := rfl

theorem tail_eq (N : ℕ) : tail N = realPrimeGapTail N := by
  rw [realPrimeGapTail_eq_tsum_shifted_gaps]
  rfl

theorem shift_eq (h N : ℕ) : shift h N = realTailShift realPrimeGapTail h N := by
  rw [shift, realTailShift, tail_eq, tail_eq]

theorem window_eq (h N L : ℕ) : window h N L = signedWindow h N L := rfl

theorem quartic_eq (x : ℝ) : quartic x = quarticTailPolynomial x := rfl

theorem explicitRemainder_eq (h N L : ℕ) :
    explicitRemainder h N L = PaperR7.explicitRemainder h N L := rfl

theorem intDist_eq (x : ℝ) : intDist x = integerDistance x := rfl

theorem explicit_remainder_certificate (h N L : ℕ) :
    |shift h N - window h N L| ≤ explicitRemainder h N L ∧
    (|window h N L| + explicitRemainder h N L < 1 → |shift h N| < 1) ∧
    (explicitRemainder h N L < intDist (window h N L) → ¬ IsIntegral (shift h N)) := by
  rw [shift_eq]
  exact PaperR7.explicit_remainder_certificate h N L

end Erdos249257.ExternalVerification251ExplicitRemainder
