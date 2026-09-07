/-
Copyright (c) 2026 Will Cook. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Will Cook
-/
import Mathlib

/-!
# Trusted challenge for the explicit remainder bound in Erdős #251

Write `g n` for the `n`-th consecutive prime gap, zero-based, and `T N` for the
complete real tail `∑' j, g (N + j + 1) / 2 ^ (j + 1)` of the prime-gap dyadic
series. The finite signed window of length `L` at shift `h` and index `N`
approximates the shift `T (N + h) - T N`.

The theorem bounds the approximation error by the explicit quantity

`1250 / 2 ^ L * (P (N + h + L + 2) + P (N + L + 2))`, `P x = x ^ 4 + 8 x ^ 3 + 36 x ^ 2 + 104 x + 150`,

with no unevaluated constant, and records the two certificate consequences: a
small window with a small bound keeps the shift inside the open unit interval,
and a window farther from the integers than the bound makes the shift
non-integral.

The bound is unconditional. It supplies no block satisfying either
certificate, and it does not settle Erdős Problem #251.
-/

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

/-- The explicit remainder bound and both finite certificates. -/
theorem explicit_remainder_certificate (h N L : ℕ) :
    |shift h N - window h N L| ≤ explicitRemainder h N L ∧
    (|window h N L| + explicitRemainder h N L < 1 → |shift h N| < 1) ∧
    (explicitRemainder h N L < intDist (window h N L) → ¬ IsIntegral (shift h N)) := by
  sorry

end Erdos249257.ExternalVerification251ExplicitRemainder
