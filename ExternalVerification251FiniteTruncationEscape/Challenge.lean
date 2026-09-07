/-
Copyright (c) 2026 Will Cook. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Will Cook
-/
import Mathlib

/-!
# Trusted challenge for the finite-truncation escape criterion in Erdős #251

Write `g n` for the `n`-th consecutive prime gap, zero-based, and

`T N = ∑' j, g (N + j + 1) / 2 ^ (j + 1)`

for the complete real tail of the prime-gap dyadic series after index `N`.
The `h`-shift of that tail is `T (N + h) - T N`.

Fix a majorant `M` of the gaps. The finite window

`S = ∑ j < L, (g (N + h + j + 1) - g (N + j + 1)) / 2 ^ (j + 1)`

is computable from finitely many primes, and the omitted part of the shift is
controlled by the tail mass `R = ∑' j, (M (N + h + L + j + 1) + M (N + L + j + 1)) / 2 ^ (L + j + 1)`.

The theorem states that a cofinal supply of finite blocks whose window is
farther than `R` from every integer forces the shift to be non-integral
cofinally, for every fixed positive `h`, and hence forces the prime dyadic
series `∑' n, p n / 2 ^ (n + 1)` to be irrational.

The supply hypothesis is not proved here for the actual prime gaps. This is a
conditional criterion and it does not settle Erdős Problem #251.
-/

namespace Erdos249257.ExternalVerification251FiniteTruncationEscape

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

/-- One term of the omitted tail mass under the majorant `M`. -/
noncomputable def remainderTerm (M : ℕ → ℝ) (h N L j : ℕ) : ℝ :=
  (M (N + h + L + j + 1) + M (N + L + j + 1)) / 2 ^ (L + j + 1)

/-- The omitted tail mass under the majorant `M`. -/
noncomputable def remainder (M : ℕ → ℝ) (h N L : ℕ) : ℝ :=
  ∑' j : ℕ, remainderTerm M h N L j

/-- Euclidean distance to the integers. -/
noncomputable def intDist (x : ℝ) : ℝ :=
  Metric.infDist x (Set.range (fun z : ℤ => (z : ℝ)))

/-- A cofinal supply of separated finite blocks forces cofinal
non-integrality of every fixed positive shift of the actual prime-gap tail. -/
theorem cofinal_escape_of_finite_truncation (M : ℕ → ℝ)
    (hM : ∀ n, (gap n : ℝ) ≤ M n)
    (hsupply : ∀ h : ℕ, 0 < h → ∀ N₀ : ℕ, ∃ N L : ℕ,
      N₀ ≤ N ∧ 1 ≤ L ∧ Summable (remainderTerm M h N L) ∧
      remainder M h N L < intDist (window h N L)) :
    ∀ h : ℕ, 0 < h → ∀ N₀ : ℕ, ∃ N : ℕ, N₀ ≤ N ∧ ¬ IsIntegral (shift h N) := by
  sorry

/-- The same supply forces irrationality of the prime dyadic series. -/
theorem irrational_prime_series_of_finite_truncation (M : ℕ → ℝ)
    (hM : ∀ n, (gap n : ℝ) ≤ M n)
    (hsupply : ∀ h : ℕ, 0 < h → ∀ N₀ : ℕ, ∃ N L : ℕ,
      N₀ ≤ N ∧ 1 ≤ L ∧ Summable (remainderTerm M h N L) ∧
      remainder M h N L < intDist (window h N L)) :
    Irrational (∑' n : ℕ, (Nat.nth Nat.Prime n : ℝ) / 2 ^ (n + 1)) := by
  sorry

end Erdos249257.ExternalVerification251FiniteTruncationEscape
