/-
Copyright (c) 2026 Will Cook. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Will Cook
-/
import Mathlib

/-!
# Trusted challenge for the Erdős #1049 rational-base clearing barrier

This Mathlib-only interface isolates the exact cleared-tail recurrence, the
exponential denominator-base forcing term, and the resulting failure of one
literal coordinatewise clearing scheme at base `3 / 2`.

The package does not derive the cleared state from a rational Lambert value,
exclude other linear-form constructions, or prove irrationality at `3 / 2`.
-/

namespace Erdos249257.ExternalVerification1049RationalBaseBarrier

open scoped BigOperators

/-- The finite arithmetic core of a coordinatewise rational-base corridor. -/
def CoordinatewiseCorridor
    (a b N K Q digit : ℕ) : Prop :=
  0 < a ∧ 0 < Q ∧ 0 < digit ∧ digit ≤ N + K ∧
    a ^ K ∣ Q * digit ∧
    Q * b ^ (N + K + 1) < a ^ (K + 1)

/-- The first `N` rational-base divisor-series coordinates. -/
def rationalBasePrefixQ
    (r s : ℚ) (coeff : ℕ → ℚ) (N : ℕ) : ℚ :=
  ∑ m ∈ Finset.range N,
    coeff (m + 1) * s ^ (m + 1) / r ^ (m + 1)

/-- The denominator-cleared tail state attached to a putative value `F`. -/
def rationalBaseClearedTailQ
    (r s B F : ℚ) (coeff : ℕ → ℚ) (N : ℕ) : ℚ :=
  B * r ^ N * (F - rationalBasePrefixQ r s coeff N)

/-- Natural-valued magnitude of the recurrence forcing term. -/
def rationalBaseForcingNat
    (s B : ℕ) (coeff : ℕ → ℕ) (N : ℕ) : ℕ :=
  B * coeff (N + 1) * s ^ (N + 1)

/-- Exact rational-base cleared-tail recurrence. -/
theorem rationalBaseClearedTailQ_succ
    {r s B F : ℚ} {coeff : ℕ → ℚ} (hr : r ≠ 0) (N : ℕ) :
    rationalBaseClearedTailQ r s B F coeff (N + 1) =
      r * rationalBaseClearedTailQ r s B F coeff N -
        B * coeff (N + 1) * s ^ (N + 1) := by
  sorry

/-- Every genuine denominator base forces at least exponential growth. -/
theorem twoPow_le_rationalBaseForcingNat
    {s B : ℕ} {coeff : ℕ → ℕ} {N : ℕ}
    (hs : 2 ≤ s) (hB : 1 ≤ B) (hc : 1 ≤ coeff (N + 1)) :
    2 ^ (N + 1) ≤ rationalBaseForcingNat s B coeff N := by
  sorry

/-- The literal coordinatewise corridor is impossible at base `3 / 2`. -/
theorem threeHalves_no_coordinatewiseCorridor
    {N K Q digit : ℕ} (hN : 1 ≤ N) (hK : 1 ≤ K) :
    ¬ CoordinatewiseCorridor 3 2 N K Q digit := by
  sorry

end Erdos249257.ExternalVerification1049RationalBaseBarrier
