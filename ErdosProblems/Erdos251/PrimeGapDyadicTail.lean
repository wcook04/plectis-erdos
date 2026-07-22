import Mathlib.Data.Nat.Prime.Nth
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

open scoped BigOperators

/-!
# Erdős #251: prime-gap dyadic tails

Rationality controls the fractional part of a scaled tail, not the prime-gap
word itself. This module records the exact dyadic coboundary which exposes the
free integer carry and proves its finite telescoping identity. It is the
formal no-go behind attempts to deduce eventual periodicity or automaticity of
prime gaps from a periodic fractional orbit.

The remaining analytic producer is growing-block dyadic anti-concentration for
the actual consecutive prime gaps.
-/

namespace ErdosProblems.Erdos251

/-- Zero-based prime enumeration. -/
noncomputable def prime0 (n : ℕ) : ℕ :=
  Nat.nth Nat.Prime n

/-- Zero-based consecutive prime gap. -/
noncomputable def primeGap0 (n : ℕ) : ℕ :=
  prime0 (n + 1) - prime0 n

@[simp] theorem primeGap0_zero : primeGap0 0 = 1 := by
  simp [primeGap0, prime0, Nat.nth_prime_zero_eq_two,
    Nat.nth_prime_one_eq_three]

@[simp] theorem primeGap0_one : primeGap0 1 = 2 := by
  simp [primeGap0, prime0, Nat.nth_prime_one_eq_three,
    Nat.nth_prime_two_eq_five]

/-- The coefficient emitted by an unrestricted integer carry. -/
def carryCoeff (K : ℕ → ℚ) (n : ℕ) : ℚ :=
  2 * K n - K (n + 1)

/-- The finite dyadic series emitted by `carryCoeff`. -/
def carryPartialSum (K : ℕ → ℚ) (n : ℕ) : ℚ :=
  ∑ i ∈ Finset.range n, carryCoeff K i / 2 ^ (i + 1)

/-- Exact telescoping: arbitrary carries can produce a rational dyadic series
without making the coefficient stream periodic. -/
theorem carryPartialSum_eq (K : ℕ → ℚ) (n : ℕ) :
    carryPartialSum K n = K 0 - K n / 2 ^ n := by
  induction n with
  | zero => simp [carryPartialSum]
  | succ n ih =>
      rw [carryPartialSum, Finset.sum_range_succ]
      change carryPartialSum K n + carryCoeff K n / 2 ^ (n + 1) = _
      rw [ih]
      simp only [carryCoeff, pow_succ]
      ring

/-- Natural-valued carries emit nonnegative coefficients when the next carry
is at most twice the current one. -/
def natCarryCoeff (K : ℕ → ℕ) (n : ℕ) : ℕ :=
  2 * K n - K (n + 1)

theorem natCarryCoeff_cast
    (K : ℕ → ℕ) (n : ℕ) (hK : K (n + 1) ≤ 2 * K n) :
    (natCarryCoeff K n : ℚ) =
      carryCoeff (fun j => (K j : ℚ)) n := by
  simp [natCarryCoeff, carryCoeff, Nat.cast_sub hK]

end ErdosProblems.Erdos251
