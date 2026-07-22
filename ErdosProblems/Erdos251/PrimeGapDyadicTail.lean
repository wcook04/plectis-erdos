import Mathlib.Data.Nat.Prime.Nth
import Mathlib.Data.Nat.PrimeFin
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

/-- Finite zero-based dyadic partial sum of a rational sequence. -/
def dyadicPartialSumQ (P : ℕ → ℚ) (n : ℕ) : ℚ :=
  ∑ i ∈ Finset.range n, P i / 2 ^ (i + 1)

/-- Finite dyadic partial sum of the forward differences of a sequence. -/
def dyadicDifferencePartialSumQ (P : ℕ → ℚ) (n : ℕ) : ℚ :=
  ∑ i ∈ Finset.range n, (P (i + 1) - P i) / 2 ^ (i + 1)

@[simp] theorem dyadicPartialSumQ_succ (P : ℕ → ℚ) (n : ℕ) :
    dyadicPartialSumQ P (n + 1) =
      dyadicPartialSumQ P n + P n / 2 ^ (n + 1) := by
  rw [dyadicPartialSumQ, dyadicPartialSumQ, Finset.sum_range_succ]

@[simp] theorem dyadicDifferencePartialSumQ_succ (P : ℕ → ℚ) (n : ℕ) :
    dyadicDifferencePartialSumQ P (n + 1) =
      dyadicDifferencePartialSumQ P n +
        (P (n + 1) - P n) / 2 ^ (n + 1) := by
  rw [dyadicDifferencePartialSumQ, dyadicDifferencePartialSumQ,
    Finset.sum_range_succ]

/-- Exact finite summation by parts.  The endpoint term is retained, so the
theorem can be used before any analytic convergence argument. -/
theorem dyadicPartialSumQ_eq_start_add_differences
    (P : ℕ → ℚ) (n : ℕ) :
    dyadicPartialSumQ P (n + 1) =
      P 0 + dyadicDifferencePartialSumQ P n - P n / 2 ^ (n + 1) := by
  induction n with
  | zero =>
      simp [dyadicPartialSumQ, dyadicDifferencePartialSumQ]
      ring
  | succ n ih =>
      rw [dyadicPartialSumQ_succ, dyadicDifferencePartialSumQ_succ, ih]
      simp only [pow_succ]
      ring

/-- Consecutive zero-based primes are increasing. -/
theorem prime0_mono_step (n : ℕ) : prime0 n ≤ prime0 (n + 1) := by
  exact (Nat.nth_strictMono Nat.infinite_setOf_prime).monotone (Nat.le_succ n)

/-- Casting the natural prime gap agrees with subtraction in `ℚ`. -/
theorem primeGap0_cast (n : ℕ) :
    (primeGap0 n : ℚ) = (prime0 (n + 1) : ℚ) - prime0 n := by
  rw [primeGap0, Nat.cast_sub (prime0_mono_step n)]

/-- Finite dyadic partial sum of the actual consecutive prime gaps. -/
noncomputable def primeGapPartialSumQ (n : ℕ) : ℚ :=
  ∑ i ∈ Finset.range n, (primeGap0 i : ℚ) / 2 ^ (i + 1)

/-- Exact finite prime-gap reformulation, including the initial gap and the
endpoint correction.  Passing to an infinite series requires a separate proof
that the endpoint tends to zero. -/
theorem prime0_dyadic_summation_by_parts (n : ℕ) :
    dyadicPartialSumQ (fun i => (prime0 i : ℚ)) (n + 1) =
      2 + primeGapPartialSumQ n - (prime0 n : ℚ) / 2 ^ (n + 1) := by
  simpa [dyadicDifferencePartialSumQ, primeGapPartialSumQ, primeGap0_cast,
    prime0] using
    (dyadicPartialSumQ_eq_start_add_differences
      (fun i => (prime0 i : ℚ)) n)

/-! ## Exact tail-shift dynamics -/

/-- Abstract dyadic tail recurrence with integer digits.  The actual infinite
prime-gap tail is a future analytic instance once summability is established. -/
def DyadicTailRecurrence (g : ℕ → ℤ) (T : ℕ → ℚ) : Prop :=
  ∀ N, T (N + 1) = 2 * T N - g (N + 1)

/-- Difference between two tail states separated by `h` steps. -/
def tailShift (T : ℕ → ℚ) (h N : ℕ) : ℚ :=
  T (N + h) - T N

/-- The exact propagation identity for a fixed tail shift. -/
theorem tailShift_succ
    {g : ℕ → ℤ} {T : ℕ → ℚ}
    (hrec : DyadicTailRecurrence g T) (h N : ℕ) :
    tailShift T h (N + 1) =
      2 * tailShift T h N -
        ((g (N + h + 1) : ℚ) - (g (N + 1) : ℚ)) := by
  unfold tailShift
  rw [show N + 1 + h = (N + h) + 1 by omega,
    hrec (N + h), hrec N]
  ring

/-- A rational number is integral when it is the cast of an integer. -/
def RatIntegral (x : ℚ) : Prop :=
  ∃ z : ℤ, x = z

/-- Once a fixed tail shift is integral, the recurrence keeps it integral at
the next index.  This is the exact finite algebra behind the eventual-shift
criterion; no prime-distribution input is used. -/
theorem tailShift_integral_succ
    {g : ℕ → ℤ} {T : ℕ → ℚ}
    (hrec : DyadicTailRecurrence g T) {h N : ℕ}
    (hInt : RatIntegral (tailShift T h N)) :
    RatIntegral (tailShift T h (N + 1)) := by
  rcases hInt with ⟨z, hz⟩
  refine ⟨2 * z - (g (N + h + 1) - g (N + 1)), ?_⟩
  rw [tailShift_succ hrec, hz]
  push_cast
  ring

/-- Integrality therefore propagates through every later index. -/
theorem tailShift_integral_add
    {g : ℕ → ℤ} {T : ℕ → ℚ}
    (hrec : DyadicTailRecurrence g T) {h N : ℕ}
    (hInt : RatIntegral (tailShift T h N)) :
    ∀ k, RatIntegral (tailShift T h (N + k))
  | 0 => by simpa using hInt
  | k + 1 => by
      simpa [Nat.add_assoc] using
        tailShift_integral_succ hrec (tailShift_integral_add hrec hInt k)

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
