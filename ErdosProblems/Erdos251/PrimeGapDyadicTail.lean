import Mathlib.Data.Nat.Prime.Nth
import Mathlib.Data.Nat.PrimeFin
import Mathlib.Data.Nat.Factorization.Basic
import Mathlib.Data.Rat.Lemmas
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.NumberTheory.PowModTotient
import Mathlib.NumberTheory.Real.Irrational
import Mathlib.Topology.Algebra.InfiniteSum.NatInt
import Mathlib.Tactic.FieldSimp
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

/-- The finite zero-based normalization with denominator `2^i`, matching the
displayed indexing used by the formal conjecture. -/
noncomputable def prime0DisplayedPartialSumQ (n : ℕ) : ℚ :=
  ∑ i ∈ Finset.range n, (prime0 i : ℚ) / 2 ^ i

/-- Exact factor-of-two indexing normalization: the zero-based displayed
partial sum is twice the convention with denominator `2^(i+1)`. -/
theorem prime0DisplayedPartialSumQ_eq_two_mul (n : ℕ) :
    prime0DisplayedPartialSumQ n =
      2 * dyadicPartialSumQ (fun i => (prime0 i : ℚ)) n := by
  rw [prime0DisplayedPartialSumQ, dyadicPartialSumQ, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _hi
  simp only [pow_succ]
  field_simp

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

/-! ## Infinite prime-gap reformulation -/

/-- The real term in the normalized zero-based prime series. -/
noncomputable def primeDyadicTerm (n : ℕ) : ℝ :=
  (prime0 n : ℝ) / 2 ^ (n + 1)

/-- The term with denominator `2^n` used by the displayed formal
conjecture. -/
noncomputable def primeDisplayedDyadicTerm (n : ℕ) : ℝ :=
  (prime0 n : ℝ) / 2 ^ n

/-- The real term in the corresponding consecutive-prime-gap series. -/
noncomputable def primeGapDyadicTerm (n : ℕ) : ℝ :=
  (primeGap0 n : ℝ) / 2 ^ (n + 1)

/-- Infinite-series version of the exact factor-two normalization. -/
theorem primeDisplayedDyadicTerm_eq_two_mul (n : ℕ) :
    primeDisplayedDyadicTerm n = 2 * primeDyadicTerm n := by
  rw [primeDisplayedDyadicTerm, primeDyadicTerm, pow_succ]
  field_simp

/-- Each gap term is the dyadic discrete derivative of the prime term. -/
theorem primeGapDyadicTerm_eq (n : ℕ) :
    primeGapDyadicTerm n =
      2 * primeDyadicTerm (n + 1) - primeDyadicTerm n := by
  rw [primeGapDyadicTerm, primeDyadicTerm, primeDyadicTerm, primeGap0,
    Nat.cast_sub (prime0_mono_step n)]
  simp only [pow_succ]
  field_simp

/-- Summability of the normalized prime series automatically supplies
summability of the actual prime-gap series.  This closes the analytic
interface left implicit by the finite summation-by-parts identity. -/
theorem summable_primeGapDyadicTerm_of_summable_primeDyadicTerm
    (hprime : Summable primeDyadicTerm) :
    Summable primeGapDyadicTerm := by
  have hshift : Summable (fun n => primeDyadicTerm (n + 1)) := by
    simpa [Nat.add_comm] using
      hprime.comp_injective (add_left_injective 1)
  exact ((hshift.mul_left 2).sub hprime).congr fun n =>
    (primeGapDyadicTerm_eq n).symm

/-- Exact infinite prime-gap reformulation.  Whenever the normalized prime
series is summable, its sum is `2` plus the sum of the actual consecutive
prime gaps. -/
theorem tsum_primeDyadicTerm_eq_two_add_primeGap
    (hprime : Summable primeDyadicTerm) :
    (∑' n : ℕ, primeDyadicTerm n) =
      2 + ∑' n : ℕ, primeGapDyadicTerm n := by
  have hshift : Summable (fun n => primeDyadicTerm (n + 1)) := by
    simpa [Nat.add_comm] using
      hprime.comp_injective (add_left_injective 1)
  have hsplit := hprime.sum_add_tsum_nat_add 1
  have hshiftSum :
      (∑' n : ℕ, primeDyadicTerm (n + 1)) =
        (∑' n : ℕ, primeDyadicTerm n) - 1 := by
    norm_num [primeDyadicTerm, prime0, Nat.nth_prime_zero_eq_two] at hsplit ⊢
    linarith
  have hgapSum :
      (∑' n : ℕ, primeGapDyadicTerm n) =
        2 * (∑' n : ℕ, primeDyadicTerm (n + 1)) -
          ∑' n : ℕ, primeDyadicTerm n := by
    simpa only [primeGapDyadicTerm_eq] using
      ((hshift.hasSum.mul_left 2).sub hprime.hasSum).tsum_eq
  rw [hgapSum, hshiftSum]
  ring

/-- Erdős #251 is therefore exactly equivalent to irrationality of the
consecutive-prime-gap dyadic series, once summability of the displayed prime
series is supplied. -/
theorem irrational_tsum_primeDyadicTerm_iff_primeGap
    (hprime : Summable primeDyadicTerm) :
    Irrational (∑' n : ℕ, primeDyadicTerm n) ↔
      Irrational (∑' n : ℕ, primeGapDyadicTerm n) := by
  rw [tsum_primeDyadicTerm_eq_two_add_primeGap hprime]
  exact irrational_natCast_add_iff

/-- The zero-based displayed series is `4` plus twice the normalized
prime-gap series. -/
theorem tsum_primeDisplayedDyadicTerm_eq_four_add_two_primeGap
    (hprime : Summable primeDyadicTerm) :
    (∑' n : ℕ, primeDisplayedDyadicTerm n) =
      4 + 2 * ∑' n : ℕ, primeGapDyadicTerm n := by
  calc
    (∑' n : ℕ, primeDisplayedDyadicTerm n) =
        2 * ∑' n : ℕ, primeDyadicTerm n :=
      (by simpa only [primeDisplayedDyadicTerm_eq_two_mul] using
        (hprime.hasSum.mul_left 2).tsum_eq)
    _ = 4 + 2 * ∑' n : ℕ, primeGapDyadicTerm n := by
      rw [tsum_primeDyadicTerm_eq_two_add_primeGap hprime]
      ring

/-- Direct irrationality equivalence for the indexing used in the formal
conjecture. -/
theorem irrational_tsum_primeDisplayedDyadicTerm_iff_primeGap
    (hprime : Summable primeDyadicTerm) :
    Irrational (∑' n : ℕ, primeDisplayedDyadicTerm n) ↔
      Irrational (∑' n : ℕ, primeGapDyadicTerm n) := by
  rw [tsum_primeDisplayedDyadicTerm_eq_four_add_two_primeGap hprime]
  constructor
  · intro h
    exact (Irrational.of_natCast_add 4 h).of_natCast_mul 2
  · intro h
    exact (h.natCast_mul (by norm_num : (2 : ℕ) ≠ 0)).natCast_add 4

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

/-- The integer block accumulated through `h` dyadic tail steps beginning at
index `N`.  Recursively, this is
`g (N+1) * 2^(h-1) + ⋯ + g (N+h)`. -/
def dyadicTailBlock (g : ℕ → ℤ) (N : ℕ) : ℕ → ℤ
  | 0 => 0
  | h + 1 => 2 * dyadicTailBlock g N h + g (N + h + 1)

/-- Iterating the tail recurrence for `h` steps gives the exact finite block
identity `T_(N+h) = 2^h T_N - B_(h,N)`. -/
theorem tail_iterate_eq_pow_mul_sub_block
    {g : ℕ → ℤ} {T : ℕ → ℚ}
    (hrec : DyadicTailRecurrence g T) (N h : ℕ) :
    T (N + h) = 2 ^ h * T N - dyadicTailBlock g N h := by
  induction h with
  | zero => simp [dyadicTailBlock]
  | succ h ih =>
      rw [show N + (h + 1) = (N + h) + 1 by omega, hrec (N + h), ih]
      simp only [dyadicTailBlock, pow_succ]
      push_cast
      ring

/-- The shifted-tail difference is a scaled copy of `T_N`, up to the explicit
integer block. -/
theorem tailShift_eq_scaled_sub_block
    {g : ℕ → ℤ} {T : ℕ → ℚ}
    (hrec : DyadicTailRecurrence g T) (N h : ℕ) :
    tailShift T h N =
      ((2 ^ h : ℚ) - 1) * T N - dyadicTailBlock g N h := by
  rw [tailShift, tail_iterate_eq_pow_mul_sub_block hrec]
  ring

/-- Subtracting an integer does not change whether a rational number is
integral. -/
theorem ratIntegral_sub_int_iff (x : ℚ) (z : ℤ) :
    RatIntegral (x - z) ↔ RatIntegral x := by
  constructor
  · rintro ⟨k, hk⟩
    refine ⟨k + z, ?_⟩
    calc
      x = (x - (z : ℚ)) + z := by ring
      _ = (k : ℚ) + z := by rw [hk]
      _ = ((k + z : ℤ) : ℚ) := by push_cast; ring
  · rintro ⟨k, hk⟩
    refine ⟨k - z, ?_⟩
    rw [hk]
    push_cast
    ring

/-- Euler's congruence turns an odd reduced denominator into an explicit
integral multiplier: if `d = x.den` is odd, then
`(2^(phi d) - 1) * x` is an integer. -/
theorem ratIntegral_totientMultiplier_of_odd_den
    (x : ℚ) (hodd : Odd x.den) :
    RatIntegral (((2 : ℚ) ^ x.den.totient - 1) * x) := by
  have hcoprime : Nat.Coprime 2 x.den :=
    Nat.coprime_two_left.mpr hodd
  have hmod : 2 ^ x.den.totient ≡ 1 [MOD x.den] :=
    Nat.ModEq.pow_totient hcoprime
  have hone : 1 ≤ 2 ^ x.den.totient := Nat.one_le_two_pow
  have hdiv : x.den ∣ 2 ^ x.den.totient - 1 :=
    (Nat.modEq_iff_dvd' hone).mp hmod.symm
  obtain ⟨k, hk⟩ := hdiv
  have hkQ : (2 : ℚ) ^ x.den.totient - 1 = x.den * k := by
    exact_mod_cast hk
  refine ⟨(k : ℤ) * x.num, ?_⟩
  calc
    ((2 : ℚ) ^ x.den.totient - 1) * x =
        ((2 : ℚ) ^ x.den.totient - 1) *
          ((x.num : ℚ) / (x.den : ℚ)) := by rw [Rat.num_div_den]
    _ = ((x.den : ℚ) * k) * ((x.num : ℚ) / (x.den : ℚ)) := by
      rw [hkQ]
    _ = (((k : ℤ) * x.num : ℤ) : ℚ) := by
      field_simp [x.den_ne_zero]
      push_cast
      ring

/-- Exact algebraic core of the integral-shift criterion: one tail shift is
integral exactly when `(2^h - 1) * T_N` is integral.  Connecting `T_N` to the
actual infinite prime-gap series remains a separate analytic interface. -/
theorem tailShift_integral_iff_scaledTail
    {g : ℕ → ℤ} {T : ℕ → ℚ}
    (hrec : DyadicTailRecurrence g T) (N h : ℕ) :
    RatIntegral (tailShift T h N) ↔
      RatIntegral (((2 ^ h : ℚ) - 1) * T N) := by
  rw [tailShift_eq_scaled_sub_block hrec]
  exact ratIntegral_sub_int_iff _ _

/-- If one tail state has odd reduced denominator `d`, its shift by
`Nat.totient d` steps is integral.  This is the explicit finite-algebraic
consequence of rationality supplied by Euler's theorem. -/
theorem tailShift_integral_totient_of_odd_den
    {g : ℕ → ℤ} {T : ℕ → ℚ}
    (hrec : DyadicTailRecurrence g T) (N : ℕ)
    (hodd : Odd (T N).den) :
    RatIntegral (tailShift T (T N).den.totient N) := by
  rw [tailShift_integral_iff_scaledTail hrec]
  exact ratIntegral_totientMultiplier_of_odd_den (T N) hodd

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

/-- Repeated doubling removes the entire power-of-two part of a rational
denominator.  The remaining reduced denominator is therefore odd. -/
theorem exists_twoPow_mul_odd_den (q : ℚ) :
    ∃ k : ℕ, Odd (((2 : ℚ) ^ k * q).den) := by
  obtain ⟨k, m, hm, hden⟩ :=
    Nat.exists_eq_two_pow_mul_odd q.den_ne_zero
  have hm0 : m ≠ 0 := by
    intro hmzero
    simp [hmzero] at hden
  have hdenQ : (q.den : ℚ) = (2 : ℚ) ^ k * m := by
    exact_mod_cast hden
  have hq :
      (2 : ℚ) ^ k * q = (q.num : ℚ) / (m : ℚ) := by
    calc
      (2 : ℚ) ^ k * q =
          (2 : ℚ) ^ k * ((q.num : ℚ) / (q.den : ℚ)) := by
            rw [q.num_div_den]
      _ = (q.num : ℚ) / (m : ℚ) := by
        rw [hdenQ]
        field_simp [hm0]
  have hcoprime : Nat.Coprime q.num.natAbs m := by
    exact q.reduced.of_dvd_right ⟨2 ^ k, by rw [hden, Nat.mul_comm]⟩
  refine ⟨k, ?_⟩
  rw [hq]
  have hdenm :
      ((q.num : ℚ) / (m : ℚ)).den = m := by
    have hdenmZ := Rat.den_div_eq_of_coprime
      (a := q.num) (b := (m : ℤ))
      (by simpa only [Int.natCast_pos] using Nat.pos_of_ne_zero hm0)
      (by simpa using hcoprime)
    exact_mod_cast hdenmZ
  rw [hdenm]
  exact hm

/-- Every rational-valued dyadic tail recurrence has an odd-denominator state.
The index is exactly the number of doublings needed to clear the initial
power-of-two denominator. -/
theorem exists_odd_den_state
    {g : ℕ → ℤ} {T : ℕ → ℚ}
    (hrec : DyadicTailRecurrence g T) :
    ∃ N : ℕ, Odd (T N).den := by
  obtain ⟨N, hodd⟩ := exists_twoPow_mul_odd_den (T 0)
  refine ⟨N, ?_⟩
  have hstate := tail_iterate_eq_pow_mul_sub_block hrec 0 N
  have hdenEq :
      (T N).den = (((2 : ℚ) ^ N * T 0).den) := by
    simpa using congrArg Rat.den hstate
  rw [hdenEq]
  exact hodd

/-- Rationality forces one fixed positive shift to be integral from some point
onwards.  This is the exact contrapositive consumer for a prime-specific
cofinal non-integrality theorem. -/
theorem exists_eventually_integral_tailShift
    {g : ℕ → ℤ} {T : ℕ → ℚ}
    (hrec : DyadicTailRecurrence g T) :
    ∃ h N : ℕ, 0 < h ∧
      ∀ k, RatIntegral (tailShift T h (N + k)) := by
  obtain ⟨N, hodd⟩ := exists_odd_den_state hrec
  let h := (T N).den.totient
  have hh : 0 < h := Nat.totient_pos.mpr (T N).den_pos
  refine ⟨h, N, hh, ?_⟩
  exact tailShift_integral_add hrec
    (tailShift_integral_totient_of_odd_den hrec N hodd)

/-! ## The real-orbit irrationality consumer -/

/-- Real-valued version of the dyadic tail recurrence. -/
def RealDyadicTailRecurrence (g : ℕ → ℤ) (T : ℕ → ℝ) : Prop :=
  ∀ N, T (N + 1) = 2 * T N - g (N + 1)

/-- Difference between two real tail states separated by `h` steps. -/
def realTailShift (T : ℕ → ℝ) (h N : ℕ) : ℝ :=
  T (N + h) - T N

/-- A real number is integral when it is the cast of an integer. -/
def RealIntegral (x : ℝ) : Prop :=
  ∃ z : ℤ, x = z

/-- Rational orbit with prescribed initial state and integer digits. -/
def rationalDyadicOrbit (g : ℕ → ℤ) (q : ℚ) : ℕ → ℚ
  | 0 => q
  | N + 1 => 2 * rationalDyadicOrbit g q N - g (N + 1)

theorem rationalDyadicOrbit_recurrence (g : ℕ → ℤ) (q : ℚ) :
    DyadicTailRecurrence g (rationalDyadicOrbit g q) := by
  intro N
  rfl

/-- A real recurrence with rational initial state is the real cast of the
corresponding rational recurrence at every later index. -/
theorem realTail_eq_ratCast_rationalDyadicOrbit
    {g : ℕ → ℤ} {T : ℕ → ℝ}
    (hrec : RealDyadicTailRecurrence g T) (q : ℚ)
    (hzero : T 0 = q) :
    ∀ N, T N = (rationalDyadicOrbit g q N : ℝ)
  | 0 => by simpa [rationalDyadicOrbit] using hzero
  | N + 1 => by
      rw [hrec N, rationalDyadicOrbit,
        realTail_eq_ratCast_rationalDyadicOrbit hrec q hzero N]
      push_cast
      rfl

/-- Cofinal failure of integral shifts for every fixed positive length. -/
def CofinalNonintegralTailShifts (T : ℕ → ℝ) : Prop :=
  ∀ h, 0 < h → ∀ N₀, ∃ N, N₀ ≤ N ∧
    ¬RealIntegral (realTailShift T h N)

/-- Exact proof consumer: to prove the initial value irrational, it is enough
to rule out eventual integrality cofinally for every fixed positive shift.
Rationality would produce a rational orbit, and the denominator-collapse
theorem above produces one fixed shift integral at every sufficiently late
index. -/
theorem irrational_initial_of_cofinalNonintegralTailShifts
    {g : ℕ → ℤ} {T : ℕ → ℝ}
    (hrec : RealDyadicTailRecurrence g T)
    (hescape : CofinalNonintegralTailShifts T) :
    Irrational (T 0) := by
  by_contra hnot
  obtain ⟨q, hq⟩ := exists_rat_of_not_irrational hnot
  have hcast := realTail_eq_ratCast_rationalDyadicOrbit hrec q hq
  obtain ⟨h, N₀, hh, hInt⟩ :=
    exists_eventually_integral_tailShift
      (rationalDyadicOrbit_recurrence g q)
  obtain ⟨N, hN, hnon⟩ := hescape h hh N₀
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hN
  apply hnon
  obtain ⟨z, hz⟩ := hInt k
  refine ⟨z, ?_⟩
  have hzR := congrArg ((↑) : ℚ → ℝ) hz
  simpa [realTailShift, tailShift, hcast] using hzR

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
