import Mathlib.Data.Nat.Prime.Nth
import Mathlib.Data.Nat.PrimeFin
import Mathlib.Data.Nat.Factorization.Basic
import Mathlib.Data.Nat.Prime.Factorial
import Mathlib.Data.Nat.Periodic
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

For a rational dyadic tail state with reduced denominator `d`, a shift of
length `h` is integral exactly when `d ∣ 2^h - 1`, equivalently when
`2^h ≡ 1 (mod d)`. Thus the possible integral shifts are classified by the
arithmetic of the current denominator, rather than by a heuristic analogy
with periodic digit words. One recurrence step replaces `d` by
`d / gcd(2, d)`: an even denominator is halved, while an odd denominator is
unchanged. Integrality then propagates to every later state.

For real-valued recurrences, the initial state is irrational exactly when
every positive tail shift is nonintegral; rationality is equivalent to the
existence of a positive shift that is eventually integral. The module also
proves the exact summation-by-parts reduction from the prime series to the
consecutive-prime-gap series and proves that the prime-gap word is not
eventually periodic.

What remains for the original problem is the analytic input: cofinally many
small, nonintegral shifts for the actual consecutive prime gaps. The finite
consumers for such an input are formalized below.
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

/-- The classical factorial construction gives arbitrarily long prime-free
intervals, hence the actual consecutive-prime gaps are unbounded. -/
theorem exists_primeGap0_gt (M : ℕ) :
    ∃ n, M < primeGap0 n := by
  let width := M + 2
  let base := width.factorial
  let primeCount := Nat.count Nat.Prime (base + 2)
  have hbasePos : 0 < base := Nat.factorial_pos width
  have hcountPos : 0 < primeCount := by
    apply Nat.pos_of_ne_zero
    exact Nat.count_ne_iff_exists.mpr
      ⟨2, by simp [base, hbasePos], Nat.prime_two⟩
  let n := primeCount - 1
  have hnSucc : n + 1 = primeCount := by
    exact Nat.sub_add_cancel hcountPos
  have hprev : prime0 n < base + 2 := by
    rw [prime0]
    apply Nat.nth_lt_of_lt_count
    change primeCount - 1 < primeCount
    omega
  have hnextPrime : Nat.Prime (prime0 (n + 1)) := by
    rw [prime0]
    exact Nat.nth_mem_of_infinite Nat.infinite_setOf_prime _
  have hnextLower : base + 2 ≤ prime0 (n + 1) := by
    rw [prime0, hnSucc]
    exact Nat.le_nth_count Nat.infinite_setOf_prime (base + 2)
  have hcomposite :
      ∀ i, 2 ≤ i → i ≤ width → ¬ Nat.Prime (base + i) := by
    intro i hiTwo hiWidth
    apply Nat.not_prime_of_dvd_of_lt (m := i)
    · simpa [base] using Nat.dvd_factorial (by omega) hiWidth
    · exact hiTwo
    · omega
  have hnext : base + width < prime0 (n + 1) := by
    by_contra h
    have hnextUpper : prime0 (n + 1) ≤ base + width := by omega
    let i := prime0 (n + 1) - base
    have hiTwo : 2 ≤ i := by omega
    have hiWidth : i ≤ width := by omega
    have hsplit : base + i = prime0 (n + 1) := by omega
    exact hcomposite i hiTwo hiWidth (hsplit ▸ hnextPrime)
  refine ⟨n, ?_⟩
  rw [primeGap0]
  omega

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

/-- Doubling a reduced rational removes exactly the common factor of its
denominator with `2`. -/
theorem den_two_mul (x : ℚ) :
    ((2 : ℚ) * x).den = x.den / Nat.gcd 2 x.den := by
  rw [Rat.mul_den]
  simp only [Rat.den_ofNat, Rat.num_ofNat, one_mul, Int.natAbs_mul]
  change x.den / Nat.gcd (2 * x.num.natAbs) x.den =
    x.den / Nat.gcd 2 x.den
  congr 1
  apply Nat.dvd_antisymm
  · apply Nat.dvd_gcd
    · have hgprod :
          Nat.gcd (2 * x.num.natAbs) x.den ∣
            2 * x.num.natAbs := Nat.gcd_dvd_left _ _
      have hgden :
          Nat.gcd (2 * x.num.natAbs) x.den ∣ x.den :=
        Nat.gcd_dvd_right _ _
      have hcop :
          Nat.Coprime (Nat.gcd (2 * x.num.natAbs) x.den)
            x.num.natAbs :=
        (x.reduced.of_dvd_right hgden).symm
      exact hcop.dvd_mul_right.mp hgprod
    · exact Nat.gcd_dvd_right _ _
  · apply Nat.dvd_gcd
    · exact (Nat.gcd_dvd_left 2 x.den).mul_right x.num.natAbs
    · exact Nat.gcd_dvd_right _ _

/-- Exact one-step denominator dynamics for a rational dyadic tail: the next
denominator is the current denominator divided by its gcd with `2`. -/
theorem tail_den_succ
    {g : ℕ → ℤ} {T : ℕ → ℚ}
    (hrec : DyadicTailRecurrence g T) (N : ℕ) :
    (T (N + 1)).den = (T N).den / Nat.gcd 2 (T N).den := by
  have hden := congrArg Rat.den (hrec N)
  simpa [den_two_mul] using hden

/-- An odd rational tail denominator is unchanged by the next recurrence
step. Since it remains odd, the same conclusion can then be iterated. -/
theorem tail_den_succ_eq_of_odd
    {g : ℕ → ℤ} {T : ℕ → ℚ}
    (hrec : DyadicTailRecurrence g T) (N : ℕ)
    (hodd : Odd (T N).den) :
    (T (N + 1)).den = (T N).den := by
  rw [tail_den_succ hrec]
  rw [hodd.coprime_two_left.gcd_eq_one, Nat.div_one]

/-- An even rational tail denominator loses exactly one factor of `2` at the
next recurrence step. -/
theorem tail_den_succ_eq_half_of_even
    {g : ℕ → ℤ} {T : ℕ → ℚ}
    (hrec : DyadicTailRecurrence g T) (N : ℕ)
    (heven : Even (T N).den) :
    (T (N + 1)).den = (T N).den / 2 := by
  rw [tail_den_succ hrec]
  rw [Nat.gcd_eq_left_iff_dvd.mpr (even_iff_two_dvd.mp heven)]

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

/-- A rational number is integral exactly when its reduced denominator is
one. -/
theorem ratIntegral_iff_den_eq_one (x : ℚ) :
    RatIntegral x ↔ x.den = 1 := by
  constructor
  · rintro ⟨z, rfl⟩
    simp
  · intro hden
    refine ⟨x.num, ?_⟩
    exact (Rat.den_eq_one_iff x).mp hden |>.symm

/-- Multiplication by a natural number clears a rational denominator exactly
when that denominator divides the multiplier. -/
theorem ratIntegral_nat_mul_iff_den_dvd (x : ℚ) (m : ℕ) :
    RatIntegral ((m : ℚ) * x) ↔ x.den ∣ m := by
  rw [ratIntegral_iff_den_eq_one]
  have hrepr :
      (m : ℚ) * x =
        ((((m : ℤ) * x.num : ℤ) : ℚ) / (x.den : ℤ)) := by
    calc
      (m : ℚ) * x =
          (m : ℚ) * ((x.num : ℚ) / (x.den : ℚ)) := by
            rw [Rat.num_div_den]
      _ = ((((m : ℤ) * x.num : ℤ) : ℚ) / (x.den : ℤ)) := by
            push_cast
            ring
  rw [hrepr, Rat.den_div_intCast_eq_one_iff _ _]
  · rw [Int.natCast_dvd]
    simp only [Int.natAbs_mul, Int.natAbs_natCast]
    exact x.reduced.symm.dvd_mul_right
  · exact Int.ofNat_ne_zero.mpr x.den_ne_zero

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

/-- Exact denominator classification of all integral shift lengths.  A shift
by `h` steps is integral precisely when the reduced denominator of the current
tail divides the Mersenne number `2^h - 1`. -/
theorem tailShift_integral_iff_den_dvd_mersenne
    {g : ℕ → ℤ} {T : ℕ → ℚ}
    (hrec : DyadicTailRecurrence g T) (N h : ℕ) :
    RatIntegral (tailShift T h N) ↔ (T N).den ∣ 2 ^ h - 1 := by
  rw [tailShift_integral_iff_scaledTail hrec]
  have hone : 1 ≤ 2 ^ h := Nat.one_le_two_pow
  simpa [Nat.cast_sub hone] using
    (ratIntegral_nat_mul_iff_den_dvd (T N) (2 ^ h - 1))

/-- Congruence form of the exact shift-length classification: the integral
shifts are precisely the exponents for which `2^h` is congruent to `1` modulo
the current reduced denominator. -/
theorem tailShift_integral_iff_two_pow_modEq_one
    {g : ℕ → ℤ} {T : ℕ → ℚ}
    (hrec : DyadicTailRecurrence g T) (N h : ℕ) :
    RatIntegral (tailShift T h N) ↔
      2 ^ h ≡ 1 [MOD (T N).den] := by
  rw [tailShift_integral_iff_den_dvd_mersenne hrec]
  have hone : 1 ≤ 2 ^ h := Nat.one_le_two_pow
  constructor
  · intro hdiv
    exact ((Nat.modEq_iff_dvd' hone).mpr hdiv).symm
  · intro hmod
    exact (Nat.modEq_iff_dvd' hone).mp hmod.symm

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
/-! ## Eventual integrality collapses under a shrinking shift -/

/-- An integral rational lying strictly between `-1` and `1` is zero. -/
theorem ratIntegral_eq_zero_of_neg_one_lt_of_lt_one
    {x : ℚ} (hInt : RatIntegral x) (hlow : -1 < x) (hhigh : x < 1) :
    x = 0 := by
  rcases hInt with ⟨z, rfl⟩
  have hzlow : (-1 : ℤ) < z := by exact_mod_cast hlow
  have hzhigh : z < (1 : ℤ) := by exact_mod_cast hhigh
  have : z = 0 := by omega
  simp [this]

/-- If one fixed tail shift is eventually integral and eventually lies in the
open unit interval around zero, then that shift is eventually identically
zero.  This is the discrete rigidity step needed to turn an analytic
small-shift estimate into exact arithmetic information. -/
theorem tailShift_eventually_zero_of_eventually_integral_of_eventually_small
    {T : ℕ → ℚ} {h : ℕ}
    (hInt : ∃ N₀, ∀ N, N₀ ≤ N → RatIntegral (tailShift T h N))
    (hsmall : ∃ N₀, ∀ N, N₀ ≤ N →
      -1 < tailShift T h N ∧ tailShift T h N < 1) :
    ∃ N₀, ∀ N, N₀ ≤ N → tailShift T h N = 0 := by
  rcases hInt with ⟨NInt, hInt⟩
  rcases hsmall with ⟨NSmall, hsmall⟩
  refine ⟨max NInt NSmall, fun N hN => ?_⟩
  exact ratIntegral_eq_zero_of_neg_one_lt_of_lt_one
    (hInt N ((le_max_left _ _).trans hN))
    (hsmall N ((le_max_right _ _).trans hN)).1
    (hsmall N ((le_max_right _ _).trans hN)).2

/-- For an integer-digit dyadic recurrence, eventual integrality plus an
eventually small fixed shift forces the digit word to be eventually periodic
with that shift.  This is a strong global route; the adjacent-pair consumer
below isolates a weaker cofinal local supply. -/
theorem digits_eventually_periodic_of_eventually_integralTailShift_of_eventually_small
    {g : ℕ → ℤ} {T : ℕ → ℚ}
    (hrec : DyadicTailRecurrence g T) (h : ℕ)
    (hInt : ∃ N₀, ∀ N, N₀ ≤ N → RatIntegral (tailShift T h N))
    (hsmall : ∃ N₀, ∀ N, N₀ ≤ N →
      -1 < tailShift T h N ∧ tailShift T h N < 1) :
    ∃ N₀, ∀ N, N₀ ≤ N → g (N + h + 1) = g (N + 1) := by
  obtain ⟨N₀, hzero⟩ :=
    tailShift_eventually_zero_of_eventually_integral_of_eventually_small
      hInt hsmall
  refine ⟨N₀, fun N hN => ?_⟩
  have hstep := tailShift_succ hrec h N
  rw [hzero N hN, hzero (N + 1) (hN.trans (Nat.le_succ N))] at hstep
  have hcast :
      (g (N + h + 1) : ℚ) = (g (N + 1) : ℚ) := by
    linarith
  exact_mod_cast hcast

/-- Contrapositive consumer: if the digit word is not eventually periodic
with shift `h`, then an eventually small `h`-shift cannot also be eventually
integral. -/
theorem not_eventuallyIntegralTailShift_of_eventually_small_of_not_periodic
    {g : ℕ → ℤ} {T : ℕ → ℚ}
    (hrec : DyadicTailRecurrence g T) (h : ℕ)
    (hsmall : ∃ N₀, ∀ N, N₀ ≤ N →
      -1 < tailShift T h N ∧ tailShift T h N < 1)
    (hnotPeriodic :
      ¬ ∃ N₀, ∀ N, N₀ ≤ N → g (N + h + 1) = g (N + 1)) :
    ¬ ∃ N₀, ∀ N, N₀ ≤ N → RatIntegral (tailShift T h N) := by
  intro hInt
  exact hnotPeriodic
    (digits_eventually_periodic_of_eventually_integralTailShift_of_eventually_small
      hrec h hInt hsmall)

/-- A single adjacent pair of small shifts with a mismatching digit difference
already excludes simultaneous integrality.  This is the shortest finite
consumer for a growing-block anti-concentration certificate. -/
theorem tailShift_not_both_integral_of_small_pair_of_digit_ne
    {g : ℕ → ℤ} {T : ℕ → ℚ}
    (hrec : DyadicTailRecurrence g T) (h N : ℕ)
    (hsmall :
      (-1 < tailShift T h N ∧ tailShift T h N < 1) ∧
      (-1 < tailShift T h (N + 1) ∧ tailShift T h (N + 1) < 1))
    (hdigit : g (N + h + 1) ≠ g (N + 1)) :
    ¬ (RatIntegral (tailShift T h N) ∧
      RatIntegral (tailShift T h (N + 1))) := by
  rintro ⟨hIntN, hIntSucc⟩
  have hzeroN : tailShift T h N = 0 :=
    ratIntegral_eq_zero_of_neg_one_lt_of_lt_one
      hIntN hsmall.1.1 hsmall.1.2
  have hzeroSucc : tailShift T h (N + 1) = 0 :=
    ratIntegral_eq_zero_of_neg_one_lt_of_lt_one
      hIntSucc hsmall.2.1 hsmall.2.2
  have hstep := tailShift_succ hrec h N
  rw [hzeroN, hzeroSucc] at hstep
  apply hdigit
  have hcast :
      (g (N + h + 1) : ℚ) = (g (N + 1) : ℚ) := by
    linarith
  exact_mod_cast hcast

/-- Cofinal finite-certificate consumer.  To rule out eventual integrality of
a fixed shift it is enough to find, beyond every level, one adjacent pair of
strictly small shifts whose corresponding digits differ. -/
theorem not_eventuallyIntegralTailShift_of_cofinal_small_mismatch
    {g : ℕ → ℤ} {T : ℕ → ℚ}
    (hrec : DyadicTailRecurrence g T) (h : ℕ)
    (hsupply : ∀ N₀, ∃ N, N₀ ≤ N ∧
      ((-1 < tailShift T h N ∧ tailShift T h N < 1) ∧
       (-1 < tailShift T h (N + 1) ∧ tailShift T h (N + 1) < 1)) ∧
      g (N + h + 1) ≠ g (N + 1)) :
    ¬ ∃ N₀, ∀ N, N₀ ≤ N → RatIntegral (tailShift T h N) := by
  rintro ⟨N₀, hInt⟩
  obtain ⟨N, hN, hsmall, hdigit⟩ := hsupply N₀
  exact tailShift_not_both_integral_of_small_pair_of_digit_ne
    hrec h N hsmall hdigit
    ⟨hInt N hN, hInt (N + 1) (hN.trans (Nat.le_succ N))⟩

/-- Consecutive prime gaps cannot become periodic with any positive period.
The proof combines the exact factorial prime-free intervals above with the
finite range of a periodic natural-valued sequence. -/
theorem primeGap0_not_eventually_periodic
    {h : ℕ} (hpos : 0 < h) :
    ¬ ∃ N₀, ∀ N, N₀ ≤ N →
      primeGap0 (N + h + 1) = primeGap0 (N + 1) := by
  rintro ⟨N₀, hperiodic⟩
  let f : ℕ → ℕ := fun k => primeGap0 (N₀ + 1 + k)
  have hf : Function.Periodic f h := by
    intro k
    have hk := hperiodic (N₀ + k) (Nat.le_add_right N₀ k)
    simpa [f, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hk
  let periodBound := ∑ i ∈ Finset.range h, f i
  let initialBound := ∑ i ∈ Finset.range (N₀ + 1), primeGap0 i
  obtain ⟨n, hn⟩ := exists_primeGap0_gt (periodBound + initialBound)
  have hnLate : N₀ + 1 ≤ n := by
    by_contra h
    have hnMem : n ∈ Finset.range (N₀ + 1) := Finset.mem_range.mpr (by omega)
    have hnInitial : primeGap0 n ≤ initialBound := by
      exact Finset.single_le_sum (fun _ _ => Nat.zero_le _) hnMem
    omega
  let k := n - (N₀ + 1)
  have hkEq : N₀ + 1 + k = n := by
    exact Nat.add_sub_of_le hnLate
  have hkMem : k % h ∈ Finset.range h :=
    Finset.mem_range.mpr (Nat.mod_lt k hpos)
  have hkBound : f k ≤ periodBound := by
    calc
      f k = f (k % h) := (hf.map_mod_nat k).symm
      _ ≤ periodBound :=
        Finset.single_le_sum (fun _ _ => Nat.zero_le _) hkMem
  change primeGap0 (N₀ + 1 + k) ≤ periodBound at hkBound
  rw [hkEq] at hkBound
  omega

/-- Prime-specific global exclusion of eventual integral tail shifts.
Eventual strict smallness would force periodicity, which the factorial gap
theorem rules out.  The next theorem uses only cofinally many local
small-mismatch certificates. -/
theorem primeGapTailShift_not_eventuallyIntegral_of_eventually_small
    {T : ℕ → ℚ} {h : ℕ}
    (hrec : DyadicTailRecurrence (fun n => (primeGap0 n : ℤ)) T)
    (hpos : 0 < h)
    (hsmall : ∃ N₀, ∀ N, N₀ ≤ N →
      -1 < tailShift T h N ∧ tailShift T h N < 1) :
    ¬ ∃ N₀, ∀ N, N₀ ≤ N → RatIntegral (tailShift T h N) := by
  apply not_eventuallyIntegralTailShift_of_eventually_small_of_not_periodic
    hrec h hsmall
  intro hperiodic
  apply primeGap0_not_eventually_periodic hpos
  rcases hperiodic with ⟨N₀, hperiodic⟩
  refine ⟨N₀, fun N hN => ?_⟩
  exact_mod_cast hperiodic N hN

/-- Actual-prime-gap version of the cofinal finite-certificate consumer. -/
theorem primeGapTailShift_not_eventuallyIntegral_of_cofinal_small_mismatch
    {T : ℕ → ℚ} (h : ℕ)
    (hrec : DyadicTailRecurrence (fun n => (primeGap0 n : ℤ)) T)
    (hsupply : ∀ N₀, ∃ N, N₀ ≤ N ∧
      ((-1 < tailShift T h N ∧ tailShift T h N < 1) ∧
       (-1 < tailShift T h (N + 1) ∧ tailShift T h (N + 1) < 1)) ∧
      primeGap0 (N + h + 1) ≠ primeGap0 (N + 1)) :
    ¬ ∃ N₀, ∀ N, N₀ ≤ N → RatIntegral (tailShift T h N) := by
  apply not_eventuallyIntegralTailShift_of_cofinal_small_mismatch hrec h
  intro N₀
  obtain ⟨N, hN, hsmall, hdigit⟩ := hsupply N₀
  refine ⟨N, hN, hsmall, ?_⟩
  exact_mod_cast hdigit

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

/-- A finite approximation certifies nonintegrality when its error is no
larger than `R` and the approximation stays farther than `R` from every
integer. -/
theorem not_ratIntegral_of_approximation_gap
    (full approx R : ℚ)
    (herror : |full - approx| ≤ R)
    (hgap : ∀ z : ℤ, R < |approx - z|) :
    ¬ RatIntegral full := by
  rintro ⟨z, rfl⟩
  have hle : |approx - (z : ℚ)| ≤ R := by
    simpa [abs_sub_comm] using herror
  exact (not_lt_of_ge hle) (hgap z)

/-! ## Exact rationality classification for real dyadic tail orbits -/

/-- Iterating a real dyadic tail recurrence produces the same integer block as
in the rational orbit. -/
theorem real_tail_iterate_eq_pow_mul_sub_block
    {g : ℕ → ℤ} {T : ℕ → ℝ}
    (hrec : RealDyadicTailRecurrence g T) (N h : ℕ) :
    T (N + h) = 2 ^ h * T N - dyadicTailBlock g N h := by
  induction h with
  | zero => simp [dyadicTailBlock]
  | succ h ih =>
      rw [show N + (h + 1) = (N + h) + 1 by omega, hrec (N + h), ih]
      simp only [dyadicTailBlock, pow_succ]
      push_cast
      ring

/-- A real tail difference is a nonzero integer multiple of its initial state,
up to the explicit integer block. -/
theorem realTailShift_eq_scaled_sub_block
    {g : ℕ → ℤ} {T : ℕ → ℝ}
    (hrec : RealDyadicTailRecurrence g T) (N h : ℕ) :
    realTailShift T h N =
      ((2 ^ h : ℝ) - 1) * T N - dyadicTailBlock g N h := by
  rw [realTailShift, real_tail_iterate_eq_pow_mul_sub_block hrec]
  ring

/-- Exact classifier for an integer-digit dyadic tail orbit: the initial state
is rational if and only if one positive-length tail difference is integral.
The forward direction uses denominator collapse; the reverse direction uses
the nonzero multiplier `2^h - 1` in the block identity. -/
theorem not_irrational_initial_iff_exists_integral_positive_tailShift
    {g : ℕ → ℤ} {T : ℕ → ℝ}
    (hrec : RealDyadicTailRecurrence g T) :
    ¬ Irrational (T 0) ↔
      ∃ h N : ℕ, 0 < h ∧ RealIntegral (realTailShift T h N) := by
  constructor
  · intro hrat
    obtain ⟨q, hq⟩ := exists_rat_of_not_irrational hrat
    have hcast := realTail_eq_ratCast_rationalDyadicOrbit hrec q hq
    obtain ⟨h, N, hh, hInt⟩ :=
      exists_eventually_integral_tailShift
        (rationalDyadicOrbit_recurrence g q)
    refine ⟨h, N, hh, ?_⟩
    obtain ⟨z, hz⟩ := hInt 0
    refine ⟨z, ?_⟩
    have hzR := congrArg ((↑) : ℚ → ℝ) hz
    simpa [realTailShift, tailShift, hcast] using hzR
  · rintro ⟨h, N, hh, z, hz⟩
    have hpowNat : 1 < 2 ^ h := Nat.one_lt_two_pow hh.ne'
    have hpowR : (1 : ℝ) < (2 : ℝ) ^ h := by exact_mod_cast hpowNat
    have hfactor : (2 : ℝ) ^ h - 1 ≠ 0 :=
      sub_ne_zero.mpr (ne_of_gt hpowR)
    let qN : ℚ :=
      ((z + dyadicTailBlock g N h : ℤ) : ℚ) / ((2 : ℚ) ^ h - 1)
    have hTN : T N = (qN : ℝ) := by
      rw [realTailShift_eq_scaled_sub_block hrec] at hz
      dsimp [qN]
      push_cast
      field_simp [hfactor]
      linarith
    let q0 : ℚ :=
      (qN + dyadicTailBlock g 0 N) / (2 : ℚ) ^ N
    have hpow0 : (2 : ℝ) ^ N ≠ 0 := pow_ne_zero _ (by norm_num)
    have hT0 : T 0 = (q0 : ℝ) := by
      have hiterate := real_tail_iterate_eq_pow_mul_sub_block hrec 0 N
      simp only [Nat.zero_add] at hiterate
      dsimp [q0]
      push_cast
      field_simp [hpow0]
      rw [hTN] at hiterate
      linarith
    rw [hT0]
    exact q0.not_irrational

/-- Equivalent eventual form of the classifier: rationality is exactly the
existence of a fixed positive shift that is integral at every later index. -/
theorem not_irrational_initial_iff_exists_eventually_integral_positive_tailShift
    {g : ℕ → ℤ} {T : ℕ → ℝ}
    (hrec : RealDyadicTailRecurrence g T) :
    ¬ Irrational (T 0) ↔
      ∃ h N : ℕ, 0 < h ∧
        ∀ k, RealIntegral (realTailShift T h (N + k)) := by
  constructor
  · intro hrat
    obtain ⟨q, hq⟩ := exists_rat_of_not_irrational hrat
    have hcast := realTail_eq_ratCast_rationalDyadicOrbit hrec q hq
    obtain ⟨h, N, hh, hInt⟩ :=
      exists_eventually_integral_tailShift
        (rationalDyadicOrbit_recurrence g q)
    refine ⟨h, N, hh, fun k => ?_⟩
    obtain ⟨z, hz⟩ := hInt k
    refine ⟨z, ?_⟩
    have hzR := congrArg ((↑) : ℚ → ℝ) hz
    simpa [realTailShift, tailShift, hcast] using hzR
  · rintro ⟨h, N, hh, hInt⟩
    exact
      (not_irrational_initial_iff_exists_integral_positive_tailShift hrec).2
        ⟨h, N, hh, hInt 0⟩

/-- Exact irrationality normal form: an integer-digit dyadic tail starts at an
irrational value exactly when none of its positive-length tail differences is
an integer. -/
theorem irrational_initial_iff_all_positive_tailShifts_nonintegral
    {g : ℕ → ℤ} {T : ℕ → ℝ}
    (hrec : RealDyadicTailRecurrence g T) :
    Irrational (T 0) ↔
      ∀ h : ℕ, 0 < h → ∀ N : ℕ,
        ¬ RealIntegral (realTailShift T h N) := by
  constructor
  · intro hirr h hh N hInt
    exact
      (not_irrational_initial_iff_exists_integral_positive_tailShift hrec).2
        ⟨h, N, hh, hInt⟩ hirr
  · intro hnone
    by_contra hrat
    obtain ⟨h, N, hh, hInt⟩ :=
      (not_irrational_initial_iff_exists_integral_positive_tailShift hrec).1 hrat
    exact hnone h hh N hInt

end ErdosProblems.Erdos251
