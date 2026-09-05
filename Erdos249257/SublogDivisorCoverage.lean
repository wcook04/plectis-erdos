import Erdos249257.RationalSupportCarrySkeleton
import Erdos249257.BinaryTailWindowTransfer
import Mathlib.NumberTheory.ArithmeticFunction.Misc

/-!
# Zero-window growth for rational Erdős support series

This file isolates the algebraic consumer boundary of the development's T11
sublogarithmic divisor-coverage claim.  If the support coefficient vanishes
for `h` consecutive indices after `N`, the shifted odd-denominator tail state
from `RationalSupportCarrySkeleton` doubles exactly `h` times.  Positivity of
that state therefore forces

`2^h ≤ v * binaryCoeffTail (supportCoeff A) (c + N + h)`.

The unconditional half is now closed in the same module.  A fixed-natural-
power factorisation argument proves

`τ(n)^k ≤ (k^(2^k))^k * n`.

Taking one real `k`-th root and summing an exact weighted geometric majorant
gives a `1/k` support-tail envelope.  Raising the carry inequality to the
`k`-th power consumes one binary factor from the self-reference through `h`,
which yields the final coefficient `1/(k-1)`.  The theorem
`supportCoeffZeroWindow_length_le_eps_logb` proves the development's
`ε * log₂ N + O(1)` zero-window bound for every positive `N`.

**NON-CLAIM.**  This closes the internal T11 theorem described above; it does
not prove or refute universal Erdős #257, and Erdős #249 also remains open.
-/

namespace Erdos249257

open Set

/-! ## An explicit fixed-power divisor bound -/

/-- A single explicit penalty `k^k` controls every exponent at every prime
at least two. -/
theorem nat_add_one_pow_le_self_pow_mul_two_pow
    (k a : ℕ) (hk : 1 ≤ k) :
    (a + 1) ^ k ≤ k ^ k * 2 ^ a := by
  have hk0 : 0 < k := Nat.zero_lt_of_lt hk
  let q := a / k
  have hmod : a % k < k := Nat.mod_lt a hk0
  have hdecomp : a = q * k + a % k := by
    simpa [q] using (Nat.div_add_mod' a k).symm
  have haq : a + 1 ≤ k * (q + 1) := by
    calc
      a + 1 = q * k + (a % k + 1) := by omega
      _ ≤ q * k + k :=
        Nat.add_le_add_left (Nat.succ_le_iff.mpr hmod) (q * k)
      _ = k * (q + 1) := by ring
  have hq : q + 1 ≤ 2 ^ q := nat_add_one_le_two_pow q
  have hbase : a + 1 ≤ k * 2 ^ q :=
    haq.trans (Nat.mul_le_mul_left k hq)
  calc
    (a + 1) ^ k ≤ (k * 2 ^ q) ^ k := Nat.pow_le_pow_left hbase k
    _ = k ^ k * 2 ^ (q * k) := by rw [mul_pow, ← pow_mul]
    _ ≤ k ^ k * 2 ^ a := by
      apply Nat.mul_le_mul_left
      exact Nat.pow_le_pow_right (by omega) (Nat.div_mul_le_self a k)

/-- Pointwise prime-factor estimate: only primes below `2^k` pay the
explicit `k^k` penalty. -/
theorem factorization_add_one_pow_le_penalty_mul
    (n p k : ℕ) (hk : 1 ≤ k)
    (hp : p ∈ n.primeFactors) :
    (n.factorization p + 1) ^ k ≤
      (if p < 2 ^ k then k ^ k else 1) *
        p ^ n.factorization p := by
  let a := n.factorization p
  have hpprime : p.Prime := Nat.prime_of_mem_primeFactors hp
  have hp2 : 2 ≤ p := hpprime.two_le
  by_cases hsmall : p < 2 ^ k
  · simp only [if_pos hsmall]
    calc
      (a + 1) ^ k ≤ k ^ k * 2 ^ a :=
        nat_add_one_pow_le_self_pow_mul_two_pow k a hk
      _ ≤ k ^ k * p ^ a :=
        Nat.mul_le_mul_left _ (Nat.pow_le_pow_left hp2 a)
  · have hlarge : 2 ^ k ≤ p := Nat.le_of_not_gt hsmall
    simp only [if_neg hsmall, one_mul]
    calc
      (a + 1) ^ k ≤ (2 ^ a) ^ k :=
        Nat.pow_le_pow_left (nat_add_one_le_two_pow a) k
      _ = (2 ^ k) ^ a := by simp only [← pow_mul, Nat.mul_comm k a]
      _ ≤ p ^ a := Nat.pow_le_pow_left hlarge a

/-- There are at most `2^k` prime factors below the cutoff `2^k`. -/
theorem card_small_primeFactors_le_two_pow (n k : ℕ) :
    (n.primeFactors.filter fun p => p < 2 ^ k).card ≤ 2 ^ k := by
  calc
    (n.primeFactors.filter fun p => p < 2 ^ k).card
        ≤ (Finset.range (2 ^ k)).card := by
      apply Finset.card_le_card
      intro p hp
      rw [Finset.mem_filter] at hp
      exact Finset.mem_range.mpr hp.2
    _ = 2 ^ k := Finset.card_range _

/-- Completely explicit constant for the fixed-`k` divisor bound. -/
def divisorSubpowerConst (k : ℕ) : ℕ := k ^ (2 ^ k)

/-- Fixed-natural-power divisor theorem.  All prime-factor bookkeeping is in
`ℕ`; the only loss is the explicit penalty from primes below `2^k`. -/
theorem card_divisors_pow_le_divisorSubpowerConst_pow_mul
    (n k : ℕ) (hn : 0 < n) (hk : 1 ≤ k) :
    n.divisors.card ^ k ≤ divisorSubpowerConst k ^ k * n := by
  have hn0 : n ≠ 0 := Nat.ne_of_gt hn
  rw [Nat.card_divisors hn0, ← Finset.prod_pow]
  calc
    n.primeFactors.prod (fun p => (n.factorization p + 1) ^ k)
        ≤ n.primeFactors.prod (fun p =>
          (if p < 2 ^ k then k ^ k else 1) *
            p ^ n.factorization p) := by
      apply Finset.prod_le_prod
      · intro p hp
        exact Nat.zero_le _
      · intro p hp
        exact factorization_add_one_pow_le_penalty_mul n p k hk hp
    _ =
        n.primeFactors.prod (fun p => if p < 2 ^ k then k ^ k else 1) *
          n.primeFactors.prod (fun p => p ^ n.factorization p) := by
      rw [Finset.prod_mul_distrib]
    _ =
        (k ^ k) ^ (n.primeFactors.filter fun p => p < 2 ^ k).card * n := by
      congr 1
      · rw [← Finset.prod_filter]
        simp
      · simpa [← Nat.support_factorization] using
          (Nat.prod_factorization_pow_eq_self hn0)
    _ ≤ (k ^ k) ^ (2 ^ k) * n := by
      apply Nat.mul_le_mul_right
      exact Nat.pow_le_pow_right (by positivity)
        (card_small_primeFactors_le_two_pow n k)
    _ = divisorSubpowerConst k ^ k * n := by
      simp only [divisorSubpowerConst, ← pow_mul, Nat.mul_comm k (2 ^ k)]

/-- Take the real `k`-th root once, after the finite prime-factor product has
been closed in `ℕ`.  This version includes `n = 0`. -/
theorem card_divisors_le_divisorSubpowerConst_mul_rpow
    (n k : ℕ) (hk : 1 ≤ k) :
    (n.divisors.card : ℝ) ≤
      (divisorSubpowerConst k : ℝ) *
        (n : ℝ) ^ ((k : ℝ)⁻¹) := by
  by_cases hn0 : n = 0
  · subst n
    simp [Nat.divisors]
    positivity
  · have hn : 0 < n := Nat.pos_of_ne_zero hn0
    have hnat :=
      card_divisors_pow_le_divisorSubpowerConst_pow_mul n k hn hk
    have hreal :
        (n.divisors.card : ℝ) ^ k ≤
          (divisorSubpowerConst k : ℝ) ^ k * (n : ℝ) := by
      exact_mod_cast hnat
    have hk0 : k ≠ 0 := by omega
    have hroot := Real.rpow_le_rpow (by positivity) hreal (by positivity :
      0 ≤ ((k : ℝ)⁻¹))
    calc
      (n.divisors.card : ℝ) =
          ((n.divisors.card : ℝ) ^ k) ^ ((k : ℝ)⁻¹) := by
        symm
        exact Real.pow_rpow_inv_natCast (by positivity) hk0
      _ ≤
          (((divisorSubpowerConst k : ℝ) ^ k) * (n : ℝ)) ^
            ((k : ℝ)⁻¹) := hroot
      _ =
          (divisorSubpowerConst k : ℝ) *
            (n : ℝ) ^ ((k : ℝ)⁻¹) := by
        rw [Real.mul_rpow (by positivity) (by positivity)]
        rw [Real.pow_rpow_inv_natCast (by positivity) hk0]

/-- The support coefficient inherits the fixed-power divisor theorem. -/
theorem supportCoeff_pow_le_divisorSubpowerConst_pow_mul
    (A : Set ℕ) (n k : ℕ) (hn : 0 < n) (hk : 1 ≤ k) :
    supportCoeff A n ^ k ≤ divisorSubpowerConst k ^ k * n := by
  calc
    supportCoeff A n ^ k ≤ n.divisors.card ^ k :=
      Nat.pow_le_pow_left (supportCoeff_le_card_divisors A n) k
    _ ≤ divisorSubpowerConst k ^ k * n :=
      card_divisors_pow_le_divisorSubpowerConst_pow_mul n k hn hk

/-- Real subpower form inherited by `supportCoeff`. -/
theorem supportCoeff_le_divisorSubpowerConst_mul_rpow
    (A : Set ℕ) (n k : ℕ) (hk : 1 ≤ k) :
    (supportCoeff A n : ℝ) ≤
      (divisorSubpowerConst k : ℝ) *
        (n : ℝ) ^ ((k : ℝ)⁻¹) := by
  calc
    (supportCoeff A n : ℝ) ≤ (n.divisors.card : ℝ) := by
      exact_mod_cast supportCoeff_le_card_divisors A n
    _ ≤
        (divisorSubpowerConst k : ℝ) *
          (n : ℝ) ^ ((k : ℝ)⁻¹) :=
      card_divisors_le_divisorSubpowerConst_mul_rpow n k hk

/-- `supportCoeff A` vanishes on the `h` positive indices immediately after
`N`, namely `N + 1, ..., N + h`. -/
def SupportCoeffZeroWindow (A : Set ℕ) (N h : ℕ) : Prop :=
  CoeffZeroWindow (supportCoeff A) N h

/-- A shifted natural tail state doubles exactly across a support-coefficient
zero window.  This is the recurrence-only core of T11; it uses no analytic
growth estimate. -/
theorem shiftedTailState_eq_pow_mul_of_supportCoeffZeroWindow
    (A : Set ℕ) (c v N h : ℕ) (u : ℕ → ℕ)
    (hrec : ∀ n : ℕ,
      u (n + 1) + v * supportCoeff A (c + n + 1) = 2 * u n)
    (hzero : SupportCoeffZeroWindow A (c + N) h) :
    u (N + h) = 2 ^ h * u N := by
  exact state_eq_pow_mul_of_coeffZeroWindow
    (supportCoeff A) c v N h u hrec hzero

/-- Positivity upgrades exact doubling to the natural-number lower bound
`2^h ≤ u(N+h)`. -/
theorem pow_le_shiftedTailState_of_supportCoeffZeroWindow
    (A : Set ℕ) (c v N h : ℕ) (u : ℕ → ℕ)
    (hpos : ∀ n : ℕ, 0 < u n)
    (hrec : ∀ n : ℕ,
      u (n + 1) + v * supportCoeff A (c + n + 1) = 2 * u n)
    (hzero : SupportCoeffZeroWindow A (c + N) h) :
    2 ^ h ≤ u (N + h) := by
  rw [state_eq_pow_mul_of_coeffZeroWindow
    (supportCoeff A) c v N h u hrec hzero]
  exact Nat.le_mul_of_pos_right (2 ^ h) (hpos N)

/-- Fraction-facing algebraic T11 boundary.  For a displayed denominator
`2^c * v`, every zero window forces the odd tail state, hence the scaled true
tail, to be at least `2^h`. -/
theorem pow_le_mul_binaryCoeffTail_of_support_fraction_zeroWindow
    (A : Set ℕ) (hA : ∃ a : ℕ, 0 < a ∧ a ∈ A)
    (p : ℤ) (c v N h : ℕ) (hv : 0 < v)
    (hvalue : erdosSupportSeries 2 A =
      (p : ℝ) / ((2 ^ c * v : ℕ) : ℝ))
    (hzero : SupportCoeffZeroWindow A (c + N) h) :
    (2 : ℝ) ^ h ≤
      (v : ℝ) * binaryCoeffTail (supportCoeff A) (c + N + h) := by
  obtain ⟨u, htail, hpos, hrec, _⟩ :=
    exists_shifted_odd_tail_nat_states_of_support_fraction
      A hA p c v hv hvalue
  change BinaryTailWindowLowerBound
    (supportCoeff A) (v : ℝ) (c + N) h
  exact binaryTailWindowLowerBound_of_natState
    (supportCoeff A) c v N h u (hpos N) hrec htail hzero

/-- An explicit upper envelope for the scaled support-coefficient tail. -/
def SupportCoeffTailEnvelope (A : Set ℕ) (envelope : ℕ → ℝ) : Prop :=
  BinaryCoeffTailEnvelope (supportCoeff A) envelope

/-- Package a pointwise divisor-card bound into the exact tail-envelope
interface consumed by the rational carry theorem below. -/
theorem supportCoeffTailEnvelope_two_mul_rpow_of_card_divisors_bound
    (A : Set ℕ) (C δ : ℝ)
    (hδ0 : 0 ≤ δ) (hδ1 : δ ≤ 1)
    (hdiv : ∀ n : ℕ, (n.divisors.card : ℝ) ≤ C * (n : ℝ) ^ δ) :
    SupportCoeffTailEnvelope A
      (fun M : ℕ => 2 * C * (((M + 1 : ℕ) : ℝ) ^ δ)) := by
  change BinaryCoeffTailEnvelope (supportCoeff A) _
  apply binaryCoeffTailEnvelope_two_mul_rpow (supportCoeff A) C δ hδ0 hδ1
  intro n
  have hcoeff : (supportCoeff A n : ℝ) ≤ (n.divisors.card : ℝ) := by
    exact_mod_cast supportCoeff_le_card_divisors A n
  exact hcoeff.trans (hdiv n)

/-- Unconditional support-tail envelope with exponent exactly `1/k`. -/
theorem supportCoeffTailEnvelope_divisorSubpower
    (A : Set ℕ) (k : ℕ) (hk : 1 ≤ k) :
    SupportCoeffTailEnvelope A
      (fun M : ℕ =>
        2 * (divisorSubpowerConst k : ℝ) *
          (((M + 1 : ℕ) : ℝ) ^ ((k : ℝ)⁻¹))) := by
  apply supportCoeffTailEnvelope_two_mul_rpow_of_card_divisors_bound
  · positivity
  · apply (inv_le_one₀ (by positivity : (0 : ℝ) < k)).2
    exact_mod_cast hk
  · intro n
    exact card_divisors_le_divisorSubpowerConst_mul_rpow n k hk

/-- Consumer-shaped conditional T11 theorem.  Once a subpower tail envelope
is supplied, a zero window is bounded by that envelope at its right endpoint.
No divisor-growth implementation detail leaks into the rational-support
argument. -/
theorem pow_le_mul_tailEnvelope_of_support_fraction_zeroWindow
    (A : Set ℕ) (hA : ∃ a : ℕ, 0 < a ∧ a ∈ A)
    (p : ℤ) (c v N h : ℕ) (hv : 0 < v)
    (hvalue : erdosSupportSeries 2 A =
      (p : ℝ) / ((2 ^ c * v : ℕ) : ℝ))
    (hzero : SupportCoeffZeroWindow A (c + N) h)
    (envelope : ℕ → ℝ) (henvelope : SupportCoeffTailEnvelope A envelope) :
    (2 : ℝ) ^ h ≤ (v : ℝ) * envelope (c + N + h) := by
  apply binaryTailWindowLowerBound_le_mul_envelope
  · exact pow_le_mul_binaryCoeffTail_of_support_fraction_zeroWindow
      A hA p c v N h hv hvalue hzero
  · exact Nat.cast_nonneg v
  · exact henvelope

/-- Direct consumer bridge from any pointwise divisor subpower bound to a
zero-window power inequality. -/
theorem pow_le_mul_two_mul_rpow_of_card_divisors_bound_zeroWindow
    (A : Set ℕ) (hA : ∃ a : ℕ, 0 < a ∧ a ∈ A)
    (p : ℤ) (c v N h : ℕ) (hv : 0 < v)
    (hvalue : erdosSupportSeries 2 A =
      (p : ℝ) / ((2 ^ c * v : ℕ) : ℝ))
    (hzero : SupportCoeffZeroWindow A (c + N) h)
    (C δ : ℝ) (hδ0 : 0 ≤ δ) (hδ1 : δ ≤ 1)
    (hdiv : ∀ n : ℕ, (n.divisors.card : ℝ) ≤ C * (n : ℝ) ^ δ) :
    (2 : ℝ) ^ h ≤
      (v : ℝ) * (2 * C * ((((c + N + h) + 1 : ℕ) : ℝ) ^ δ)) := by
  exact pow_le_mul_tailEnvelope_of_support_fraction_zeroWindow
    A hA p c v N h hv hvalue hzero
    (fun M : ℕ => 2 * C * (((M + 1 : ℕ) : ℝ) ^ δ))
    (supportCoeffTailEnvelope_two_mul_rpow_of_card_divisors_bound
      A C δ hδ0 hδ1 hdiv)

/-- The unconditional divisor-subpower envelope composed with the verified
rational carry mechanism. -/
theorem pow_le_divisorSubpower_of_support_fraction_zeroWindow
    (A : Set ℕ) (hA : ∃ a : ℕ, 0 < a ∧ a ∈ A)
    (p : ℤ) (c v N h k : ℕ) (hv : 0 < v) (hk : 1 ≤ k)
    (hvalue : erdosSupportSeries 2 A =
      (p : ℝ) / ((2 ^ c * v : ℕ) : ℝ))
    (hzero : SupportCoeffZeroWindow A (c + N) h) :
    (2 : ℝ) ^ h ≤
      (2 * (v : ℝ) * (divisorSubpowerConst k : ℝ)) *
        (((c + N + 1 + h : ℕ) : ℝ) ^ ((k : ℝ)⁻¹)) := by
  have hraw := pow_le_mul_tailEnvelope_of_support_fraction_zeroWindow
    A hA p c v N h hv hvalue hzero
    (fun M : ℕ =>
      2 * (divisorSubpowerConst k : ℝ) *
        (((M + 1 : ℕ) : ℝ) ^ ((k : ℝ)⁻¹)))
    (supportCoeffTailEnvelope_divisorSubpower A k hk)
  calc
    (2 : ℝ) ^ h ≤
        (v : ℝ) *
          (2 * (divisorSubpowerConst k : ℝ) *
            (((c + N + h + 1 : ℕ) : ℝ) ^ ((k : ℝ)⁻¹))) := hraw
    _ = (2 * (v : ℝ) * (divisorSubpowerConst k : ℝ)) *
        (((c + N + 1 + h : ℕ) : ℝ) ^ ((k : ℝ)⁻¹)) := by
      rw [show c + N + h + 1 = c + N + 1 + h by omega]
      ring

/-! ## Unconditional T11 -/

/-- Parameterized fixed-`k` T11 theorem.  This is the load-bearing form from
which the every-`ε` statement follows. -/
theorem supportCoeffZeroWindow_length_le_logb_divisorSubpower
    (A : Set ℕ) (hA : ∃ a : ℕ, 0 < a ∧ a ∈ A)
    (p : ℤ) (c v N h k : ℕ) (hv : 0 < v) (hk : 2 ≤ k)
    (hvalue : erdosSupportSeries 2 A =
      (p : ℝ) / ((2 ^ c * v : ℕ) : ℝ))
    (hzero : SupportCoeffZeroWindow A (c + N) h) :
    (h : ℝ) ≤
      (Real.logb 2 (c + N + 1 : ℝ) +
        Real.logb 2
          ((2 * (v : ℝ) * (divisorSubpowerConst k : ℝ)) ^ k)) /
        ((k - 1 : ℕ) : ℝ) := by
  let L : ℝ := 2 * (v : ℝ) * (divisorSubpowerConst k : ℝ)
  have hk1 : 1 ≤ k := le_trans (by omega) hk
  have hL : 1 ≤ L := by
    dsimp [L]
    have hkpos : 0 < k := by omega
    have hpos : 0 < 2 * v * divisorSubpowerConst k := by
      dsimp [divisorSubpowerConst]
      positivity
    have hnat : 1 ≤ 2 * v * divisorSubpowerConst k := by omega
    exact_mod_cast hnat
  have hlower : BinaryTailWindowLowerBound
      (supportCoeff A) (v : ℝ) (c + N) h :=
    pow_le_mul_binaryCoeffTail_of_support_fraction_zeroWindow
      A hA p c v N h hv hvalue hzero
  have henvelope : BinaryCoeffTailEnvelope (supportCoeff A)
      (fun M : ℕ =>
        (2 * (divisorSubpowerConst k : ℝ)) *
          (((M + 1 : ℕ) : ℝ) ^ ((k : ℝ)⁻¹))) := by
    exact supportCoeffTailEnvelope_divisorSubpower A k hk1
  have hLC :
      1 ≤ (v : ℝ) * (2 * (divisorSubpowerConst k : ℝ)) := by
    simpa [L, mul_assoc, mul_left_comm, mul_comm] using hL
  have htransfer := length_le_logb_of_binaryTailWindowLowerBound
    (supportCoeff A) (v : ℝ) (2 * (divisorSubpowerConst k : ℝ))
    (c + N) h k hlower (Nat.cast_nonneg v) henvelope hk hLC
  simpa [L, mul_assoc, mul_left_comm, mul_comm] using htransfer

/-- **Unconditional T11.**  For every positive `ε`, a rational support-series
value forces every support-coefficient zero window to have length at most
`ε * log₂(N+1)` plus a constant depending only on `ε`, `v`, and `c`.

The bound is uniform in the support `A`, numerator `p`, starting index `N`,
and window length `h`. -/
theorem supportCoeffZeroWindow_length_le_eps_logb_add
    (A : Set ℕ) (hA : ∃ a : ℕ, 0 < a ∧ a ∈ A)
    (p : ℤ) (c v : ℕ) (hv : 0 < v)
    (hvalue : erdosSupportSeries 2 A =
      (p : ℝ) / ((2 ^ c * v : ℕ) : ℝ))
    (ε : ℝ) (hε : 0 < ε) :
    ∃ B : ℝ, 0 ≤ B ∧
      ∀ N h : ℕ,
        SupportCoeffZeroWindow A (c + N) h →
        (h : ℝ) ≤ ε * Real.logb 2 (N + 1 : ℝ) + B := by
  obtain ⟨k, hk, hinv⟩ := exists_nat_two_le_inv_sub_one_le hε
  let L : ℝ := 2 * (v : ℝ) * (divisorSubpowerConst k : ℝ)
  let D : ℝ := Real.logb 2 (L ^ k)
  let B : ℝ :=
    (Real.logb 2 (c + 1 : ℝ) + D) / ((k - 1 : ℕ) : ℝ)
  have hL : 1 ≤ L := by
    dsimp [L]
    have hkpos : 0 < k := by omega
    have hpos : 0 < 2 * v * divisorSubpowerConst k := by
      dsimp [divisorSubpowerConst]
      positivity
    have hnat : 1 ≤ 2 * v * divisorSubpowerConst k := by omega
    exact_mod_cast hnat
  have hD : 0 ≤ D := by
    dsimp [D]
    exact Real.logb_nonneg (by norm_num) (one_le_pow₀ hL)
  have hB : 0 ≤ B := by
    dsimp [B]
    apply div_nonneg
    · exact add_nonneg (Real.logb_nonneg (by norm_num) (by norm_num)) hD
    · positivity
  refine ⟨B, hB, ?_⟩
  intro N h hzero
  have hkbound := supportCoeffZeroWindow_length_le_logb_divisorSubpower
    A hA p c v N h k hv hk hvalue hzero
  have hfinal :=
    le_epsilon_mul_logb_add_constant_div_of_affine_log_bound
      (ε := ε) (D := D) (x := (h : ℝ))
      (c := c) (N := N) (k := k) hkbound hinv
  simpa [B, D, L] using hfinal

/-- Exact `ε * log₂ N + O(1)` form of unconditional T11 for every positive
starting index. -/
theorem supportCoeffZeroWindow_length_le_eps_logb
    (A : Set ℕ) (hA : ∃ a : ℕ, 0 < a ∧ a ∈ A)
    (p : ℤ) (c v : ℕ) (hv : 0 < v)
    (hvalue : erdosSupportSeries 2 A =
      (p : ℝ) / ((2 ^ c * v : ℕ) : ℝ))
    (ε : ℝ) (hε : 0 < ε) :
    ∃ B : ℝ, 0 ≤ B ∧
      ∀ N h : ℕ, 1 ≤ N →
        SupportCoeffZeroWindow A (c + N) h →
        (h : ℝ) ≤ ε * Real.logb 2 (N : ℝ) + B := by
  obtain ⟨B, hB, hbound⟩ :=
    supportCoeffZeroWindow_length_le_eps_logb_add
      A hA p c v hv hvalue ε hε
  refine ⟨B + ε, add_nonneg hB hε.le, ?_⟩
  intro N h hN hzero
  calc
    (h : ℝ) ≤ ε * Real.logb 2 (N + 1 : ℝ) + B := hbound N h hzero
    _ ≤ ε * (1 + Real.logb 2 (N : ℝ)) + B := by
      gcongr
      exact logb_nat_succ_le_one_add N hN
    _ = ε * Real.logb 2 (N : ℝ) + (B + ε) := by ring

#print axioms shiftedTailState_eq_pow_mul_of_supportCoeffZeroWindow
#print axioms pow_le_shiftedTailState_of_supportCoeffZeroWindow
#print axioms pow_le_mul_binaryCoeffTail_of_support_fraction_zeroWindow
#print axioms pow_le_mul_tailEnvelope_of_support_fraction_zeroWindow
#print axioms card_divisors_pow_le_divisorSubpowerConst_pow_mul
#print axioms card_divisors_le_divisorSubpowerConst_mul_rpow
#print axioms binaryCoeffTail_le_two_mul_rpow
#print axioms supportCoeffTailEnvelope_divisorSubpower
#print axioms length_le_logb_of_pow_le_mul_add_invNat_rpow
#print axioms supportCoeffZeroWindow_length_le_logb_divisorSubpower
#print axioms supportCoeffZeroWindow_length_le_eps_logb_add
#print axioms supportCoeffZeroWindow_length_le_eps_logb

end Erdos249257
