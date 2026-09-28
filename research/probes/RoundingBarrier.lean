-- SPDX-FileCopyrightText: 2026 Will Cook
-- SPDX-License-Identifier: Apache-2.0
import Erdos249257.TotientTailPeriodKiller
import ErdosProblems.Erdos251.BoundedPerturbationCountermodel
import ErdosProblems.Erdos249.PaperCompleteR20.FinitePrefixCountermodelEndpoint

/-!
# Rounding shadows and a barrier for binary irrationality demands

Let `c : ℕ → ℕ` be a coefficient sequence whose series `∑ c(n)/2^n` converges, and fix a
modulus `q ≥ 1` and a cutoff `M`.  Write `T_c(M) = ∑_{j≥1} c(M+j)/2^j` for the scaled tail
(`Erdos249257.binaryCoeffTail`).  Subtracting `q` times the binary digits of
`fract(T_c(M)/q)`, written after position `M`, gives a sequence `a = downShadow c q M` with

* `a(n) = c(n)` for `n ≤ M`;
* `c(n) - q ≤ a(n) ≤ c(n)` and `a(n) ≡ c(n) (mod q)` for every `n`;
* `∑ a(n)/2^n = (∑_{n≤M} c(n) 2^(M-n) + q⌊T_c(M)/q⌋) / 2^M`, a dyadic rational,

whenever `c(n) ≥ q` for every `n > M` (`hasSum_downShadow_dyadic`).  Adding the binary digits
of `fract(-T_c(M)/q)` instead needs no lower bound on `c` and gives `c(n) ≤ a(n) ≤ c(n) + q`
(`upShadow`, `hasSum_upShadow_dyadic`).  The digits are `ErdosProblems.Erdos251.binaryDigit`,
and the upward construction has the shape of the prime-gap perturbation
`ErdosProblems.Erdos251.exists_bounded_perturbation`, here with an exact dyadic value and the
indexing `∑ c(n)/2^n`.

A dyadic value leaves no room for a period certificate.  For a sequence with `c(n) ≤ n` the
corpus certificate `GenericTailCertificates.certificate` is sound, so a value `p/2^e` excludes
every certificate at every `N ≥ e`, every lag and every depth (`no_certificate_of_dyadic`), and
any rational value excludes the cofinal supply `FinitePrefixCountermodel.separation`
(`not_separation_of_rational`).  At `c = φ` the certificate is `certifiedKill` and the supply is
the hypothesis of `irrational_totient_series_of_certificate_supply` (`certificate_totient_iff`,
`separation_totient_iff`).

`no_route_of_rational_witness` is the barrier schema: a property set that holds for some
sequence with `c(n) ≤ n` and a rational binary value implies no demand that a sound engine
turns into irrationality of the binary series.  The instances are the base-two coefficient
series of the corpus.

* Erdős #249, `c = φ`: `totientShadow` has the parity of `φ`, lies within two of `φ`, satisfies
  `a(n) ≤ n`, has `∑ a(n)/2^n = 5/4` and has no certificate at any `N ≥ 2`.  For every modulus
  `q` the downward shadow with cutoff `(2q)^(2q)` keeps `φ` modulo `q` (`totient_rounding_barrier`).
* Erdős #251, `c(n) = p_n`: for every modulus `q`, a sequence congruent to the primes modulo `q`
  and within `q` below them has a dyadic binary value (`prime_rounding_barrier`).
* Erdős #257, `c = f_A`, the number of divisors of `n` lying in `A`: for every support `A` and
  modulus `q` the upward shadow with cutoff `2q + 1` keeps `f_A` modulo `q`, satisfies
  `a(n) ≤ n` and has a dyadic value (`support_rounding_barrier`).  The full support `A = ℕ`
  gives the divisor count, the base-two case of Erdős #1049 (`divisorCount_rounding_barrier`).

Multiplicativity separates `φ` from its shadow: a sequence multiplicative on coprime arguments
at bounded distance from `φ` equals `φ` (`eq_totient_of_multiplicative_of_bounded_sub`), so
`totientShadow` is not multiplicative (`totientShadow_not_multiplicative`).  The same rigidity
holds for the divisor count.

Nothing in this file decides the irrationality of any of these series.
-/

noncomputable section

/-! ## Multiplicative rigidity -/

namespace ErdosProblems.Synthesis.MultiplicativeRigidity

/-- **Bounded-perturbation rigidity.**  Let `a` and `f` be multiplicative on coprime arguments
with `|a(n) - f(n)| ≤ C` for every `n ≥ 1`.  If `f` is unbounded on the integers coprime to each
fixed `n ≥ 1`, then `a(n) = f(n)` for every `n ≥ 1`.  For `k` coprime to `n`,
`(a(n) - f(n)) f(k) = (a(nk) - f(nk)) - a(n) (a(k) - f(k))`, and the right side has absolute
value at most `C (1 + |a(n)|)` whatever `k` is. -/
theorem eq_of_multiplicative_of_bounded_sub {a f : ℕ → ℝ}
    (ha : ∀ m n, Nat.Coprime m n → a (m * n) = a m * a n)
    (hf : ∀ m n, Nat.Coprime m n → f (m * n) = f m * f n)
    {C : ℝ} (hC : ∀ n, 1 ≤ n → |a n - f n| ≤ C)
    (hunb : ∀ n, 1 ≤ n → ∀ B : ℝ, ∃ k, 1 ≤ k ∧ Nat.Coprime n k ∧ B < |f k|) :
    ∀ n, 1 ≤ n → a n = f n := by
  intro n hn
  by_contra hne
  have he : 0 < |a n - f n| := abs_pos.mpr (sub_ne_zero.mpr hne)
  obtain ⟨k, hk, hcop, hbig⟩ := hunb n hn (C * (1 + |a n|) / |a n - f n|)
  have hnk : 1 ≤ n * k := Nat.one_le_iff_ne_zero.mpr (Nat.mul_ne_zero (by omega) (by omega))
  have hid : (a n - f n) * f k = (a (n * k) - f (n * k)) - a n * (a k - f k) := by
    rw [ha n k hcop, hf n k hcop]
    ring
  have h1 := abs_le.mp (hC (n * k) hnk)
  have h2 : |a n * (a k - f k)| ≤ |a n| * C := by
    rw [abs_mul]
    exact mul_le_mul_of_nonneg_left (hC k hk) (abs_nonneg _)
  have h3 := abs_le.mp h2
  have hbound : |a n - f n| * |f k| ≤ C * (1 + |a n|) := by
    rw [← abs_mul, hid, abs_le]
    constructor <;> linarith [h1.1, h1.2, h3.1, h3.2]
  rw [div_lt_iff₀ he] at hbig
  linarith

/-- Euler's totient is unbounded on the integers coprime to any fixed `n ≥ 1`: a prime
`p ≥ n + 2 + ⌈B⌉` is coprime to `n` and has `φ(p) = p - 1 > B`. -/
theorem totient_unbounded_coprime (n : ℕ) (hn : 1 ≤ n) (B : ℝ) :
    ∃ k, 1 ≤ k ∧ Nat.Coprime n k ∧ B < |(Nat.totient k : ℝ)| := by
  obtain ⟨p, hp_ge, hp⟩ := Nat.exists_infinite_primes (n + 2 + ⌈B⌉₊)
  have hp1 : 1 ≤ p := hp.one_lt.le
  refine ⟨p, hp1, ?_, ?_⟩
  · refine Nat.Coprime.symm ((Nat.Prime.coprime_iff_not_dvd hp).mpr fun hdvd => ?_)
    have := Nat.le_of_dvd (by omega) hdvd
    omega
  · rw [Nat.totient_prime hp, Nat.cast_sub hp1, Nat.cast_one]
    have hceil := Nat.le_ceil B
    have hpR : ((n + 2 + ⌈B⌉₊ : ℕ) : ℝ) ≤ p := by exact_mod_cast hp_ge
    push_cast at hpR
    have hn0 : (0 : ℝ) ≤ n := Nat.cast_nonneg n
    have hc0 : (0 : ℝ) ≤ (⌈B⌉₊ : ℝ) := Nat.cast_nonneg _
    have hpos : (0 : ℝ) ≤ (p : ℝ) - 1 := by linarith
    rw [abs_of_nonneg hpos]
    linarith

/-- **Rigidity at the totient.**  A real sequence that is multiplicative on coprime arguments and
lies within a fixed distance of `φ` at every `n ≥ 1` equals `φ` at every `n ≥ 1`. -/
theorem eq_totient_of_multiplicative_of_bounded_sub {a : ℕ → ℝ}
    (ha : ∀ m n, Nat.Coprime m n → a (m * n) = a m * a n)
    {C : ℝ} (hC : ∀ n, 1 ≤ n → |a n - Nat.totient n| ≤ C) :
    ∀ n, 1 ≤ n → a n = Nat.totient n :=
  eq_of_multiplicative_of_bounded_sub (f := fun n => (Nat.totient n : ℝ)) ha
    (fun m n hmn => by
      show ((Nat.totient (m * n) : ℕ) : ℝ) = (Nat.totient m : ℝ) * (Nat.totient n : ℝ)
      rw [Nat.totient_mul hmn, Nat.cast_mul])
    hC totient_unbounded_coprime

/-- The divisor count is unbounded on the integers coprime to any fixed `n ≥ 1`: for a prime
`p > n` the power `p^j` has `j + 1` divisors. -/
theorem card_divisors_unbounded_coprime (n : ℕ) (hn : 1 ≤ n) (B : ℝ) :
    ∃ k, 1 ≤ k ∧ Nat.Coprime n k ∧ B < |((Nat.divisors k).card : ℝ)| := by
  obtain ⟨p, hp_ge, hp⟩ := Nat.exists_infinite_primes (n + 1)
  refine ⟨p ^ ⌈B⌉₊, Nat.one_le_pow _ _ hp.pos, ?_, ?_⟩
  · refine Nat.Coprime.pow_right _
      (Nat.Coprime.symm ((Nat.Prime.coprime_iff_not_dvd hp).mpr fun hdvd => ?_))
    have := Nat.le_of_dvd (by omega) hdvd
    omega
  · rw [← ArithmeticFunction.sigma_zero_apply, ArithmeticFunction.sigma_zero_apply_prime_pow hp,
      abs_of_nonneg (Nat.cast_nonneg _)]
    push_cast
    linarith [Nat.le_ceil B]

/-- **Rigidity at the divisor count.**  A real sequence that is multiplicative on coprime
arguments and lies within a fixed distance of `τ(n) = #divisors(n)` at every `n ≥ 1` equals `τ`
at every `n ≥ 1`. -/
theorem eq_card_divisors_of_multiplicative_of_bounded_sub {a : ℕ → ℝ}
    (ha : ∀ m n, Nat.Coprime m n → a (m * n) = a m * a n)
    {C : ℝ} (hC : ∀ n, 1 ≤ n → |a n - (Nat.divisors n).card| ≤ C) :
    ∀ n, 1 ≤ n → a n = (Nat.divisors n).card :=
  eq_of_multiplicative_of_bounded_sub (f := fun n => ((Nat.divisors n).card : ℝ)) ha
    (fun m n hmn => by
      show (((m * n).divisors.card : ℕ) : ℝ) =
        ((m.divisors.card : ℕ) : ℝ) * ((n.divisors.card : ℕ) : ℝ)
      rw [Nat.Coprime.card_divisors_mul hmn, Nat.cast_mul])
    hC card_divisors_unbounded_coprime

end ErdosProblems.Synthesis.MultiplicativeRigidity

/-! ## The generic rounding construction -/

namespace ErdosProblems.Synthesis.RoundingBarrier

open Erdos249257 ErdosProblems.Erdos249.PaperCompleteR20

/-! ### Binary digits written after a cutoff -/

/-- The binary digits of `D` written after position `M`: position `M + 1 + k` carries the
`(k + 1)`-st binary digit `ErdosProblems.Erdos251.binaryDigit D k`, and every position `n ≤ M`
carries `0`. -/
def placedDigit (D : ℝ) (M n : ℕ) : ℕ :=
  if M < n then (ErdosProblems.Erdos251.binaryDigit D (n - (M + 1))).toNat else 0

theorem placedDigit_le_one (D : ℝ) (M n : ℕ) : placedDigit D M n ≤ 1 := by
  unfold placedDigit
  split
  · have h1 := ErdosProblems.Erdos251.binaryDigit_le_one D (n - (M + 1))
    have h0 := ErdosProblems.Erdos251.binaryDigit_nonneg D (n - (M + 1))
    omega
  · omega

theorem placedDigit_of_le {D : ℝ} {M n : ℕ} (hn : n ≤ M) : placedDigit D M n = 0 := by
  unfold placedDigit
  rw [if_neg (Nat.not_lt.mpr hn)]

theorem placedDigit_add_cast (D : ℝ) (M k : ℕ) :
    (placedDigit D M (k + (M + 1)) : ℝ) = (ErdosProblems.Erdos251.binaryDigit D k : ℝ) := by
  unfold placedDigit
  rw [if_pos (show M < k + (M + 1) by omega), Nat.add_sub_cancel]
  exact_mod_cast Int.toNat_of_nonneg (ErdosProblems.Erdos251.binaryDigit_nonneg D k)

/-- For `0 ≤ D < 1` the digits written after `M` sum to `D / 2^M`. -/
theorem hasSum_placedDigit {D : ℝ} (h0 : 0 ≤ D) (h1 : D < 1) (M : ℕ) :
    HasSum (fun n => (placedDigit D M n : ℝ) / 2 ^ n) (D / 2 ^ M) := by
  have hbase := (ErdosProblems.Erdos251.hasSum_binaryDigit D h0 h1).mul_right (1 / 2 ^ M)
  have hfun : (fun k => (placedDigit D M (k + (M + 1)) : ℝ) / 2 ^ (k + (M + 1))) =
      fun k => (ErdosProblems.Erdos251.binaryDigit D k : ℝ) / 2 ^ (k + 1) * (1 / 2 ^ M) := by
    funext k
    rw [placedDigit_add_cast, div_mul_div_comm, mul_one, ← pow_add,
      show k + 1 + M = k + (M + 1) by omega]
  have hshift : HasSum (fun k => (placedDigit D M (k + (M + 1)) : ℝ) / 2 ^ (k + (M + 1)))
      (D / 2 ^ M) := by
    rw [hfun, show D / 2 ^ M = D * (1 / 2 ^ M) by ring]
    exact hbase
  have hzero : ∑ i ∈ Finset.range (M + 1), (placedDigit D M i : ℝ) / 2 ^ i = 0 :=
    Finset.sum_eq_zero fun i hi => by
      rw [placedDigit_of_le (Nat.lt_succ_iff.mp (Finset.mem_range.mp hi))]
      simp
  refine (hasSum_nat_add_iff' (M + 1)).mp ?_
  rw [hzero, sub_zero]
  exact hshift

/-! ### Prefix and scaled tail -/

/-- `∑ c(n)/2^n = ∑_{n ≤ M} c(n)/2^n + T_c(M)/2^M`, with `T_c(M) = binaryCoeffTail c M`. -/
theorem tsum_eq_prefix_add_tail (c : ℕ → ℕ) (hsum : Summable (fun n => (c n : ℝ) / 2 ^ n))
    (M : ℕ) :
    ∑' n, (c n : ℝ) / 2 ^ n =
      (∑ n ∈ Finset.range (M + 1), (c n : ℝ) / 2 ^ n) + binaryCoeffTail c M / 2 ^ M := by
  rw [← hsum.sum_add_tsum_nat_add (M + 1)]
  congr 1
  unfold binaryCoeffTail
  rw [← tsum_div_const]
  refine tsum_congr fun j => ?_
  show (c (j + (M + 1)) : ℝ) / 2 ^ (j + (M + 1)) = (c (M + j + 1) : ℝ) / 2 ^ (j + 1) / 2 ^ M
  rw [show j + (M + 1) = M + j + 1 by omega, div_div, ← pow_add,
    show j + 1 + M = M + j + 1 by omega]

/-- The prefix `∑_{n ≤ M} c(n)/2^n` has denominator dividing `2^M`. -/
theorem prefix_sum_div_eq (c : ℕ → ℕ) (M : ℕ) :
    ∑ n ∈ Finset.range (M + 1), (c n : ℝ) / 2 ^ n =
      (∑ n ∈ Finset.range (M + 1), (c n : ℝ) * 2 ^ (M - n)) / 2 ^ M := by
  rw [Finset.sum_div]
  refine Finset.sum_congr rfl fun n hn => ?_
  have hnM : n ≤ M := Nat.lt_succ_iff.mp (Finset.mem_range.mp hn)
  have hpow : (2 : ℝ) ^ M = 2 ^ n * 2 ^ (M - n) := by
    rw [← pow_add, Nat.add_sub_cancel' hnM]
  rw [hpow, mul_div_mul_right _ _ (by positivity : (2 : ℝ) ^ (M - n) ≠ 0)]

/-! ### Downward rounding -/

/-- The downward rounding fraction `fract(T_c(M) / q) ∈ [0, 1)`. -/
def downFraction (c : ℕ → ℕ) (q M : ℕ) : ℝ := Int.fract (binaryCoeffTail c M / (q : ℝ))

/-- **Downward rounding shadow.**  `c(n)` minus `q` times the binary digits of
`downFraction c q M` written after position `M`. -/
def downShadow (c : ℕ → ℕ) (q M n : ℕ) : ℕ :=
  c n - q * placedDigit (downFraction c q M) M n

/-- The integer numerator of the downward shadow's binary value over `2^M`. -/
def downNumerator (c : ℕ → ℕ) (q M : ℕ) : ℤ :=
  (∑ n ∈ Finset.range (M + 1), (c n : ℤ) * 2 ^ (M - n)) +
    (q : ℤ) * ⌊binaryCoeffTail c M / (q : ℝ)⌋

theorem downShadow_of_le (c : ℕ → ℕ) (q : ℕ) {M n : ℕ} (hn : n ≤ M) :
    downShadow c q M n = c n := by
  unfold downShadow
  rw [placedDigit_of_le hn, mul_zero, Nat.sub_zero]

theorem downShadow_le (c : ℕ → ℕ) (q M n : ℕ) : downShadow c q M n ≤ c n := Nat.sub_le _ _

theorem downShadow_add {c : ℕ → ℕ} {q M : ℕ} (hbig : ∀ n, M < n → q ≤ c n) (n : ℕ) :
    downShadow c q M n + q * placedDigit (downFraction c q M) M n = c n := by
  unfold downShadow
  rcases Nat.lt_or_ge M n with hMn | hnM
  · have hq := hbig n hMn
    have hd := placedDigit_le_one (downFraction c q M) M n
    have hle : q * placedDigit (downFraction c q M) M n ≤ c n :=
      calc q * placedDigit (downFraction c q M) M n ≤ q * 1 := Nat.mul_le_mul_left _ hd
        _ = q := mul_one q
        _ ≤ c n := hq
    omega
  · rw [placedDigit_of_le hnM, mul_zero, Nat.sub_zero, Nat.add_zero]

theorem le_downShadow_add {c : ℕ → ℕ} {q M : ℕ} (hbig : ∀ n, M < n → q ≤ c n) (n : ℕ) :
    c n ≤ downShadow c q M n + q := by
  have h := downShadow_add hbig n
  have hd := placedDigit_le_one (downFraction c q M) M n
  have hle : q * placedDigit (downFraction c q M) M n ≤ q :=
    calc q * placedDigit (downFraction c q M) M n ≤ q * 1 := Nat.mul_le_mul_left _ hd
      _ = q := mul_one q
  omega

theorem downShadow_modEq {c : ℕ → ℕ} {q M : ℕ} (hbig : ∀ n, M < n → q ≤ c n) (n : ℕ) :
    downShadow c q M n ≡ c n [MOD q] := by
  show downShadow c q M n % q = c n % q
  conv_rhs => rw [← downShadow_add hbig n]
  rw [Nat.add_mul_mod_self_left]

/-- **Downward rounding value.**  If `c(n) ≥ q` for every `n > M`, the downward shadow has
binary value `∑_{n ≤ M} c(n)/2^n + q ⌊T_c(M)/q⌋ / 2^M`. -/
theorem hasSum_downShadow (c : ℕ → ℕ) {q : ℕ} (hq : 0 < q) (M : ℕ)
    (hsum : Summable (fun n => (c n : ℝ) / 2 ^ n)) (hbig : ∀ n, M < n → q ≤ c n) :
    HasSum (fun n => (downShadow c q M n : ℝ) / 2 ^ n)
      ((∑ n ∈ Finset.range (M + 1), (c n : ℝ) / 2 ^ n) +
        (q : ℝ) * ((⌊binaryCoeffTail c M / (q : ℝ)⌋ : ℤ) : ℝ) / 2 ^ M) := by
  have hqR : (q : ℝ) ≠ 0 := by exact_mod_cast hq.ne'
  have hdig := (hasSum_placedDigit (D := downFraction c q M) (Int.fract_nonneg _)
    (Int.fract_lt_one _) M).mul_left (q : ℝ)
  have hsub := hsum.hasSum.sub hdig
  have hfun : (fun n => (downShadow c q M n : ℝ) / 2 ^ n) = fun n =>
      (c n : ℝ) / 2 ^ n - (q : ℝ) * ((placedDigit (downFraction c q M) M n : ℝ) / 2 ^ n) := by
    funext n
    have hR : (downShadow c q M n : ℝ) + (q : ℝ) * (placedDigit (downFraction c q M) M n : ℝ) =
        (c n : ℝ) := by
      exact_mod_cast downShadow_add hbig n
    rw [← hR]
    ring
  rw [hfun]
  convert hsub using 1
  rw [tsum_eq_prefix_add_tail c hsum M, downFraction, ← Int.self_sub_floor]
  have hT : (q : ℝ) * (binaryCoeffTail c M / (q : ℝ)) = binaryCoeffTail c M := by
    rw [mul_div_assoc', mul_div_cancel_left₀ _ hqR]
  rw [mul_div_assoc', mul_sub, hT]
  ring

/-- **Downward rounding, dyadic form.**  If `c(n) ≥ q` for every `n > M`, the downward shadow
has binary value `downNumerator c q M / 2^M`. -/
theorem hasSum_downShadow_dyadic (c : ℕ → ℕ) {q : ℕ} (hq : 0 < q) (M : ℕ)
    (hsum : Summable (fun n => (c n : ℝ) / 2 ^ n)) (hbig : ∀ n, M < n → q ≤ c n) :
    HasSum (fun n => (downShadow c q M n : ℝ) / 2 ^ n) ((downNumerator c q M : ℝ) / 2 ^ M) := by
  convert hasSum_downShadow c hq M hsum hbig using 1
  rw [prefix_sum_div_eq, downNumerator]
  push_cast
  ring

/-- **Generic rounding theorem (downward).**  Every coefficient sequence with a convergent binary
series and `c(n) ≥ q` beyond a cutoff `M` has a shadow that agrees with it up to `M`, lies
between `c - q` and `c`, is congruent to it modulo `q`, and has a dyadic binary value. -/
theorem exists_downShadow (c : ℕ → ℕ) {q : ℕ} (hq : 0 < q) (M : ℕ)
    (hsum : Summable (fun n => (c n : ℝ) / 2 ^ n)) (hbig : ∀ n, M < n → q ≤ c n) :
    ∃ a : ℕ → ℕ, (∀ n, a n ≡ c n [MOD q]) ∧ (∀ n, a n ≤ c n ∧ c n ≤ a n + q) ∧
      (∀ n, n ≤ M → a n = c n) ∧
      ∃ p : ℤ, HasSum (fun n => (a n : ℝ) / 2 ^ n) ((p : ℝ) / 2 ^ M) :=
  ⟨downShadow c q M, downShadow_modEq hbig,
    fun n => ⟨downShadow_le c q M n, le_downShadow_add hbig n⟩,
    fun _ hn => downShadow_of_le c q hn, downNumerator c q M,
    hasSum_downShadow_dyadic c hq M hsum hbig⟩

/-! ### Upward rounding -/

/-- The upward rounding fraction `fract(-T_c(M) / q) ∈ [0, 1)`. -/
def upFraction (c : ℕ → ℕ) (q M : ℕ) : ℝ := Int.fract (-(binaryCoeffTail c M / (q : ℝ)))

/-- **Upward rounding shadow.**  `c(n)` plus `q` times the binary digits of `upFraction c q M`
written after position `M`. -/
def upShadow (c : ℕ → ℕ) (q M n : ℕ) : ℕ :=
  c n + q * placedDigit (upFraction c q M) M n

/-- The integer numerator of the upward shadow's binary value over `2^M`. -/
def upNumerator (c : ℕ → ℕ) (q M : ℕ) : ℤ :=
  (∑ n ∈ Finset.range (M + 1), (c n : ℤ) * 2 ^ (M - n)) -
    (q : ℤ) * ⌊-(binaryCoeffTail c M / (q : ℝ))⌋

theorem upShadow_of_le (c : ℕ → ℕ) (q : ℕ) {M n : ℕ} (hn : n ≤ M) :
    upShadow c q M n = c n := by
  unfold upShadow
  rw [placedDigit_of_le hn, mul_zero, Nat.add_zero]

theorem le_upShadow (c : ℕ → ℕ) (q M n : ℕ) : c n ≤ upShadow c q M n := Nat.le_add_right _ _

theorem upShadow_le_add (c : ℕ → ℕ) (q M n : ℕ) : upShadow c q M n ≤ c n + q := by
  unfold upShadow
  have hd := placedDigit_le_one (upFraction c q M) M n
  have hle : q * placedDigit (upFraction c q M) M n ≤ q :=
    calc q * placedDigit (upFraction c q M) M n ≤ q * 1 := Nat.mul_le_mul_left _ hd
      _ = q := mul_one q
  omega

theorem upShadow_modEq (c : ℕ → ℕ) (q M n : ℕ) : upShadow c q M n ≡ c n [MOD q] := by
  show (c n + q * placedDigit (upFraction c q M) M n) % q = c n % q
  rw [Nat.add_mul_mod_self_left]

/-- **Upward rounding value.**  The upward shadow has binary value
`∑_{n ≤ M} c(n)/2^n - q ⌊-T_c(M)/q⌋ / 2^M`; no lower bound on `c` is needed. -/
theorem hasSum_upShadow (c : ℕ → ℕ) {q : ℕ} (hq : 0 < q) (M : ℕ)
    (hsum : Summable (fun n => (c n : ℝ) / 2 ^ n)) :
    HasSum (fun n => (upShadow c q M n : ℝ) / 2 ^ n)
      ((∑ n ∈ Finset.range (M + 1), (c n : ℝ) / 2 ^ n) -
        (q : ℝ) * ((⌊-(binaryCoeffTail c M / (q : ℝ))⌋ : ℤ) : ℝ) / 2 ^ M) := by
  have hqR : (q : ℝ) ≠ 0 := by exact_mod_cast hq.ne'
  have hdig := (hasSum_placedDigit (D := upFraction c q M) (Int.fract_nonneg _)
    (Int.fract_lt_one _) M).mul_left (q : ℝ)
  have hadd := hsum.hasSum.add hdig
  have hfun : (fun n => (upShadow c q M n : ℝ) / 2 ^ n) = fun n =>
      (c n : ℝ) / 2 ^ n + (q : ℝ) * ((placedDigit (upFraction c q M) M n : ℝ) / 2 ^ n) := by
    funext n
    unfold upShadow
    push_cast
    ring
  rw [hfun]
  convert hadd using 1
  rw [tsum_eq_prefix_add_tail c hsum M, upFraction, ← Int.self_sub_floor]
  have hT : (q : ℝ) * (-(binaryCoeffTail c M / (q : ℝ))) = -binaryCoeffTail c M := by
    rw [mul_neg, mul_div_assoc', mul_div_cancel_left₀ _ hqR]
  rw [mul_div_assoc', mul_sub, hT]
  ring

/-- **Upward rounding, dyadic form.** -/
theorem hasSum_upShadow_dyadic (c : ℕ → ℕ) {q : ℕ} (hq : 0 < q) (M : ℕ)
    (hsum : Summable (fun n => (c n : ℝ) / 2 ^ n)) :
    HasSum (fun n => (upShadow c q M n : ℝ) / 2 ^ n) ((upNumerator c q M : ℝ) / 2 ^ M) := by
  convert hasSum_upShadow c hq M hsum using 1
  rw [prefix_sum_div_eq, upNumerator]
  push_cast
  ring

/-- **Generic rounding theorem (upward).**  Every coefficient sequence with a convergent binary
series has, for every modulus `q ≥ 1` and cutoff `M`, a shadow that agrees with it up to `M`,
lies between `c` and `c + q`, is congruent to it modulo `q`, and has a dyadic binary value. -/
theorem exists_upShadow (c : ℕ → ℕ) {q : ℕ} (hq : 0 < q) (M : ℕ)
    (hsum : Summable (fun n => (c n : ℝ) / 2 ^ n)) :
    ∃ a : ℕ → ℕ, (∀ n, a n ≡ c n [MOD q]) ∧ (∀ n, c n ≤ a n ∧ a n ≤ c n + q) ∧
      (∀ n, n ≤ M → a n = c n) ∧
      ∃ p : ℤ, HasSum (fun n => (a n : ℝ) / 2 ^ n) ((p : ℝ) / 2 ^ M) :=
  ⟨upShadow c q M, upShadow_modEq c q M,
    fun n => ⟨le_upShadow c q M n, upShadow_le_add c q M n⟩,
    fun _ hn => upShadow_of_le c q hn, upNumerator c q M, hasSum_upShadow_dyadic c hq M hsum⟩

/-! ## Certificates for a rational binary value -/

theorem summable_of_le_self (c : ℕ → ℕ) (hc : ∀ n, c n ≤ n) :
    Summable (fun n => (c n : ℝ) / 2 ^ n) := by
  have hs : Summable (fun n : ℕ => (n : ℝ) * (1 / 2 : ℝ) ^ n) := by
    simpa using summable_pow_mul_geometric_of_norm_lt_one 1 (r := (1 / 2 : ℝ)) (by norm_num)
  refine Summable.of_nonneg_of_le (fun n => by positivity) (fun n => ?_) hs
  rw [div_pow, one_pow, mul_one_div]
  exact div_le_div_of_nonneg_right (by exact_mod_cast hc n) (by positivity)

/-- With `c(0) = 0` the series `∑_{n ≥ 0} c(n)/2^n` is the corpus series `binaryCoeffSeries c`. -/
theorem tsum_eq_binaryCoeffSeries (c : ℕ → ℕ) (hc0 : c 0 = 0)
    (hsum : Summable (fun n => (c n : ℝ) / 2 ^ n)) :
    ∑' n, (c n : ℝ) / 2 ^ n = binaryCoeffSeries c := by
  rw [hsum.tsum_eq_zero_add]
  simp [binaryCoeffSeries, hc0]

theorem not_irrational_int_div_two_pow (p : ℤ) (e : ℕ) : ¬ Irrational ((p : ℝ) / 2 ^ e) := by
  have h := Rat.not_irrational ((p : ℚ) / 2 ^ e)
  push_cast at h
  exact h

/-- **A dyadic value has no certificate.**  If `c(n) ≤ n` and `∑ c(n)/2^n = p/2^e`, then no
certificate `GenericTailCertificates.certificate c h N L` holds at any `N ≥ e`, any lag `h` and
any depth `L`: every tail difference is an integer there, and certificates are sound. -/
theorem no_certificate_of_dyadic (c : ℕ → ℕ) (hc : ∀ n, c n ≤ n) (p : ℤ) (e : ℕ)
    (hS : binaryCoeffSeries c = (p : ℝ) / 2 ^ e) :
    ∀ N, e ≤ N → ∀ h L, ¬ GenericTailCertificates.certificate c h N L := by
  intro N hN h L hcert
  have hS' : binaryCoeffSeries c = (p : ℝ) / ((2 : ℝ) ^ e * ((1 : ℕ) : ℝ)) := by
    rw [hS, Nat.cast_one, mul_one]
  exact GenericTailCertificates.certificate_sound c hc h N L hcert
    (GenericTailCertificates.generic_tail_period c hc p e 1 h N Nat.one_pos hN (one_dvd _) hS')

/-- A rational binary value makes some positive lag eventually integral: take the odd part `m`
of the denominator and the lag `φ(m)`. -/
theorem exists_integral_tail_period_of_rational (c : ℕ → ℕ) (hc : ∀ n, c n ≤ n)
    (hrat : ¬ Irrational (binaryCoeffSeries c)) :
    ∃ h, 0 < h ∧ ∃ N₀, ∀ N, N₀ ≤ N →
      binaryCoeffTail c (N + h) - binaryCoeffTail c N ∈ Set.range ((↑) : ℤ → ℝ) := by
  have hmem : binaryCoeffSeries c ∈ Set.range ((↑) : ℚ → ℝ) := by
    by_contra hmem
    exact hrat hmem
  obtain ⟨r, hr⟩ := hmem
  have hr' : (r : ℝ) = binaryCoeffSeries c := hr
  have hd0 : r.den ≠ 0 := r.den_pos.ne'
  have hm0 : 0 < ordCompl[2] r.den := Nat.ordCompl_pos 2 hd0
  have hcop : Nat.Coprime 2 (ordCompl[2] r.den) := Nat.coprime_ordCompl Nat.prime_two hd0
  refine ⟨Nat.totient (ordCompl[2] r.den), Nat.totient_pos.mpr hm0, r.den.factorization 2,
    fun N hN => ?_⟩
  have heuler : 2 ^ Nat.totient (ordCompl[2] r.den) ≡ 1 [MOD ordCompl[2] r.den] :=
    Nat.ModEq.pow_totient hcop
  have hmdvd : ordCompl[2] r.den ∣ 2 ^ Nat.totient (ordCompl[2] r.den) - 1 :=
    (Nat.modEq_iff_dvd' (Nat.one_le_pow _ _ (by norm_num))).mp heuler.symm
  have hfact : 2 ^ r.den.factorization 2 * ordCompl[2] r.den = r.den :=
    Nat.ordProj_mul_ordCompl_eq_self r.den 2
  have hden : ((r.den : ℕ) : ℝ) =
      (2 : ℝ) ^ r.den.factorization 2 * ((ordCompl[2] r.den : ℕ) : ℝ) := by
    exact_mod_cast hfact.symm
  refine GenericTailCertificates.generic_tail_period c hc r.num (r.den.factorization 2)
    (ordCompl[2] r.den) _ N hm0 hN hmdvd ?_
  rw [← hr', Rat.cast_def, hden]

/-- **Soundness of the cofinal supply.**  For `c(n) ≤ n`, the sequence-parametric certificate
supply `separation c` (a certificate at arbitrarily large `N` for every lag `h > 0`) makes the
binary series irrational.  At `c = φ` this is `irrational_totient_series_of_certificate_supply`. -/
theorem irrational_of_separation (c : ℕ → ℕ) (hc : ∀ n, c n ≤ n)
    (hsep : FinitePrefixCountermodel.separation c) : Irrational (binaryCoeffSeries c) := by
  by_contra hrat
  obtain ⟨h, hh, N₀, hint⟩ := exists_integral_tail_period_of_rational c hc hrat
  obtain ⟨N, hN, L, hcert⟩ := hsep h hh N₀
  exact GenericTailCertificates.certificate_sound c hc h N L hcert (hint N hN)

theorem not_separation_of_rational (c : ℕ → ℕ) (hc : ∀ n, c n ≤ n)
    (hrat : ¬ Irrational (binaryCoeffSeries c)) : ¬ FinitePrefixCountermodel.separation c :=
  fun hsep => hrat (irrational_of_separation c hc hsep)

/-! ### The corpus notions at `c = φ` -/

theorem discrepancy_totient (h N L : ℕ) :
    GenericTailCertificates.discrepancy Nat.totient h N L =
      TotientTailPeriodKiller.windowDiscrepancy h N L := by
  unfold GenericTailCertificates.discrepancy TotientTailPeriodKiller.windowDiscrepancy
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [show N + h + j + 1 = N + h + 1 + j by omega, show N + j + 1 = N + 1 + j by omega]

/-- The sequence-parametric certificate at `c = φ` is the #249 certificate `certifiedKill`. -/
theorem certificate_totient_iff (h N L : ℕ) :
    GenericTailCertificates.certificate Nat.totient h N L ↔
      TotientTailPeriodKiller.certifiedKill h N L := by
  unfold GenericTailCertificates.certificate TotientTailPeriodKiller.certifiedKill
  rw [discrepancy_totient]

/-- The sequence-parametric supply at `c = φ` is the hypothesis of
`irrational_totient_series_of_certificate_supply`. -/
theorem separation_totient_iff :
    FinitePrefixCountermodel.separation Nat.totient ↔
      ∀ h : ℕ, 0 < h → ∀ N₀ : ℕ, ∃ N, N₀ ≤ N ∧ ∃ L,
        TotientTailPeriodKiller.certifiedKill h N L := by
  unfold FinitePrefixCountermodel.separation
  simp only [certificate_totient_iff]

theorem irrational_totient_series_of_separation
    (hsep : FinitePrefixCountermodel.separation Nat.totient) :
    Irrational (∑' n : ℕ, (Nat.totient n : ℝ) / 2 ^ n) :=
  TotientTailPeriodKiller.irrational_totient_series_of_certificate_supply
    (separation_totient_iff.mp hsep)

/-! ## The barrier schema -/

/-- **Barrier schema.**  Let `D` be a demand on coefficient sequences that an engine turns into
irrationality of the binary series whenever `c(n) ≤ n`.  If a property set `P` holds for some
sequence `a` with `a(n) ≤ n` and a rational binary value, then `P` does not imply `D`. -/
theorem no_route_of_rational_witness {P D : (ℕ → ℕ) → Prop}
    (engine : ∀ c : ℕ → ℕ, (∀ n, c n ≤ n) → D c → Irrational (binaryCoeffSeries c))
    {a : ℕ → ℕ} (ha : ∀ n, a n ≤ n) (hP : P a) (hrat : ¬ Irrational (binaryCoeffSeries a)) :
    ¬ ∀ c, P c → D c :=
  fun route => hrat (engine a ha (route a hP))

/-- The schema for the certificate supply `separation`. -/
theorem no_separation_route_of_rational_witness {P : (ℕ → ℕ) → Prop}
    {a : ℕ → ℕ} (ha : ∀ n, a n ≤ n) (hP : P a) (hrat : ¬ Irrational (binaryCoeffSeries a)) :
    ¬ ∀ c, P c → FinitePrefixCountermodel.separation c :=
  no_route_of_rational_witness irrational_of_separation ha hP hrat

/-! ## Rounding barriers -/

theorem downShadow_le_self {c : ℕ → ℕ} (hc : ∀ n, c n ≤ n) (q M n : ℕ) :
    downShadow c q M n ≤ n :=
  (downShadow_le c q M n).trans (hc n)

theorem binaryCoeffSeries_downShadow (c : ℕ → ℕ) (hc : ∀ n, c n ≤ n) {q : ℕ} (hq : 0 < q)
    (M : ℕ) (hbig : ∀ n, M < n → q ≤ c n) :
    binaryCoeffSeries (downShadow c q M) = (downNumerator c q M : ℝ) / 2 ^ M := by
  have h0 : downShadow c q M 0 = 0 := by
    have := downShadow_le_self hc q M 0
    omega
  rw [← tsum_eq_binaryCoeffSeries _ h0 (summable_of_le_self _ (downShadow_le_self hc q M))]
  exact (hasSum_downShadow_dyadic c hq M (summable_of_le_self c hc) hbig).tsum_eq

/-- The downward shadow of a sequence with `c(n) ≤ n` has no certificate at any `N ≥ M`. -/
theorem downShadow_no_certificate (c : ℕ → ℕ) (hc : ∀ n, c n ≤ n) {q : ℕ} (hq : 0 < q)
    (M : ℕ) (hbig : ∀ n, M < n → q ≤ c n) :
    ∀ N, M ≤ N → ∀ h L, ¬ GenericTailCertificates.certificate (downShadow c q M) h N L :=
  no_certificate_of_dyadic _ (downShadow_le_self hc q M) _ M
    (binaryCoeffSeries_downShadow c hc hq M hbig)

/-- **Rounding barrier, downward form.**  Let `c(n) ≤ n` and `c(n) ≥ q` beyond `M`.  Agreement
with `c` modulo `q`, lying between `c - q` and `c`, agreement with `c` up to `M` and `a(n) ≤ n`
do not imply the certificate supply `separation a`. -/
theorem down_rounding_barrier (c : ℕ → ℕ) (hc : ∀ n, c n ≤ n) {q : ℕ} (hq : 0 < q) (M : ℕ)
    (hbig : ∀ n, M < n → q ≤ c n) :
    ¬ ∀ a : ℕ → ℕ, (∀ n, a n ≤ n) → (∀ n, a n ≡ c n [MOD q]) →
      (∀ n, a n ≤ c n ∧ c n ≤ a n + q) → (∀ n, n ≤ M → a n = c n) →
      FinitePrefixCountermodel.separation a := by
  intro route
  have hrat : ¬ Irrational (binaryCoeffSeries (downShadow c q M)) := by
    rw [binaryCoeffSeries_downShadow c hc hq M hbig]
    exact not_irrational_int_div_two_pow _ _
  exact not_separation_of_rational _ (downShadow_le_self hc q M) hrat
    (route (downShadow c q M) (downShadow_le_self hc q M) (downShadow_modEq hbig)
      (fun n => ⟨downShadow_le c q M n, le_downShadow_add hbig n⟩)
      (fun _ hn => downShadow_of_le c q hn))

/-- **Rounding barrier at the level of irrationality, downward form.**  For any coefficient
sequence with a convergent binary series and `c(n) ≥ q` beyond `M`, the same properties do not
imply irrationality of `∑ a(n)/2^n`. -/
theorem down_rounding_barrier_irrational (c : ℕ → ℕ) {q : ℕ} (hq : 0 < q) (M : ℕ)
    (hsum : Summable (fun n => (c n : ℝ) / 2 ^ n)) (hbig : ∀ n, M < n → q ≤ c n) :
    ¬ ∀ a : ℕ → ℕ, (∀ n, a n ≡ c n [MOD q]) → (∀ n, a n ≤ c n ∧ c n ≤ a n + q) →
      (∀ n, n ≤ M → a n = c n) → Irrational (∑' n, (a n : ℝ) / 2 ^ n) := by
  intro route
  have h := route (downShadow c q M) (downShadow_modEq hbig)
    (fun n => ⟨downShadow_le c q M n, le_downShadow_add hbig n⟩)
    (fun _ hn => downShadow_of_le c q hn)
  rw [(hasSum_downShadow_dyadic c hq M hsum hbig).tsum_eq] at h
  exact not_irrational_int_div_two_pow _ _ h

theorem upShadow_le_self {c : ℕ → ℕ} (hc : ∀ n, c n ≤ n) {q M : ℕ}
    (hroom : ∀ n, M < n → c n + q ≤ n) (n : ℕ) : upShadow c q M n ≤ n := by
  rcases Nat.lt_or_ge M n with hMn | hnM
  · exact (upShadow_le_add c q M n).trans (hroom n hMn)
  · rw [upShadow_of_le c q hnM]
    exact hc n

theorem binaryCoeffSeries_upShadow (c : ℕ → ℕ) (hc : ∀ n, c n ≤ n) {q : ℕ} (hq : 0 < q)
    (M : ℕ) (hroom : ∀ n, M < n → c n + q ≤ n) :
    binaryCoeffSeries (upShadow c q M) = (upNumerator c q M : ℝ) / 2 ^ M := by
  have h0 : upShadow c q M 0 = 0 := by
    have := upShadow_le_self hc hroom 0
    omega
  rw [← tsum_eq_binaryCoeffSeries _ h0 (summable_of_le_self _ (upShadow_le_self hc hroom))]
  exact (hasSum_upShadow_dyadic c hq M (summable_of_le_self c hc)).tsum_eq

/-- The upward shadow of a sequence with `c(n) + q ≤ n` beyond `M` has no certificate at any
`N ≥ M`. -/
theorem upShadow_no_certificate (c : ℕ → ℕ) (hc : ∀ n, c n ≤ n) {q : ℕ} (hq : 0 < q)
    (M : ℕ) (hroom : ∀ n, M < n → c n + q ≤ n) :
    ∀ N, M ≤ N → ∀ h L, ¬ GenericTailCertificates.certificate (upShadow c q M) h N L :=
  no_certificate_of_dyadic _ (upShadow_le_self hc hroom) _ M
    (binaryCoeffSeries_upShadow c hc hq M hroom)

/-- **Rounding barrier, upward form.**  Let `c(n) ≤ n` and `c(n) + q ≤ n` beyond `M`.
Agreement with `c` modulo `q`, lying between `c` and `c + q`, agreement with `c` up to `M` and
`a(n) ≤ n` do not imply the certificate supply `separation a`. -/
theorem up_rounding_barrier (c : ℕ → ℕ) (hc : ∀ n, c n ≤ n) {q : ℕ} (hq : 0 < q) (M : ℕ)
    (hroom : ∀ n, M < n → c n + q ≤ n) :
    ¬ ∀ a : ℕ → ℕ, (∀ n, a n ≤ n) → (∀ n, a n ≡ c n [MOD q]) →
      (∀ n, c n ≤ a n ∧ a n ≤ c n + q) → (∀ n, n ≤ M → a n = c n) →
      FinitePrefixCountermodel.separation a := by
  intro route
  have hrat : ¬ Irrational (binaryCoeffSeries (upShadow c q M)) := by
    rw [binaryCoeffSeries_upShadow c hc hq M hroom]
    exact not_irrational_int_div_two_pow _ _
  exact not_separation_of_rational _ (upShadow_le_self hc hroom) hrat
    (route (upShadow c q M) (upShadow_le_self hc hroom) (upShadow_modEq c q M)
      (fun n => ⟨le_upShadow c q M n, upShadow_le_add c q M n⟩)
      (fun _ hn => upShadow_of_le c q hn))

/-- **Rounding barrier at the level of irrationality, upward form.**  For any coefficient
sequence with a convergent binary series, the same properties do not imply irrationality. -/
theorem up_rounding_barrier_irrational (c : ℕ → ℕ) {q : ℕ} (hq : 0 < q) (M : ℕ)
    (hsum : Summable (fun n => (c n : ℝ) / 2 ^ n)) :
    ¬ ∀ a : ℕ → ℕ, (∀ n, a n ≡ c n [MOD q]) → (∀ n, c n ≤ a n ∧ a n ≤ c n + q) →
      (∀ n, n ≤ M → a n = c n) → Irrational (∑' n, (a n : ℝ) / 2 ^ n) := by
  intro route
  have h := route (upShadow c q M) (upShadow_modEq c q M)
    (fun n => ⟨le_upShadow c q M n, upShadow_le_add c q M n⟩)
    (fun _ hn => upShadow_of_le c q hn)
  rw [(hasSum_upShadow_dyadic c hq M hsum).tsum_eq] at h
  exact not_irrational_int_div_two_pow _ _ h

/-! ## Erdős #249: the totient -/

theorem two_le_totient_of_three_le {n : ℕ} (hn : 3 ≤ n) : 2 ≤ Nat.totient n := by
  obtain ⟨k, hk⟩ := Nat.totient_even (show 2 < n by omega)
  have hpos : 0 < Nat.totient n := Nat.totient_pos.mpr (by omega)
  omega

theorem totient_big : ∀ n, 2 < n → 2 ≤ Nat.totient n :=
  fun _ hn => two_le_totient_of_three_le hn

/-- **The within-two totient shadow**: `φ(n)` for `n ≤ 2`, and `φ(n) - 2 d_{n-2}` for `n ≥ 3`,
where `d_j` is the `j`-th binary digit of `fract(T_φ(2)/2) = 2S - 5/2`. -/
def totientShadow : ℕ → ℕ := downShadow Nat.totient 2 2

theorem totientShadow_le_self (n : ℕ) : totientShadow n ≤ n :=
  downShadow_le_self Nat.totient_le 2 2 n

theorem totientShadow_mod_two (n : ℕ) : totientShadow n % 2 = Nat.totient n % 2 :=
  downShadow_modEq totient_big n

theorem totientShadow_eq_of_le_two {n : ℕ} (hn : n ≤ 2) : totientShadow n = Nat.totient n :=
  downShadow_of_le Nat.totient 2 hn

theorem totient_sub_totientShadow (n : ℕ) :
    Nat.totient n - totientShadow n = 0 ∨ Nat.totient n - totientShadow n = 2 := by
  have h : totientShadow n + 2 * placedDigit (downFraction Nat.totient 2 2) 2 n =
      Nat.totient n :=
    downShadow_add totient_big n
  rcases Nat.le_one_iff_eq_zero_or_eq_one.mp
      (placedDigit_le_one (downFraction Nat.totient 2 2) 2 n) with hd | hd <;>
    rw [hd] at h <;> omega

theorem abs_totientShadow_sub_le (n : ℕ) : |(totientShadow n : ℤ) - Nat.totient n| ≤ 2 := by
  have h1 : totientShadow n ≤ Nat.totient n := downShadow_le Nat.totient 2 2 n
  have h2 : Nat.totient n ≤ totientShadow n + 2 := le_downShadow_add totient_big n
  rw [abs_le]
  constructor <;> omega

theorem totientTail_two_bounds :
    2 ≤ binaryCoeffTail Nat.totient 2 ∧ binaryCoeffTail Nat.totient 2 < 4 := by
  have h3 : binaryCoeffTail Nat.totient 3 =
      2 * binaryCoeffTail Nat.totient 2 - (Nat.totient 3 : ℝ) :=
    binaryCoeffTail_succ Nat.totient Nat.totient_le 2
  have h4 : binaryCoeffTail Nat.totient 4 =
      2 * binaryCoeffTail Nat.totient 3 - (Nat.totient 4 : ℝ) :=
    binaryCoeffTail_succ Nat.totient Nat.totient_le 3
  have h5 : binaryCoeffTail Nat.totient 5 =
      2 * binaryCoeffTail Nat.totient 4 - (Nat.totient 5 : ℝ) :=
    binaryCoeffTail_succ Nat.totient Nat.totient_le 4
  have hT5 := binaryCoeffTail_nonneg Nat.totient 5
  have hT3 : binaryCoeffTail Nat.totient 3 ≤ ((3 : ℕ) : ℝ) + 2 :=
    binaryCoeffTail_le Nat.totient Nat.totient_le 3
  have e3 : Nat.totient 3 = 2 := by decide
  have e4 : Nat.totient 4 = 2 := by decide
  have e5 : Nat.totient 5 = 4 := by decide
  rw [e3] at h3
  rw [e4] at h4
  rw [e5] at h5
  push_cast at h3 h4 h5 hT3
  constructor <;> linarith

theorem totientTail_two_gt : 2 < binaryCoeffTail Nat.totient 2 := by
  have h3 : binaryCoeffTail Nat.totient 3 =
      2 * binaryCoeffTail Nat.totient 2 - (Nat.totient 3 : ℝ) :=
    binaryCoeffTail_succ Nat.totient Nat.totient_le 2
  have h4 : binaryCoeffTail Nat.totient 4 =
      2 * binaryCoeffTail Nat.totient 3 - (Nat.totient 4 : ℝ) :=
    binaryCoeffTail_succ Nat.totient Nat.totient_le 3
  have h5 : binaryCoeffTail Nat.totient 5 =
      2 * binaryCoeffTail Nat.totient 4 - (Nat.totient 5 : ℝ) :=
    binaryCoeffTail_succ Nat.totient Nat.totient_le 4
  have h6 : binaryCoeffTail Nat.totient 6 =
      2 * binaryCoeffTail Nat.totient 5 - (Nat.totient 6 : ℝ) :=
    binaryCoeffTail_succ Nat.totient Nat.totient_le 5
  have hT6 := binaryCoeffTail_nonneg Nat.totient 6
  have e3 : Nat.totient 3 = 2 := by decide
  have e4 : Nat.totient 4 = 2 := by decide
  have e5 : Nat.totient 5 = 4 := by decide
  have e6 : Nat.totient 6 = 2 := by decide
  rw [e3] at h3
  rw [e4] at h4
  rw [e5] at h5
  rw [e6] at h6
  push_cast at h3 h4 h5 h6
  linarith

theorem floor_totientTail_two : ⌊binaryCoeffTail Nat.totient 2 / ((2 : ℕ) : ℝ)⌋ = 1 := by
  obtain ⟨h1, h2⟩ := totientTail_two_bounds
  rw [Int.floor_eq_iff]
  push_cast
  constructor <;> linarith

/-- **The shadow's value.**  `∑ a(n)/2^n = 5/4` for the within-two totient shadow. -/
theorem hasSum_totientShadow :
    HasSum (fun n => (totientShadow n : ℝ) / 2 ^ n) (5 / 4) := by
  have h := hasSum_downShadow Nat.totient (q := 2) (by norm_num) 2
    (summable_of_le_self _ Nat.totient_le) totient_big
  rw [floor_totientTail_two] at h
  show HasSum (fun n => (downShadow Nat.totient 2 2 n : ℝ) / 2 ^ n) (5 / 4)
  convert h using 1
  norm_num [Finset.sum_range_succ, Nat.totient_zero, Nat.totient_one, Nat.totient_two]

theorem tsum_totientShadow : ∑' n : ℕ, (totientShadow n : ℝ) / 2 ^ n = 5 / 4 :=
  hasSum_totientShadow.tsum_eq

theorem binaryCoeffSeries_totientShadow :
    binaryCoeffSeries totientShadow = ((5 : ℤ) : ℝ) / 2 ^ 2 := by
  have h0 : totientShadow 0 = 0 := by
    have := totientShadow_le_self 0
    omega
  rw [← tsum_eq_binaryCoeffSeries _ h0 (summable_of_le_self _ totientShadow_le_self),
    tsum_totientShadow]
  norm_num

theorem not_irrational_totientShadow :
    ¬ Irrational (∑' n : ℕ, (totientShadow n : ℝ) / 2 ^ n) := by
  rw [tsum_totientShadow]
  exact fun h => h.ne_rational 5 4 (by norm_num)

/-- **No certificate for the shadow.**  The within-two totient shadow has no certificate at any
`N ≥ 2`, any lag `h` and any depth `L`. -/
theorem totientShadow_no_certificate :
    ∀ N, 2 ≤ N → ∀ h L, ¬ GenericTailCertificates.certificate totientShadow h N L :=
  no_certificate_of_dyadic totientShadow totientShadow_le_self 5 2
    binaryCoeffSeries_totientShadow

/-- The #249 property bundle: agreement with `φ` modulo two, distance at most two from `φ`, and
`a(n) ≤ n` (nonnegativity is built into `ℕ`). -/
def TotientParityWithinTwo (a : ℕ → ℕ) : Prop :=
  (∀ n, a n % 2 = Nat.totient n % 2) ∧ (∀ n, |(a n : ℤ) - Nat.totient n| ≤ 2) ∧
    (∀ n, a n ≤ n)

theorem totientParityWithinTwo_totient : TotientParityWithinTwo Nat.totient :=
  ⟨fun _ => rfl, fun n => by simp, Nat.totient_le⟩

theorem totientParityWithinTwo_totientShadow : TotientParityWithinTwo totientShadow :=
  ⟨totientShadow_mod_two, abs_totientShadow_sub_le, totientShadow_le_self⟩

/-- **Barrier at the #249 shadow.**  No property `P` that the within-two totient shadow satisfies
implies the certificate supply `separation`. -/
theorem no_certificate_route_of_totientShadow (P : (ℕ → ℕ) → Prop) (hP : P totientShadow)
    (route : ∀ a, P a → FinitePrefixCountermodel.separation a) : False :=
  no_separation_route_of_rational_witness totientShadow_le_self hP
    (by rw [binaryCoeffSeries_totientShadow]; exact not_irrational_int_div_two_pow 5 2) route

/-- **The #249 barrier.**  The parity of `φ`, distance at most two from `φ` and `a(n) ≤ n` do not
imply the certificate supply `separation`, whose instance at `φ` is the hypothesis of
`irrational_totient_series_of_certificate_supply`. -/
theorem no_certificate_route_249
    (route : ∀ a : ℕ → ℕ, TotientParityWithinTwo a → FinitePrefixCountermodel.separation a) :
    False :=
  no_certificate_route_of_totientShadow TotientParityWithinTwo
    totientParityWithinTwo_totientShadow route

theorem totientParityWithinTwo_not_imply_irrational :
    ¬ ∀ a : ℕ → ℕ, TotientParityWithinTwo a → Irrational (∑' n : ℕ, (a n : ℝ) / 2 ^ n) :=
  fun route => not_irrational_totientShadow (route _ totientParityWithinTwo_totientShadow)

theorem tsum_totient_ne_five_fourths : ∑' n : ℕ, (Nat.totient n : ℝ) / 2 ^ n ≠ 5 / 4 := by
  intro h
  rw [tsum_eq_prefix_add_tail Nat.totient (summable_of_le_self _ Nat.totient_le) 2] at h
  norm_num [Finset.sum_range_succ, Nat.totient_zero, Nat.totient_one, Nat.totient_two] at h
  linarith [totientTail_two_gt]

/-- **Multiplicativity separates `φ` from its shadow.** -/
theorem totientShadow_not_multiplicative :
    ¬ ∀ m n, Nat.Coprime m n → totientShadow (m * n) = totientShadow m * totientShadow n := by
  intro hmul
  have hrig := MultiplicativeRigidity.eq_totient_of_multiplicative_of_bounded_sub
    (a := fun n => (totientShadow n : ℝ)) (C := 2)
    (fun m n hmn => by
      show (totientShadow (m * n) : ℝ) = (totientShadow m : ℝ) * (totientShadow n : ℝ)
      rw [hmul m n hmn, Nat.cast_mul])
    (fun n _ => by
      show |(totientShadow n : ℝ) - (Nat.totient n : ℝ)| ≤ 2
      have h := abs_totientShadow_sub_le n
      exact_mod_cast h)
  have heq : ∀ n, totientShadow n = Nat.totient n := by
    intro n
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · exact totientShadow_eq_of_le_two (by norm_num)
    · have h : (totientShadow n : ℝ) = (Nat.totient n : ℝ) := hrig n hn
      exact_mod_cast h
  apply tsum_totient_ne_five_fourths
  rw [← tsum_totientShadow]
  exact tsum_congr fun n => by rw [heq n]

/-! ### Every fixed modulus for #249 -/

theorem pow_factorization_lt_of_totient_lt {q n p : ℕ} (hn : n ≠ 0)
    (hlt : Nat.totient n < q) (hp : p ∈ n.primeFactors) : p ^ n.factorization p < 2 * q := by
  have hpr : p.Prime := Nat.prime_of_mem_primeFactors hp
  have hk : 0 < n.factorization p :=
    hpr.factorization_pos_of_dvd hn (Nat.dvd_of_mem_primeFactors hp)
  have hφpos : 0 < Nat.totient n := Nat.totient_pos.mpr (Nat.pos_of_ne_zero hn)
  have hle : Nat.totient (p ^ n.factorization p) ≤ Nat.totient n :=
    Nat.le_of_dvd hφpos (Nat.totient_dvd_of_dvd (Nat.ordProj_dvd n p))
  obtain ⟨k, hk'⟩ : ∃ k, n.factorization p = k + 1 := ⟨n.factorization p - 1, by omega⟩
  rw [hk'] at hle ⊢
  rw [Nat.totient_prime_pow_succ hpr] at hle
  have h2 : 2 ≤ p := hpr.two_le
  have hkey : p ^ (k + 1) ≤ 2 * (p ^ k * (p - 1)) := by
    rw [pow_succ]
    have hp2 : p ≤ 2 * (p - 1) := by omega
    calc p ^ k * p ≤ p ^ k * (2 * (p - 1)) := Nat.mul_le_mul_left _ hp2
      _ = 2 * (p ^ k * (p - 1)) := by ring
  omega

/-- `φ(n) < q` forces `n ≤ (2q)^(2q)`: each prime power `p^k ∥ n` has `p^k ≤ 2φ(p^k) ≤ 2φ(n)`. -/
theorem le_of_totient_lt {q n : ℕ} (hn : n ≠ 0) (hlt : Nat.totient n < q) :
    n ≤ (2 * q) ^ (2 * q) := by
  have hq : 0 < q := by omega
  have hprod : ∏ p ∈ n.primeFactors, p ^ n.factorization p = n := by
    have h := Nat.prod_factorization_pow_eq_self hn
    rwa [Finsupp.prod, Nat.support_factorization] at h
  have hsub : n.primeFactors ⊆ Finset.range (2 * q) := by
    intro p hp
    have h1 := pow_factorization_lt_of_totient_lt hn hlt hp
    have hk : 0 < n.factorization p :=
      (Nat.prime_of_mem_primeFactors hp).factorization_pos_of_dvd hn
        (Nat.dvd_of_mem_primeFactors hp)
    have h2 : p ≤ p ^ n.factorization p := Nat.le_self_pow (by omega) p
    exact Finset.mem_range.mpr (by omega)
  have hcard : n.primeFactors.card ≤ 2 * q := by
    simpa using Finset.card_le_card hsub
  calc n = ∏ p ∈ n.primeFactors, p ^ n.factorization p := hprod.symm
    _ ≤ (2 * q) ^ n.primeFactors.card :=
        Finset.prod_le_pow_card _ _ _ fun p hp => (pow_factorization_lt_of_totient_lt hn hlt hp).le
    _ ≤ (2 * q) ^ (2 * q) := Nat.pow_le_pow_right (by omega) hcard

theorem totient_ge_of_large {q n : ℕ} (hn : (2 * q) ^ (2 * q) < n) : q ≤ Nat.totient n := by
  by_contra h
  have := le_of_totient_lt (by omega : n ≠ 0) (not_le.mp h)
  omega

/-- **The #249 barrier at every modulus.**  For every `q ≥ 1` and every prefix length
`B ≥ (2q)^(2q)`: agreement with `φ` modulo `q`, lying between `φ - q` and `φ`, agreement with `φ`
up to `B` and `a(n) ≤ n` do not imply the certificate supply `separation a`. -/
theorem totient_rounding_barrier {q B : ℕ} (hq : 0 < q) (hB : (2 * q) ^ (2 * q) ≤ B) :
    ¬ ∀ a : ℕ → ℕ, (∀ n, a n ≤ n) → (∀ n, a n ≡ Nat.totient n [MOD q]) →
      (∀ n, a n ≤ Nat.totient n ∧ Nat.totient n ≤ a n + q) →
      (∀ n, n ≤ B → a n = Nat.totient n) → FinitePrefixCountermodel.separation a :=
  down_rounding_barrier Nat.totient Nat.totient_le hq B
    (fun _ hn => totient_ge_of_large (lt_of_le_of_lt hB hn))

theorem totient_downShadow_no_certificate {q B : ℕ} (hq : 0 < q)
    (hB : (2 * q) ^ (2 * q) ≤ B) :
    ∀ N, B ≤ N → ∀ h L,
      ¬ GenericTailCertificates.certificate (downShadow Nat.totient q B) h N L :=
  downShadow_no_certificate Nat.totient Nat.totient_le hq B
    (fun _ hn => totient_ge_of_large (lt_of_le_of_lt hB hn))

/-! ## Erdős #251: the primes -/

theorem add_two_le_prime0 (n : ℕ) : n + 2 ≤ ErdosProblems.Erdos251.prime0 n :=
  Nat.add_two_le_nth_prime n

theorem summable_prime0_div :
    Summable (fun n => (ErdosProblems.Erdos251.prime0 n : ℝ) / 2 ^ n) :=
  (ErdosProblems.Erdos251.summable_primeDyadicTerm.mul_left 2).congr fun n =>
    (ErdosProblems.Erdos251.primeDisplayedDyadicTerm_eq_two_mul n).symm

/-- **The #251 barrier.**  For every modulus `q ≥ 1` and prefix length `B ≥ q`: agreement with
the primes `p_n` modulo `q`, lying between `p_n - q` and `p_n`, and agreement with `p_n` up to `B`
do not imply irrationality of `∑ a(n)/2^n`. -/
theorem prime_rounding_barrier {q B : ℕ} (hq : 0 < q) (hB : q ≤ B) :
    ¬ ∀ a : ℕ → ℕ, (∀ n, a n ≡ ErdosProblems.Erdos251.prime0 n [MOD q]) →
      (∀ n, a n ≤ ErdosProblems.Erdos251.prime0 n ∧ ErdosProblems.Erdos251.prime0 n ≤ a n + q) →
      (∀ n, n ≤ B → a n = ErdosProblems.Erdos251.prime0 n) →
      Irrational (∑' n, (a n : ℝ) / 2 ^ n) :=
  down_rounding_barrier_irrational _ hq B summable_prime0_div fun n hn => by
    have := add_two_le_prime0 n
    omega

/-! ## Erdős #257 and the base-two case of #1049: divisor counts over a support -/

theorem supportCoeff_zero (A : Set ℕ) : supportCoeff A 0 = 0 := by
  simp [supportCoeff]

theorem card_divisors_le_half_add_one (n : ℕ) : n.divisors.card ≤ n / 2 + 1 := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp
  have hsub : n.divisors ⊆ insert n (Finset.Icc 1 (n / 2)) := by
    intro d hd
    have hdvd : d ∣ n := Nat.dvd_of_mem_divisors hd
    have hdpos : 0 < d := Nat.pos_of_mem_divisors hd
    rw [Finset.mem_insert, Finset.mem_Icc]
    by_cases hdn : d = n
    · exact Or.inl hdn
    · right
      refine ⟨hdpos, ?_⟩
      obtain ⟨k, hk⟩ := hdvd
      have hk0 : k ≠ 0 := by
        rintro rfl
        simp at hk
        omega
      have hk1 : k ≠ 1 := by
        rintro rfl
        simp at hk
        exact hdn hk.symm
      have h2 : d * 2 ≤ n := by
        rw [hk]
        exact Nat.mul_le_mul_left d (by omega)
      omega
  calc n.divisors.card ≤ (insert n (Finset.Icc 1 (n / 2))).card := Finset.card_le_card hsub
    _ ≤ (Finset.Icc 1 (n / 2)).card + 1 := Finset.card_insert_le _ _
    _ = n / 2 + 1 := by simp

theorem supportCoeff_add_le (A : Set ℕ) {q n : ℕ} (hn : 2 * q + 1 < n) :
    supportCoeff A n + q ≤ n := by
  have h1 := supportCoeff_le_card_divisors A n
  have h2 := card_divisors_le_half_add_one n
  omega

theorem erdosSupportSeries_two_eq (A : Set ℕ) :
    erdosSupportSeries 2 A = binaryCoeffSeries (supportCoeff A) := by
  rw [erdosSupportSeries_eq_tsum_supportCoeff 2 A le_rfl]
  unfold binaryCoeffSeries
  norm_num

/-- **The #257 barrier.**  For every support `A`, modulus `q ≥ 1` and prefix length
`B ≥ 2q + 1`: agreement with `f_A` modulo `q`, lying between `f_A` and `f_A + q`, agreement with
`f_A` up to `B` and `a(n) ≤ n` do not imply the certificate supply `separation a`. -/
theorem support_rounding_barrier (A : Set ℕ) {q B : ℕ} (hq : 0 < q) (hB : 2 * q + 1 ≤ B) :
    ¬ ∀ a : ℕ → ℕ, (∀ n, a n ≤ n) → (∀ n, a n ≡ supportCoeff A n [MOD q]) →
      (∀ n, supportCoeff A n ≤ a n ∧ a n ≤ supportCoeff A n + q) →
      (∀ n, n ≤ B → a n = supportCoeff A n) → FinitePrefixCountermodel.separation a :=
  up_rounding_barrier (supportCoeff A) (supportCoeff_le_self A) hq B
    fun _ hn => supportCoeff_add_le A (by omega)

theorem support_upShadow_no_certificate (A : Set ℕ) {q B : ℕ} (hq : 0 < q)
    (hB : 2 * q + 1 ≤ B) :
    ∀ N, B ≤ N → ∀ h L,
      ¬ GenericTailCertificates.certificate (upShadow (supportCoeff A) q B) h N L :=
  upShadow_no_certificate (supportCoeff A) (supportCoeff_le_self A) hq B
    fun _ hn => supportCoeff_add_le A (by omega)

/-- **The #257 barrier at the level of irrationality.**  For every support `A`, modulus `q ≥ 1`
and prefix length `B`, the same properties do not imply irrationality of `∑ a(n)/2^n`. -/
theorem support_rounding_barrier_irrational (A : Set ℕ) {q : ℕ} (hq : 0 < q) (B : ℕ) :
    ¬ ∀ a : ℕ → ℕ, (∀ n, a n ≡ supportCoeff A n [MOD q]) →
      (∀ n, supportCoeff A n ≤ a n ∧ a n ≤ supportCoeff A n + q) →
      (∀ n, n ≤ B → a n = supportCoeff A n) → Irrational (∑' n, (a n : ℝ) / 2 ^ n) :=
  up_rounding_barrier_irrational (supportCoeff A) hq B
    (summable_of_le_self _ (supportCoeff_le_self A))

/-- **The divisor count.**  The full support gives `τ(n) = #divisors(n)`, the coefficient
sequence of `∑ 1/(2^n - 1)`, the base-two case of Erdős #1049. -/
theorem divisorCount_rounding_barrier {q B : ℕ} (hq : 0 < q) (hB : 2 * q + 1 ≤ B) :
    ¬ ∀ a : ℕ → ℕ, (∀ n, a n ≤ n) → (∀ n, a n ≡ n.divisors.card [MOD q]) →
      (∀ n, n.divisors.card ≤ a n ∧ a n ≤ n.divisors.card + q) →
      (∀ n, n ≤ B → a n = n.divisors.card) → FinitePrefixCountermodel.separation a := by
  have h := support_rounding_barrier Set.univ hq hB
  simpa only [supportCoeff_univ_eq_card_divisors] using h

end ErdosProblems.Synthesis.RoundingBarrier

#print axioms ErdosProblems.Synthesis.MultiplicativeRigidity.eq_of_multiplicative_of_bounded_sub
#print axioms ErdosProblems.Synthesis.MultiplicativeRigidity.eq_totient_of_multiplicative_of_bounded_sub
#print axioms ErdosProblems.Synthesis.MultiplicativeRigidity.eq_card_divisors_of_multiplicative_of_bounded_sub
#print axioms ErdosProblems.Synthesis.RoundingBarrier.hasSum_placedDigit
#print axioms ErdosProblems.Synthesis.RoundingBarrier.hasSum_downShadow_dyadic
#print axioms ErdosProblems.Synthesis.RoundingBarrier.hasSum_upShadow_dyadic
#print axioms ErdosProblems.Synthesis.RoundingBarrier.exists_downShadow
#print axioms ErdosProblems.Synthesis.RoundingBarrier.exists_upShadow
#print axioms ErdosProblems.Synthesis.RoundingBarrier.no_certificate_of_dyadic
#print axioms ErdosProblems.Synthesis.RoundingBarrier.irrational_of_separation
#print axioms ErdosProblems.Synthesis.RoundingBarrier.not_separation_of_rational
#print axioms ErdosProblems.Synthesis.RoundingBarrier.certificate_totient_iff
#print axioms ErdosProblems.Synthesis.RoundingBarrier.separation_totient_iff
#print axioms ErdosProblems.Synthesis.RoundingBarrier.irrational_totient_series_of_separation
#print axioms ErdosProblems.Synthesis.RoundingBarrier.no_route_of_rational_witness
#print axioms ErdosProblems.Synthesis.RoundingBarrier.no_separation_route_of_rational_witness
#print axioms ErdosProblems.Synthesis.RoundingBarrier.down_rounding_barrier
#print axioms ErdosProblems.Synthesis.RoundingBarrier.down_rounding_barrier_irrational
#print axioms ErdosProblems.Synthesis.RoundingBarrier.up_rounding_barrier
#print axioms ErdosProblems.Synthesis.RoundingBarrier.up_rounding_barrier_irrational
#print axioms ErdosProblems.Synthesis.RoundingBarrier.hasSum_totientShadow
#print axioms ErdosProblems.Synthesis.RoundingBarrier.tsum_totientShadow
#print axioms ErdosProblems.Synthesis.RoundingBarrier.totientShadow_mod_two
#print axioms ErdosProblems.Synthesis.RoundingBarrier.abs_totientShadow_sub_le
#print axioms ErdosProblems.Synthesis.RoundingBarrier.totient_sub_totientShadow
#print axioms ErdosProblems.Synthesis.RoundingBarrier.totientShadow_le_self
#print axioms ErdosProblems.Synthesis.RoundingBarrier.totientShadow_no_certificate
#print axioms ErdosProblems.Synthesis.RoundingBarrier.no_certificate_route_of_totientShadow
#print axioms ErdosProblems.Synthesis.RoundingBarrier.no_certificate_route_249
#print axioms ErdosProblems.Synthesis.RoundingBarrier.totientParityWithinTwo_not_imply_irrational
#print axioms ErdosProblems.Synthesis.RoundingBarrier.totientShadow_not_multiplicative
#print axioms ErdosProblems.Synthesis.RoundingBarrier.totient_ge_of_large
#print axioms ErdosProblems.Synthesis.RoundingBarrier.totient_rounding_barrier
#print axioms ErdosProblems.Synthesis.RoundingBarrier.totient_downShadow_no_certificate
#print axioms ErdosProblems.Synthesis.RoundingBarrier.prime_rounding_barrier
#print axioms ErdosProblems.Synthesis.RoundingBarrier.erdosSupportSeries_two_eq
#print axioms ErdosProblems.Synthesis.RoundingBarrier.support_rounding_barrier
#print axioms ErdosProblems.Synthesis.RoundingBarrier.support_upShadow_no_certificate
#print axioms ErdosProblems.Synthesis.RoundingBarrier.support_rounding_barrier_irrational
#print axioms ErdosProblems.Synthesis.RoundingBarrier.divisorCount_rounding_barrier
