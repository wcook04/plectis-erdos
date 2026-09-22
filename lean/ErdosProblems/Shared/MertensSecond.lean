import Mathlib.NumberTheory.Chebyshev
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Data.Nat.Choose.Factorization
import Mathlib.Data.Nat.Factorization.Basic

/-!
# Mertens' first theorem and the difference form of Mertens' second theorem

Mathlib has Chebyshev's upper bound `θ(x) ≤ x log 4`
(`Chebyshev.theta_le_log4_mul_x`) but no Mertens theorem.  This file proves
both of Mertens' classical estimates with explicit constants, by elementary
means only; no integral and no prime number theorem is used.

* `mertens_first` / `abs_primeLogSum_sub_log_le` (**Mertens I**): for every
  `n ≥ 1`, `|∑_{p ≤ n} log p / p - log n| ≤ 3`.
  Legendre's formula `log n! = ∑_{p ≤ n} v_p(n!) log p` is combined with
  `⌊n/p⌋ ≤ v_p(n!) ≤ n/(p-1)`, the bounds `n log n - n ≤ log n! ≤ n log n`,
  Chebyshev's `θ(n) ≤ n log 4`, and the telescoping majorant
  `∑_{p ≤ n} log p / (p(p-1)) ≤ 2` (the step `g(k-1) - g(k)` of
  `g(k) = (log k + 2)/k` dominates `log k / (k(k-1))`).
* `abs_sum_inv_primes_sub_loglog_le` (**Mertens II, difference form**): for
  `2 ≤ M ≤ N`,
  `|∑_{M < p ≤ N} 1/p - (log log N - log log M)| ≤ 10 / log M`.
  Discrete summation by parts against `1/log k` reduces this to Mertens I and
  the per-step comparison `0 ≤ log(b/a) - (1 - a/b) ≤ 1/a - 1/b` for
  `a = log k`, `b = log (k+1)`; every error term telescopes.
* `card_primes_Ioc_mul_log_le`: `#{M < p ≤ x} · log M ≤ x log 4`.

Nothing here mentions a specific Erdős problem; the file imports only Mathlib.
-/

namespace ErdosProblems.Shared.Mertens

open Finset Real

/-! ## Legendre's formula as a logarithmic identity -/

/-- `log n! = ∑_{p ≤ n} v_p(n!) log p`. -/
theorem log_factorial_eq_sum_primes (n : ℕ) :
    Real.log (n.factorial : ℝ) =
      ∑ p ∈ (Ioc 0 n).filter Nat.Prime,
        ((n.factorial.factorization p : ℕ) : ℝ) * Real.log p := by
  rw [Real.log_nat_eq_sum_factorization]
  refine Finsupp.sum_of_support_subset _ ?_ _ (fun p _ => by simp)
  intro p hp
  rw [Nat.support_factorization] at hp
  have hpp := Nat.prime_of_mem_primeFactors hp
  have hdvd := Nat.dvd_of_mem_primeFactors hp
  simp only [Finset.mem_filter, Finset.mem_Ioc]
  exact ⟨⟨hpp.pos, (Nat.Prime.dvd_factorial hpp).mp hdvd⟩, hpp⟩

/-- The first Legendre term: `⌊n/p⌋ ≤ v_p(n!)`. -/
theorem div_le_factorization_factorial {n p : ℕ} (hp : p.Prime) :
    n / p ≤ n.factorial.factorization p := by
  rw [Nat.factorization_factorial hp (Nat.lt_succ_self (Nat.log p n))]
  rcases Nat.lt_or_ge n p with hnp | hpn
  · rw [Nat.div_eq_of_lt hnp]; exact Nat.zero_le _
  · have hlog : 0 < Nat.log p n := Nat.log_pos hp.one_lt hpn
    have hmem : 1 ∈ Finset.Ico 1 (Nat.log p n).succ := by
      rw [Finset.mem_Ico]; omega
    calc n / p = n / p ^ 1 := by rw [pow_one]
      _ ≤ ∑ i ∈ Finset.Ico 1 (Nat.log p n).succ, n / p ^ i :=
        Finset.single_le_sum (f := fun i => n / p ^ i) (fun i _ => Nat.zero_le _) hmem

/-- The geometric Legendre bound: `v_p(n!) ≤ n / (p - 1)`. -/
theorem factorization_factorial_le_div {n p : ℕ} (hp : p.Prime) :
    ((n.factorial.factorization p : ℕ) : ℝ) ≤ n / ((p : ℝ) - 1) := by
  have h := Nat.sub_one_mul_factorization_factorial (n := n) hp
  have hle : (p - 1) * n.factorial.factorization p ≤ n := by rw [h]; exact Nat.sub_le _ _
  have hp1 : (1 : ℝ) < p := by exact_mod_cast hp.one_lt
  have hpos : (0 : ℝ) < (p : ℝ) - 1 := by linarith
  rw [le_div_iff₀ hpos]
  have hcast : ((p - 1 : ℕ) : ℝ) = (p : ℝ) - 1 := by
    rw [Nat.cast_sub hp.one_le]; simp
  have h2 : (((p - 1) * n.factorial.factorization p : ℕ) : ℝ) ≤ (n : ℝ) := by exact_mod_cast hle
  rw [Nat.cast_mul, hcast] at h2
  linarith [h2]

/-- `log n! ≤ n log n`. -/
theorem log_factorial_le (n : ℕ) : Real.log (n.factorial : ℝ) ≤ n * Real.log n := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp
  have h1 : (n.factorial : ℝ) ≤ (n : ℝ) ^ n := by exact_mod_cast Nat.factorial_le_pow n
  have h2 : (0 : ℝ) < n.factorial := by exact_mod_cast Nat.factorial_pos n
  calc Real.log (n.factorial : ℝ) ≤ Real.log ((n : ℝ) ^ n) := Real.log_le_log h2 h1
    _ = n * Real.log n := by rw [Real.log_pow]

/-- `n log n - n ≤ log n!`, from `n^n / n! ≤ e^n`. -/
theorem sub_le_log_factorial (n : ℕ) : n * Real.log n - n ≤ Real.log (n.factorial : ℝ) := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp
  have hnpos : (0 : ℝ) < n := by exact_mod_cast hn
  have h := Real.pow_div_factorial_le_exp (n : ℝ) hnpos.le n
  have hf : (0 : ℝ) < n.factorial := by exact_mod_cast Nat.factorial_pos n
  have hq : 0 < (n : ℝ) ^ n / n.factorial := by positivity
  have hlog := Real.log_le_log hq h
  rw [Real.log_exp, Real.log_div (by positivity) hf.ne', Real.log_pow] at hlog
  linarith

/-- Chebyshev's bound `θ(n) ≤ n log 4`, restated on the natural numbers. -/
theorem sum_log_primes_le (n : ℕ) :
    ∑ p ∈ (Ioc 0 n).filter Nat.Prime, Real.log p ≤ Real.log 4 * n := by
  have h := Chebyshev.theta_le_log4_mul_x (Nat.cast_nonneg (α := ℝ) n)
  rw [Chebyshev.theta, Nat.floor_natCast] at h
  exact h

/-- `n / p - 1 ≤ ⌊n / p⌋`. -/
theorem div_sub_one_le_natDiv (n p : ℕ) (hp : 0 < p) :
    (n : ℝ) / p - 1 ≤ ((n / p : ℕ) : ℝ) := by
  have h := Nat.div_add_mod n p
  have hmod := Nat.mod_lt n hp
  have hpR : (0 : ℝ) < p := by exact_mod_cast hp
  rw [div_sub_one hpR.ne', div_le_iff₀ hpR]
  have h1 : (n : ℝ) = p * ((n / p : ℕ) : ℝ) + ((n % p : ℕ) : ℝ) := by exact_mod_cast h.symm
  have h2 : ((n % p : ℕ) : ℝ) < p := by exact_mod_cast hmod
  nlinarith

/-! ## Mertens' first theorem -/

/-- Mertens' sum `∑_{p ≤ n} log p / p`. -/
noncomputable def primeLogSum (n : ℕ) : ℝ :=
  ∑ p ∈ (Ioc 0 n).filter Nat.Prime, Real.log p / p

/-- Upper half of Mertens' first theorem: `∑_{p ≤ n} log p / p ≤ log n + log 4`. -/
theorem primeLogSum_le (n : ℕ) (hn : 0 < n) : primeLogSum n ≤ Real.log n + Real.log 4 := by
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have key : ∑ p ∈ (Ioc 0 n).filter Nat.Prime, ((n : ℝ) / p - 1) * Real.log p
      ≤ Real.log (n.factorial : ℝ) := by
    rw [log_factorial_eq_sum_primes]
    apply Finset.sum_le_sum
    intro p hp
    have hpp := (Finset.mem_filter.mp hp).2
    have hlog : 0 ≤ Real.log p := Real.log_nonneg (by exact_mod_cast hpp.one_le)
    apply mul_le_mul_of_nonneg_right _ hlog
    calc (n : ℝ) / p - 1 ≤ ((n / p : ℕ) : ℝ) := div_sub_one_le_natDiv n p hpp.pos
      _ ≤ _ := by exact_mod_cast div_le_factorization_factorial hpp
  have hsplit : ∑ p ∈ (Ioc 0 n).filter Nat.Prime, ((n : ℝ) / p - 1) * Real.log p
      = n * primeLogSum n - ∑ p ∈ (Ioc 0 n).filter Nat.Prime, Real.log p := by
    rw [primeLogSum, Finset.mul_sum, ← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro p _
    ring
  have hθ := sum_log_primes_le n
  have hfac := log_factorial_le n
  have hmain : (n : ℝ) * primeLogSum n ≤ n * (Real.log n + Real.log 4) := by
    rw [mul_add]; linarith
  exact le_of_mul_le_mul_left hmain hnR

/-- One telescoping step: `log (n+1) / ((n+1) n) ≤ g n - g (n+1)` for
`g k = (log k + 2) / k`. -/
theorem log_div_mul_pred_le_telescope (n : ℕ) (hn : 1 ≤ n) :
    Real.log ((n : ℝ) + 1) / (((n : ℝ) + 1) * n)
      ≤ (Real.log n + 2) / n - (Real.log ((n : ℝ) + 1) + 2) / ((n : ℝ) + 1) := by
  have hnR : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hpos : (0 : ℝ) < n := by linarith
  have hdiff : Real.log ((n : ℝ) + 1) - Real.log n ≤ 1 / n := by
    rw [← Real.log_div (by positivity) hpos.ne']
    have h := Real.log_le_sub_one_of_pos (show (0 : ℝ) < ((n : ℝ) + 1) / n by positivity)
    calc Real.log (((n : ℝ) + 1) / n) ≤ ((n : ℝ) + 1) / n - 1 := h
      _ = 1 / n := by field_simp; ring
  have hid : (Real.log n + 2) / n - (Real.log ((n : ℝ) + 1) + 2) / ((n : ℝ) + 1)
      = (Real.log ((n : ℝ) + 1)
          + (2 - ((n : ℝ) + 1) * (Real.log ((n : ℝ) + 1) - Real.log n)))
          / (((n : ℝ) + 1) * n) := by
    field_simp
    ring
  rw [hid]
  apply div_le_div_of_nonneg_right _ (by positivity)
  have hmul : ((n : ℝ) + 1) * (Real.log ((n : ℝ) + 1) - Real.log n) ≤ 2 := by
    calc ((n : ℝ) + 1) * (Real.log ((n : ℝ) + 1) - Real.log n) ≤ ((n : ℝ) + 1) * (1 / n) := by
          apply mul_le_mul_of_nonneg_left hdiff; positivity
      _ ≤ 2 := by rw [mul_one_div, div_le_iff₀ hpos]; linarith
  linarith

/-- The prime-power correction is at most `2`:
`∑_{p ≤ n} log p / (p (p-1)) ≤ 2 - (log n + 2)/n`. -/
theorem sum_primes_log_div_mul_pred_le (n : ℕ) (hn : 1 ≤ n) :
    ∑ p ∈ (Ioc 0 n).filter Nat.Prime, Real.log p / (p * ((p : ℝ) - 1))
      ≤ 2 - (Real.log n + 2) / n := by
  induction n, hn using Nat.le_induction with
  | base => norm_num [Finset.sum_filter]
  | succ n hn ih =>
    rw [Finset.sum_filter, Finset.sum_Ioc_succ_top (Nat.zero_le n), ← Finset.sum_filter]
    have hstep := log_div_mul_pred_le_telescope n hn
    have hnR : (1 : ℝ) ≤ n := by exact_mod_cast hn
    have hnn : 0 ≤ Real.log ((n : ℝ) + 1) / (((n : ℝ) + 1) * n) := by
      have := Real.log_nonneg (show (1 : ℝ) ≤ (n : ℝ) + 1 by linarith)
      positivity
    push_cast
    have hsimp : ((n : ℝ) + 1 - 1) = n := by ring
    split_ifs
    · rw [hsimp]; linarith
    · linarith

/-- Lower half of Mertens' first theorem: `log n - 3 ≤ ∑_{p ≤ n} log p / p`. -/
theorem log_sub_three_le_primeLogSum (n : ℕ) (hn : 0 < n) : Real.log n - 3 ≤ primeLogSum n := by
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have key : Real.log (n.factorial : ℝ)
      ≤ ∑ p ∈ (Ioc 0 n).filter Nat.Prime, (n : ℝ) / ((p : ℝ) - 1) * Real.log p := by
    rw [log_factorial_eq_sum_primes]
    apply Finset.sum_le_sum
    intro p hp
    have hpp := (Finset.mem_filter.mp hp).2
    exact mul_le_mul_of_nonneg_right (factorization_factorial_le_div hpp)
      (Real.log_nonneg (by exact_mod_cast hpp.one_le))
  have hsplit : ∑ p ∈ (Ioc 0 n).filter Nat.Prime, (n : ℝ) / ((p : ℝ) - 1) * Real.log p
      = n * primeLogSum n
        + n * ∑ p ∈ (Ioc 0 n).filter Nat.Prime, Real.log p / (p * ((p : ℝ) - 1)) := by
    rw [primeLogSum, Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro p hp
    have hpp := (Finset.mem_filter.mp hp).2
    have hp1 : (1 : ℝ) < p := by exact_mod_cast hpp.one_lt
    have hp0 : (p : ℝ) ≠ 0 := by positivity
    have hpm : (p : ℝ) - 1 ≠ 0 := by linarith
    field_simp
    ring
  have htel := sum_primes_log_div_mul_pred_le n hn
  have hlow := sub_le_log_factorial n
  have htel2 : ∑ p ∈ (Ioc 0 n).filter Nat.Prime, Real.log p / (p * ((p : ℝ) - 1)) ≤ 2 := by
    have : 0 ≤ (Real.log n + 2) / n := by
      have := Real.log_nonneg (show (1 : ℝ) ≤ n by exact_mod_cast hn)
      positivity
    linarith
  have hmain : (n : ℝ) * (Real.log n - 3) ≤ n * primeLogSum n := by
    have := mul_le_mul_of_nonneg_left htel2 hnR.le
    rw [mul_sub]
    linarith
  exact le_of_mul_le_mul_left hmain hnR

theorem log_four_lt_three : Real.log 4 < 3 := by
  have h : Real.log 4 = 2 * Real.log 2 := by
    rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow]; norm_num
  rw [h]; linarith [Real.log_two_lt_d9]

/-- **Mertens' first theorem** with an explicit constant:
`|∑_{p ≤ n} log p / p - log n| ≤ 3` for every `n ≥ 1`. -/
theorem abs_primeLogSum_sub_log_le (n : ℕ) (hn : 0 < n) :
    |primeLogSum n - Real.log n| ≤ 3 := by
  have h1 := primeLogSum_le n hn
  have h2 := log_sub_three_le_primeLogSum n hn
  have h4 := log_four_lt_three
  rw [abs_le]; constructor <;> linarith

/-- **Mertens' first theorem**, stated on the prime sum itself:
`|∑_{p ≤ n} log p / p - log n| ≤ 3` for every `n ≥ 1`. -/
theorem mertens_first (n : ℕ) (hn : 0 < n) :
    |∑ p ∈ (Ioc 0 n).filter Nat.Prime, Real.log p / p - Real.log n| ≤ 3 :=
  abs_primeLogSum_sub_log_le n hn

/-! ## Summation by parts and the difference form of Mertens' second theorem -/

/-- Discrete summation by parts on `(M, N]`. -/
theorem sum_Ioc_mul_eq_sub_add_sum {a F f : ℕ → ℝ} (hF : ∀ k, F (k + 1) = F k + a (k + 1))
    {M N : ℕ} (hMN : M ≤ N) :
    ∑ k ∈ Ioc M N, a k * f k
      = F N * f N - F M * f M + ∑ k ∈ Ico M N, F k * (f k - f (k + 1)) := by
  induction N, hMN using Nat.le_induction with
  | base => simp
  | succ N hMN ih =>
    rw [Finset.sum_Ioc_succ_top hMN, ih, Finset.sum_Ico_succ_top hMN, hF N]
    ring

/-- Telescoping on `[M, N)`. -/
theorem sum_Ico_telescope (g : ℕ → ℝ) {M N : ℕ} (h : M ≤ N) :
    ∑ k ∈ Ico M N, (g k - g (k + 1)) = g M - g N := by
  induction N, h using Nat.le_induction with
  | base => simp
  | succ N hMN ih => rw [Finset.sum_Ico_succ_top hMN, ih]; ring

theorem primeLogSum_succ (k : ℕ) :
    primeLogSum (k + 1)
      = primeLogSum k + (if (k + 1).Prime then Real.log ((k + 1 : ℕ) : ℝ) / ((k + 1 : ℕ) : ℝ)
          else 0) := by
  rw [primeLogSum, primeLogSum, Finset.sum_filter, Finset.sum_filter,
    Finset.sum_Ioc_succ_top (Nat.zero_le k)]

/-- One summation-by-parts term against the telescoping `log log`. -/
theorem sbp_term_bound {k : ℕ} (hk : 2 ≤ k) {F : ℝ} (hF : |F - Real.log k| ≤ 3) :
    |F * (1 / Real.log k - 1 / Real.log ((k + 1 : ℕ) : ℝ))
        - (Real.log (Real.log ((k + 1 : ℕ) : ℝ)) - Real.log (Real.log k))|
      ≤ 4 * (1 / Real.log k - 1 / Real.log ((k + 1 : ℕ) : ℝ)) := by
  have hkR : (2 : ℝ) ≤ k := by exact_mod_cast hk
  have hk1 : ((k + 1 : ℕ) : ℝ) = (k : ℝ) + 1 := by push_cast; ring
  rw [hk1]
  set a := Real.log k with ha
  set b := Real.log ((k : ℝ) + 1) with hb
  have ha0 : 0 < a := Real.log_pos (by linarith)
  have hab : a < b := Real.log_lt_log (by linarith) (by linarith)
  have hb0 : 0 < b := lt_trans ha0 hab
  have hba1 : b - a ≤ 1 := by
    have hkpos : (0 : ℝ) < k := by linarith
    have h1 : b - a = Real.log (((k : ℝ) + 1) / k) := by
      rw [Real.log_div (by positivity) hkpos.ne']
    have h2 := Real.log_le_sub_one_of_pos (show (0 : ℝ) < ((k : ℝ) + 1) / k by positivity)
    have h3 : ((k : ℝ) + 1) / k - 1 = 1 / k := by field_simp; ring
    have h4 : (1 : ℝ) / k ≤ 1 := by rw [div_le_one hkpos]; linarith
    linarith
  have hΔeq : 1 / a - 1 / b = (b - a) / (a * b) := by field_simp
  have hΔ0 : 0 ≤ 1 / a - 1 / b := by
    rw [hΔeq]; apply div_nonneg <;> nlinarith
  have hlow : 1 - a / b ≤ Real.log (b / a) := by
    have h := Real.one_sub_inv_le_log_of_pos (show 0 < b / a by positivity)
    rwa [inv_div] at h
  have hup : Real.log (b / a) ≤ b / a - 1 := Real.log_le_sub_one_of_pos (by positivity)
  have hlogdiv : Real.log b - Real.log a = Real.log (b / a) := (Real.log_div hb0.ne' ha0.ne').symm
  have haΔ : a * (1 / a - 1 / b) = 1 - a / b := by field_simp
  have hD1 : b / a - 1 - (1 - a / b) ≤ 1 / a - 1 / b := by
    have h1 : b / a - 1 - (1 - a / b) = (b - a) ^ 2 / (a * b) := by field_simp
    rw [h1, hΔeq]
    apply div_le_div_of_nonneg_right _ (by positivity)
    nlinarith
  have hRΔ : |(F - a) * (1 / a - 1 / b)| ≤ 3 * (1 / a - 1 / b) := by
    rw [abs_mul, abs_of_nonneg hΔ0]
    exact mul_le_mul_of_nonneg_right hF hΔ0
  have heq : F * (1 / a - 1 / b) - (Real.log b - Real.log a)
      = (F - a) * (1 / a - 1 / b) - (Real.log (b / a) - (1 - a / b)) := by
    rw [hlogdiv]; linear_combination haΔ
  rw [heq]
  rw [abs_le] at hRΔ ⊢
  constructor <;> linarith [hRΔ.1, hRΔ.2]

/-- **Mertens' second theorem, difference form**, with an explicit constant:
for `2 ≤ M ≤ N`,
`|∑_{M < p ≤ N} 1/p - (log log N - log log M)| ≤ 10 / log M`. -/
theorem abs_sum_inv_primes_sub_loglog_le {M N : ℕ} (hM : 2 ≤ M) (hMN : M ≤ N) :
    |∑ p ∈ (Ioc M N).filter Nat.Prime, (1 : ℝ) / p
        - (Real.log (Real.log N) - Real.log (Real.log M))|
      ≤ 10 / Real.log M := by
  set f : ℕ → ℝ := fun k => 1 / Real.log k with hf
  set a : ℕ → ℝ := fun k => if k.Prime then Real.log k / k else 0 with ha
  set LL : ℕ → ℝ := fun k => Real.log (Real.log k) with hLL
  have hF : ∀ k, primeLogSum (k + 1) = primeLogSum k + a (k + 1) := fun k => primeLogSum_succ k
  have hMR : (2 : ℝ) ≤ M := by exact_mod_cast hM
  have hNR : (2 : ℝ) ≤ N := by exact_mod_cast (le_trans hM hMN)
  have hlogM : 0 < Real.log M := Real.log_pos (by linarith)
  have hlogN : 0 < Real.log N := Real.log_pos (by linarith)
  have hlogMN : Real.log M ≤ Real.log N :=
    Real.log_le_log (by linarith) (by exact_mod_cast hMN)
  have hsum : ∑ p ∈ (Ioc M N).filter Nat.Prime, (1 : ℝ) / p = ∑ k ∈ Ioc M N, a k * f k := by
    rw [Finset.sum_filter]
    apply Finset.sum_congr rfl
    intro k hk
    have hk2 : 2 ≤ k := by have := (Finset.mem_Ioc.mp hk).1; omega
    have hkR : (2 : ℝ) ≤ k := by exact_mod_cast hk2
    have hlog : Real.log k ≠ 0 := (Real.log_pos (by linarith)).ne'
    have hk0 : (k : ℝ) ≠ 0 := by positivity
    simp only [ha, hf]
    split_ifs
    · field_simp
    · simp
  have hsbp := sum_Ioc_mul_eq_sub_add_sum (a := a) (F := primeLogSum) (f := f) hF hMN
  have hint : |∑ k ∈ Ico M N, primeLogSum k * (f k - f (k + 1)) - (LL N - LL M)|
      ≤ 4 * (f M - f N) := by
    have htelLL := sum_Ico_telescope (fun k => - LL k) hMN
    have htelf := sum_Ico_telescope f hMN
    have hLLsum : LL N - LL M = ∑ k ∈ Ico M N, (LL (k + 1) - LL k) := by
      have : ∑ k ∈ Ico M N, (LL (k + 1) - LL k) = ∑ k ∈ Ico M N, (-LL k - -LL (k + 1)) := by
        apply Finset.sum_congr rfl; intro k _; ring
      rw [this, htelLL]; ring
    rw [hLLsum, ← Finset.sum_sub_distrib]
    calc |∑ k ∈ Ico M N, (primeLogSum k * (f k - f (k + 1)) - (LL (k + 1) - LL k))|
        ≤ ∑ k ∈ Ico M N, |primeLogSum k * (f k - f (k + 1)) - (LL (k + 1) - LL k)| :=
          Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ k ∈ Ico M N, 4 * (f k - f (k + 1)) := by
          apply Finset.sum_le_sum
          intro k hk
          have hk2 : 2 ≤ k := le_trans hM (Finset.mem_Ico.mp hk).1
          exact sbp_term_bound hk2 (abs_primeLogSum_sub_log_le k (by omega))
      _ = 4 * (f M - f N) := by rw [← Finset.mul_sum, htelf]
  have hbd : ∀ n : ℕ, 2 ≤ n → M ≤ n → |primeLogSum n * f n - 1| ≤ 3 / Real.log M := by
    intro n hn hMn
    have hnR : (2 : ℝ) ≤ n := by exact_mod_cast hn
    have hlogn : 0 < Real.log n := Real.log_pos (by linarith)
    have hlogMn : Real.log M ≤ Real.log n :=
      Real.log_le_log (by linarith) (by exact_mod_cast hMn)
    have heq : primeLogSum n * f n - 1 = (primeLogSum n - Real.log n) / Real.log n := by
      simp only [hf]; field_simp
    rw [heq, abs_div, abs_of_pos hlogn]
    calc |primeLogSum n - Real.log n| / Real.log n ≤ 3 / Real.log n := by
          apply div_le_div_of_nonneg_right (abs_primeLogSum_sub_log_le n (by omega)) hlogn.le
      _ ≤ 3 / Real.log M := by
          apply div_le_div_of_nonneg_left (by norm_num) hlogM hlogMn
  have hbN := hbd N (le_trans hM hMN) hMN
  have hbM := hbd M hM le_rfl
  have hfN : 0 ≤ f N := by simp only [hf]; positivity
  have hfM : f M = 1 / Real.log M := rfl
  rw [hsum, hsbp]
  have hsplit : primeLogSum N * f N - primeLogSum M * f M
        + ∑ k ∈ Ico M N, primeLogSum k * (f k - f (k + 1)) - (LL N - LL M)
      = (primeLogSum N * f N - 1) - (primeLogSum M * f M - 1)
        + (∑ k ∈ Ico M N, primeLogSum k * (f k - f (k + 1)) - (LL N - LL M)) := by ring
  change |primeLogSum N * f N - primeLogSum M * f M
        + ∑ k ∈ Ico M N, primeLogSum k * (f k - f (k + 1)) - (LL N - LL M)| ≤ 10 / Real.log M
  rw [hsplit]
  have h10 : 10 / Real.log M = 3 / Real.log M + 3 / Real.log M + 4 * (1 / Real.log M) := by
    field_simp; norm_num
  rw [h10]
  calc |(primeLogSum N * f N - 1) - (primeLogSum M * f M - 1)
        + (∑ k ∈ Ico M N, primeLogSum k * (f k - f (k + 1)) - (LL N - LL M))|
      ≤ |primeLogSum N * f N - 1| + |primeLogSum M * f M - 1|
        + |∑ k ∈ Ico M N, primeLogSum k * (f k - f (k + 1)) - (LL N - LL M)| := by
        have := abs_add_le ((primeLogSum N * f N - 1) - (primeLogSum M * f M - 1))
          (∑ k ∈ Ico M N, primeLogSum k * (f k - f (k + 1)) - (LL N - LL M))
        have := abs_sub (primeLogSum N * f N - 1) (primeLogSum M * f M - 1)
        linarith
    _ ≤ 3 / Real.log M + 3 / Real.log M + 4 * (1 / Real.log M) := by
        have : 4 * (f M - f N) ≤ 4 * (1 / Real.log M) := by rw [hfM]; linarith
        linarith

/-- The number of primes in `(M, x]` is at most `x log 4 / log M`. -/
theorem card_primes_Ioc_mul_log_le {M x : ℕ} (hM : 1 ≤ M) :
    (((Ioc M x).filter Nat.Prime).card : ℝ) * Real.log M ≤ Real.log 4 * x := by
  have hMR : (1 : ℝ) ≤ M := by exact_mod_cast hM
  calc (((Ioc M x).filter Nat.Prime).card : ℝ) * Real.log M
      = ∑ _p ∈ (Ioc M x).filter Nat.Prime, Real.log M := by
        rw [Finset.sum_const, nsmul_eq_mul]
    _ ≤ ∑ p ∈ (Ioc M x).filter Nat.Prime, Real.log p := by
        apply Finset.sum_le_sum
        intro p hp
        have hMp : M < p := (Finset.mem_Ioc.mp (Finset.mem_filter.mp hp).1).1
        exact Real.log_le_log (by linarith) (by exact_mod_cast hMp.le)
    _ ≤ ∑ p ∈ (Ioc 0 x).filter Nat.Prime, Real.log p := by
        apply Finset.sum_le_sum_of_subset_of_nonneg
        · exact Finset.filter_subset_filter _ (Finset.Ioc_subset_Ioc_left (Nat.zero_le M))
        · intro p hp _
          exact Real.log_nonneg (by exact_mod_cast (Finset.mem_filter.mp hp).2.one_le)
    _ ≤ Real.log 4 * x := sum_log_primes_le x

end ErdosProblems.Shared.Mertens

#print axioms ErdosProblems.Shared.Mertens.mertens_first
#print axioms ErdosProblems.Shared.Mertens.abs_sum_inv_primes_sub_loglog_le
#print axioms ErdosProblems.Shared.Mertens.card_primes_Ioc_mul_log_le
