-- SPDX-FileCopyrightText: 2026 Will Cook
-- SPDX-License-Identifier: Apache-2.0
import Mathlib.Data.Nat.Totient
import Mathlib.NumberTheory.ArithmeticFunction.Misc
import Mathlib.Data.Nat.Prime.Infinite
import Mathlib.Data.Real.Archimedean
import Mathlib.Tactic

/-!
# Multiplicative rigidity under bounded perturbation

A real sequence that is multiplicative on coprime arguments and lies within a fixed distance of
a multiplicative sequence `f` equals `f`, provided `f` is unbounded on the integers coprime to
each fixed `n ≥ 1` (`eq_of_multiplicative_of_bounded_sub`).  Euler's totient and the divisor
count satisfy the unboundedness hypothesis, so each is the only multiplicative sequence at
bounded distance from itself (`eq_totient_of_multiplicative_of_bounded_sub`,
`eq_card_divisors_of_multiplicative_of_bounded_sub`).  Bounded rounding of a coefficient
sequence therefore cannot keep multiplicativity.
-/

noncomputable section

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

#print axioms ErdosProblems.Synthesis.MultiplicativeRigidity.eq_of_multiplicative_of_bounded_sub
#print axioms ErdosProblems.Synthesis.MultiplicativeRigidity.totient_unbounded_coprime
#print axioms ErdosProblems.Synthesis.MultiplicativeRigidity.eq_totient_of_multiplicative_of_bounded_sub
#print axioms ErdosProblems.Synthesis.MultiplicativeRigidity.card_divisors_unbounded_coprime
#print axioms ErdosProblems.Synthesis.MultiplicativeRigidity.eq_card_divisors_of_multiplicative_of_bounded_sub
