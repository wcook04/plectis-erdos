/-
Copyright (c) 2026 Will Cook. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Will Cook
-/
import Mathlib

/-!
# Trusted challenge for the residue-class totient series in Erdős #249

This Mathlib-only statement isolates the special-value irrationality theorem
for fixed-resolution observables of the totient word, together with the
Diophantine core and the arithmetic supply that produce it.

The compared family concerns the reduced sequences `φ n % m`.  The letter maps
are integer valued, the resolution `m` is fixed, and the binary value is
`∑ f (φ n % m) / 2 ^ n`.  The headline consequence is the irrationality of the
least-residue series `A_m = ∑ (φ n % m) / 2 ^ n` for every `m ≥ 3`.

No theorem here concerns `∑ φ n / 2 ^ n` itself, so the package does not solve
Erdős Problem 249.
-/

namespace Erdos249257.ExternalVerification249ResidueClassTotientSeries

/-- The binary value `∑ a n / 2 ^ n` of an integer coefficient sequence. -/
noncomputable def dyadicValue (a : ℕ → ℤ) : ℝ := ∑' n : ℕ, (a n : ℝ) / 2 ^ n

/-- The binary value of a fixed-resolution observable of the totient word. -/
noncomputable def totientObservableValue (f : ℕ → ℤ) (m : ℕ) : ℝ :=
  ∑' n : ℕ, ((f (Nat.totient n % m) : ℤ) : ℝ) / 2 ^ n

/-- `A_m = ∑_{n} (φ n mod m) / 2 ^ n`, least nonnegative residues. -/
noncomputable def totientResidueValue (m : ℕ) : ℝ :=
  ∑' n : ℕ, ((Nat.totient n % m : ℕ) : ℝ) / 2 ^ n

/-- **Isolated pulse separation.**  A bounded integer sequence with a nonzero
letter `t` at `p = N + 1 + L` and a two-sided block of `L` zeros around it keeps
`q * dyadicValue a` at an explicit distance from every integer. -/
theorem isolated_pulse_separation {a : ℕ → ℤ} {C : ℝ} (hC : ∀ n, |(a n : ℝ)| ≤ C)
    {N L q : ℕ} {t : ℤ} (hq : 1 ≤ q) (hL : 2 * (q : ℝ) * C < 2 ^ L)
    (hcentre : a (N + 1 + L) = t) (ht : t ≠ 0)
    (hzero : ∀ i, i ≤ 2 * L → i ≠ L → a (N + 1 + i) = 0) (k : ℤ) :
    (q : ℝ) * (|(t : ℝ)| - C / 2 ^ L) / 2 ^ (N + 1 + L)
      ≤ |(q : ℝ) * dyadicValue a - (k : ℝ)| := by
  sorry

/-- Arbitrarily long two-sided isolated pulses force irrationality of the binary
value. -/
theorem irrational_dyadicValue_of_pulses {a : ℕ → ℤ} {C : ℝ} (hC : ∀ n, |(a n : ℝ)| ≤ C)
    (hpulse : ∀ L : ℕ, ∃ p : ℕ, L + 1 < p ∧ a p ≠ 0 ∧
      ∀ j, 0 < j → j ≤ L → a (p - j) = 0 ∧ a (p + j) = 0) :
    Irrational (dyadicValue a) := by
  sorry

/-- **Two-sided prime isolation.**  For `m ≥ 2` and any `r` with
`gcd (r + 1, m) = 1` there are arbitrarily large primes `p` with
`φ p ≡ r [MOD m]` and `m ∣ φ (p ± j)` for every `0 < j ≤ L`. -/
theorem two_sided_prime_isolation {m : ℕ} (hm : 2 ≤ m) (L N r : ℕ)
    (hr : Nat.Coprime (r + 1) m) :
    ∃ p : ℕ, N < p ∧ L + 1 < p ∧ p.Prime ∧ Nat.totient p ≡ r [MOD m] ∧
      ∀ j, 0 < j → j ≤ L → m ∣ Nat.totient (p - j) ∧ m ∣ Nat.totient (p + j) := by
  sorry

/-- **The special-value irrationality theorem for fixed-resolution observables.**
If `f` vanishes at the zero residue and is nonzero at some residue `r < m` with
`gcd (r + 1, m) = 1`, then `∑ f (φ n mod m) / 2 ^ n` is irrational. -/
theorem irrational_totientObservable {m : ℕ} (hm : 2 ≤ m) (f : ℕ → ℤ) (hf0 : f 0 = 0)
    {r : ℕ} (hr : r < m) (hcop : Nat.Coprime (r + 1) m) (hfr : f r ≠ 0) :
    Irrational (totientObservableValue f m) := by
  sorry

/-- At dyadic resolution `2 ^ k` every integer-valued letter map that vanishes on
the zero residue and is nonzero on some even residue has irrational binary
value. -/
theorem fixed_resolution_observable_irrational {k : ℕ} (hk : 1 ≤ k) (f : ℕ → ℤ)
    (hf0 : f 0 = 0) {r : ℕ} (hr : r < 2 ^ k) (hreven : r % 2 = 0) (hfr : f r ≠ 0) :
    Irrational (totientObservableValue f (2 ^ k)) := by
  sorry

/-- For every `m ≥ 3` the least-residue totient series
`A_m = ∑ (φ n mod m) / 2 ^ n` is irrational. -/
theorem residue_series_irrational {m : ℕ} (hm : 3 ≤ m) :
    Irrational (totientResidueValue m) := by
  sorry

end Erdos249257.ExternalVerification249ResidueClassTotientSeries
