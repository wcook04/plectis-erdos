import Mathlib

/-!
# Arithmetic core for pulses after finitely many dilations

ROUND-SIX CANDIDATE: NOT COMPILED. Target: Mathlib / Lean 4.29.1.

The ordinary proof supplies CRT/Dirichlet witnesses and the signed-series
consumer separately. This file supplies centre isolation and neighbour killing.
No theorem below asserts existence of the CRT witnesses, a summability result,
or the irrationality of the unreduced totient series.
-/

namespace ErdosProblems.Erdos249.FiniteDilationPulseCore

open scoped BigOperators

/-- Reindexing a finite sum of series at bases b^d gives these coefficients. -/
def mixedCoefficient (D : Finset ℕ) (g : ℕ → ℕ → ℤ) (m N : ℕ) : ℤ :=
  ∑ d ∈ D, if d ∣ N then g d (Nat.totient (N / d) % m) else 0

/-- A divisor from the finite family cannot survive at the smallest prime centre
unless it is the smallest dilation itself. -/
theorem divisor_at_minimal_prime_centre
    {d δ p : ℕ} (hp : p.Prime) (hd : 0 < d) (hδ : 0 < δ)
    (hmin : δ ≤ d) (hsmall : d < p) (hdiv : d ∣ δ * p) : d = δ := by
  have hnot : ¬ p ∣ d := by
    intro h
    have := Nat.le_of_dvd hd h
    omega
  have hcop : Nat.Coprime d p := (hp.coprime_iff_not_dvd.mpr hnot).symm
  have hdiv' : d ∣ p * δ := by simpa only [Nat.mul_comm] using hdiv
  have hdδ : d ∣ δ := hcop.dvd_of_dvd_mul_left hdiv'
  exact Nat.le_antisymm (Nat.le_of_dvd hδ hdδ) hmin

/-- The central coefficient is exactly the selected coefficient. -/
theorem mixedCoefficient_at_prime_centre
    (D : Finset ℕ) (g : ℕ → ℕ → ℤ) (m δ p : ℕ)
    (hδD : δ ∈ D) (hδ : 0 < δ) (hp : p.Prime)
    (hpos : ∀ d ∈ D, 0 < d)
    (hmin : ∀ d ∈ D, δ ≤ d)
    (hsmall : ∀ d ∈ D, d < p) :
    mixedCoefficient D g m (δ * p) = g δ ((p - 1) % m) := by
  classical
  unfold mixedCoefficient
  rw [Finset.sum_eq_single δ]
  · simp only [dvd_mul_right, if_true]
    rw [Nat.mul_div_cancel_left p hδ, Nat.totient_prime hp]
  · intro d hd hne
    have hnot : ¬ d ∣ δ * p := by
      intro hdiv
      exact hne (divisor_at_minimal_prime_centre hp (hpos d hd) hδ
        (hmin d hd) (hsmall d hd) hdiv)
    simp only [hnot, if_false]
  · intro hnot
    exact (hnot hδD).elim

/-- A prime divisor survives division by a coprime dilation. -/
theorem prime_dvd_quotient
    {q d N : ℕ} (hqd : Nat.Coprime q d) (hdN : d ∣ N) (hqN : q ∣ N) :
    q ∣ N / d := by
  have hfactor : d * (N / d) = N := Nat.mul_div_cancel' hdN
  have hprod : q ∣ d * (N / d) := by rw [hfactor]; exact hqN
  exact hqd.dvd_of_dvd_mul_left hprod

/-- A forced prime q with m | q-1 kills the totient residue of the quotient. -/
theorem modulus_dvd_quotient_totient
    {m q d N : ℕ} (hq : q.Prime) (hm : m ∣ q - 1)
    (hqd : Nat.Coprime q d) (hdN : d ∣ N) (hqN : q ∣ N) :
    m ∣ Nat.totient (N / d) := by
  have hdiv := Nat.totient_dvd_of_dvd (prime_dvd_quotient hqd hdN hqN)
  rw [Nat.totient_prime hq] at hdiv
  exact hm.trans hdiv

/-- One auxiliary prime simultaneously kills all active dilation summands. -/
theorem mixedCoefficient_eq_zero_of_auxiliary_prime
    (D : Finset ℕ) (g : ℕ → ℕ → ℤ) (m N q : ℕ)
    (hq : q.Prime) (hm : m ∣ q - 1) (hqN : q ∣ N)
    (hcop : ∀ d ∈ D, Nat.Coprime q d)
    (hzero : ∀ d ∈ D, g d 0 = 0) :
    mixedCoefficient D g m N = 0 := by
  classical
  unfold mixedCoefficient
  apply Finset.sum_eq_zero
  intro d hd
  by_cases hdN : d ∣ N
  · rw [if_pos hdN]
    have hdiv := modulus_dvd_quotient_totient hq hm (hcop d hd) hdN hqN
    rw [Nat.mod_eq_zero_of_dvd hdiv, hzero d hd]
  · rw [if_neg hdN]

end ErdosProblems.Erdos249.FiniteDilationPulseCore
