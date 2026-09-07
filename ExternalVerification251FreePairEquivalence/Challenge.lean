/-
Copyright (c) 2026 Will Cook. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Will Cook
-/
import Mathlib

/-!
# Trusted challenge for the Erdős #251 free-pair equivalence

This Mathlib-only statement exposes an unconditional equivalence whose left
side is Erdős Problem 251 itself: the dyadic series over the actual
consecutive prime gaps is irrational exactly when, for every positive modulus
`t` and every cutoff, two indices beyond the cutoff congruent modulo `t` have
a nonintegral scaled-tail difference.  The offset in the pair is free.

The abstract layer states the same equivalence for every real integer-digit
dyadic tail orbit, identifies the free-pair criterion with the fixed-offset
cofinal criterion, and pins the integral pairs of a rational orbit to a single
congruence lattice whose modulus is the multiplicative order of `2` modulo the
stabilised odd denominator.

No declaration here produces a nonintegral congruent pair.  The equivalence
supplies no free pair for the actual prime gaps, so Erdős Problem 251 is
untouched.
-/

open scoped BigOperators

namespace Erdos249257.ExternalVerification251FreePairEquivalence

noncomputable def prime0 (n : ℕ) : ℕ := Nat.nth Nat.Prime n

noncomputable def primeGap0 (n : ℕ) : ℕ := prime0 (n + 1) - prime0 n

noncomputable def primeGapDyadicTerm (n : ℕ) : ℝ :=
  (primeGap0 n : ℝ) / 2 ^ (n + 1)

def DyadicTailRecurrence (g : ℕ → ℤ) (T : ℕ → ℚ) : Prop :=
  ∀ N, T (N + 1) = 2 * T N - g (N + 1)

def RealDyadicTailRecurrence (g : ℕ → ℤ) (T : ℕ → ℝ) : Prop :=
  ∀ N, T (N + 1) = 2 * T N - g (N + 1)

def realTailShift (T : ℕ → ℝ) (h N : ℕ) : ℝ :=
  T (N + h) - T N

def RatIntegral (x : ℚ) : Prop :=
  ∃ z : ℤ, x = z

def RealIntegral (x : ℝ) : Prop :=
  ∃ z : ℤ, x = z

/-- The fixed-offset cofinal criterion: every positive shift length misses
integrality at arbitrarily late basepoints. -/
def CofinalNonintegralTailShifts (T : ℕ → ℝ) : Prop :=
  ∀ h, 0 < h → ∀ N₀, ∃ N, N₀ ≤ N ∧
    ¬RealIntegral (realTailShift T h N)

/-- The free-pair criterion: for every positive modulus and every cutoff,
some pair of indices beyond the cutoff, congruent modulo the modulus, has a
nonintegral tail difference. -/
def CofinalFreePairNonintegral (T : ℕ → ℝ) : Prop :=
  ∀ t : ℕ, 0 < t → ∀ N₀ : ℕ, ∃ N M : ℕ, N₀ ≤ N ∧ N₀ ≤ M ∧ N ≡ M [MOD t] ∧
    ¬ RealIntegral (T M - T N)

/-- The real scaled tail of the actual prime-gap series after the first `N+1`
gaps. -/
noncomputable def primeGapRealTail (N : ℕ) : ℝ :=
  2 ^ (N + 1) * ∑' k : ℕ, primeGapDyadicTerm (k + (N + 1))

/-- **Erdős #251 in free-pair form.**  The consecutive-prime-gap dyadic series
is irrational exactly when, for every positive modulus `t` and every cutoff,
two tail indices beyond the cutoff and congruent modulo `t` have a nonintegral
scaled-tail difference.  Nothing here produces such pairs. -/
theorem irrational_primeGap_tsum_iff_cofinalFreePairNonintegral :
    Irrational (∑' n : ℕ, primeGapDyadicTerm n) ↔
      CofinalFreePairNonintegral primeGapRealTail := by
  sorry

/-- The same equivalence for every real integer-digit dyadic tail orbit. -/
theorem irrational_initial_iff_cofinalFreePairNonintegral {g : ℕ → ℤ} {T : ℕ → ℝ}
    (hrec : RealDyadicTailRecurrence g T) :
    Irrational (T 0) ↔ CofinalFreePairNonintegral T := by
  sorry

/-- The free-pair criterion and the fixed-offset criterion agree on every
integer-digit orbit. -/
theorem cofinalFreePairNonintegral_iff_cofinalNonintegralTailShifts
    {g : ℕ → ℤ} {T : ℕ → ℝ} (hrec : RealDyadicTailRecurrence g T) :
    CofinalFreePairNonintegral T ↔ CofinalNonintegralTailShifts T := by
  sorry

/-- Every rational-valued integer-digit dyadic tail orbit has a cutoff and a
positive modulus beyond which the integral pairs are exactly the congruent
pairs. -/
theorem exists_free_pair_lattice {g : ℕ → ℤ} {T : ℕ → ℚ}
    (hrec : DyadicTailRecurrence g T) :
    ∃ N₀ t : ℕ, 0 < t ∧ ∀ N M : ℕ, N₀ ≤ N → N₀ ≤ M →
      (RatIntegral (T M - T N) ↔ N ≡ M [MOD t]) := by
  sorry

/-- The modulus of that lattice is the multiplicative order of `2` modulo the
stabilised odd denominator, and the offset is free. -/
theorem free_pair_integral_iff_modEq {g : ℕ → ℤ} {T : ℕ → ℚ}
    (hrec : DyadicTailRecurrence g T) {N₀ : ℕ} (hodd : Odd (T N₀).den)
    {N M : ℕ} (hN : N₀ ≤ N) (hM : N₀ ≤ M) :
    RatIntegral (T M - T N) ↔ N ≡ M [MOD orderOf (2 : ZMod (T N₀).den)] := by
  sorry

/-- The real prime-gap tail obeys the integer-digit dyadic recurrence with the
actual consecutive prime gaps as digits. -/
theorem primeGapRealTail_recurrence :
    RealDyadicTailRecurrence (fun n => (primeGap0 n : ℤ)) primeGapRealTail := by
  sorry

/-- The initial real tail is `2S - 1` with `S` the prime-gap series. -/
theorem primeGapRealTail_zero :
    primeGapRealTail 0 = 2 * (∑' n : ℕ, primeGapDyadicTerm n) - 1 := by
  sorry

end Erdos249257.ExternalVerification251FreePairEquivalence
