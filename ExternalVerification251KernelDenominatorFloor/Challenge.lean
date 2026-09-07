/-
Copyright (c) 2026 Will Cook. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Will Cook
-/
import Mathlib

/-!
# Trusted challenge for the Erdős #251 kernel-decided denominator floor

`S = Σ_{i ≥ 0} p_i / 2^{i+1}` is the zero-based prime series and `S - 2` is the
prime-gap series of Erdős Problem 251.  This Mathlib-only statement exposes an
unconditional denominator floor for both series together with the
kernel-evaluable certificate that produces it.

`noSmallDivisor`, `isPrimeTD` and `primeSumLoop` are the trial-division sieve
that runs inside the kernel: `primeSumLoop B X` returns the number of primes
below `X` together with the scaled prefix `Σ_{i < π(X)} p_i 2^{B-i-1}`.
`certCheck c u v u' v' X` packages six integer conditions on that output: the
prime count equals `c`, `v` and `v'` are positive, the Farey determinant
`u' v = u v' + 1` holds, and two inequalities place `S` strictly inside the
interval from `u/v` to `u'/v'` once the omitted tail is bounded by
`5000 (c+1)^4 / 2^{c+1}`.  The certificate constants are `c = 1229`,
`X = 10000`, and the four explicit Farey numerators and denominators of 177 and
178 digits recorded below.

The floor is `2^589`, which exceeds `10^177`.  A lower bound on the denominator
of a rational representation is compatible with rationality of either series.
This package supplies no irrationality theorem and Erdős Problem 251 is not
decided here.
-/

open scoped BigOperators

namespace Erdos249257.ExternalVerification251KernelDenominatorFloor

/-- Zero-based prime enumeration. -/
noncomputable def prime0 (n : ℕ) : ℕ :=
  Nat.nth Nat.Prime n

/-- Zero-based consecutive prime gap. -/
noncomputable def primeGap0 (n : ℕ) : ℕ :=
  prime0 (n + 1) - prime0 n

/-- The real term in the normalized zero-based prime series. -/
noncomputable def primeDyadicTerm (n : ℕ) : ℝ :=
  (prime0 n : ℝ) / 2 ^ (n + 1)

/-- The real term in the corresponding consecutive-prime-gap series. -/
noncomputable def primeGapDyadicTerm (n : ℕ) : ℝ :=
  (primeGap0 n : ℝ) / 2 ^ (n + 1)

/-- `noSmallDivisor m fuel k = true` iff no `j` with `k ≤ j < k + fuel` and
`j * j ≤ m` divides `m`. -/
def noSmallDivisor (m : ℕ) : ℕ → ℕ → Bool
  | 0, _ => true
  | fuel + 1, k =>
      if m < k * k then true
      else if m % k == 0 then false
      else noSmallDivisor m fuel (k + 1)

/-- Trial-division primality test, kernel-evaluable. -/
def isPrimeTD (m : ℕ) : Bool := decide (2 ≤ m) && noSmallDivisor m m 2

/-- After processing all `m < X`: `(π(X), Σ_{i < π(X)} p_i 2^{B-i-1})`. -/
def primeSumLoop (B : ℕ) : ℕ → ℕ × ℕ
  | 0 => (0, 0)
  | m + 1 =>
      let s := primeSumLoop B m
      if isPrimeTD m then (s.1 + 1, s.2 + m * 2 ^ (B - s.1 - 1)) else s

/-- The six integer conditions the kernel decides. -/
def certCheck (c u v u' v' X : ℕ) : Bool :=
  let s := primeSumLoop c X
  (s.1 == c) && decide (0 < v) && decide (0 < v') && (u' * v == u * v' + 1) &&
    decide (u * 2 ^ c < s.2 * v) &&
    decide ((2 * s.2 + 5000 * (c + 1) ^ 4) * v' < u' * 2 ^ (c + 1))

def certX : ℕ := 10000

def certC : ℕ := 1229

def certU : ℕ :=
  8065641857152652932176019632186898003271162829171466334827308360779441527871744503350940785598890336998852555074615973558897922500842023448210201391609566636587897181681526620217

def certV : ℕ :=
  2194945124413663232143970924541263312422069524635615360518424707735195822181683072018928990483166295508439269024868312162917239885377332351730406072544968385302138677814423351745

def certU' : ℕ :=
  653943710149816262688241189247090522210826000856855544597530261633155217846686899097127598765624846200590981384174695232839888185316374272333277389611483117334000493867584923912

def certV' : ℕ :=
  177961107578986655119842724162170963012013632328159817663784906052492297355019687649040361529707294916566508739385806203025466313389810291243786005499164537499383612081805160767


/-- The kernel re-runs the `10^4` trial-division sieve and decides the six
conditions on the certificate literals. -/
theorem cert_10000 : certCheck certC certU certV certU' certV' certX = true := by
  sorry

/-- A passing certificate at any truncation index `c ≥ 9` forces every rational
`a / b` equal to the prime series to satisfy `v + v' ≤ b`. -/
theorem den_bound_of_certCheck (c u v u' v' X : ℕ) (hc : 9 ≤ c)
    (h : certCheck c u v u' v' X = true) :
    ∀ (a : ℤ) (b : ℕ), 0 < b → (∑' n, primeDyadicTerm n) = a / b → v + v' ≤ b := by
  sorry

/-- Every rational `a / b` equal to `S` has `b ≥ 2^589 > 10^177`. -/
theorem kernel_denominator_floor (a : ℤ) (b : ℕ) (hb : 0 < b)
    (hS : (∑' n, primeDyadicTerm n) = a / b) : (2 ^ 589 : ℕ) ≤ b := by
  sorry

/-- The same floor for the prime-gap series `S - 2` of Erdős #251. -/
theorem kernel_denominator_floor_primeGap (a : ℤ) (b : ℕ) (hb : 0 < b)
    (hS : (∑' n, primeGapDyadicTerm n) = a / b) : (2 ^ 589 : ℕ) ≤ b := by
  sorry

end Erdos249257.ExternalVerification251KernelDenominatorFloor
