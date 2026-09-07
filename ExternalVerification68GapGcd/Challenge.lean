/-
Copyright (c) 2026 Will Cook. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Will Cook
-/
import Mathlib

/-!
# Trusted challenge for the factorial-gap quotient gcd and terminal-block segment

For `2 ≤ i < j` the gcd of `i! - 1` and `j! - 1` divides `j!/i! - 1`, is bounded
above by that quotient, and the quotient itself is smaller than `j ^ (j - i)`.

For a terminal block of `k` indices ending at `N`, the sum of the logarithms of
the moduli `n! - 1` is bounded by the logarithm of the common denominator
`lcm_{2 ≤ d ≤ N} (d! - 1)` plus a collision term of order `binom(k+1, 3) log N`.

Both statements are finite arithmetic statements about factorial gaps.  Neither
decides the irrationality of the associated series, and neither settles Erdős
Problem 68.
-/

namespace Erdos249257.ExternalVerification68GapGcd

open scoped BigOperators

/-- The common denominator of the factorial gaps through `D`. -/
def channelLCM (D : ℕ) : ℕ :=
  (Finset.Icc 2 D).lcm (fun d => d.factorial - 1)

/-- Divisibility, the resulting upper bound, and the strict quotient bound. -/
theorem factorial_gap_gcd {i j : ℕ} (hi : 2 ≤ i) (hij : i < j) :
    Nat.gcd (i.factorial - 1) (j.factorial - 1) ∣
        j.factorial / i.factorial - 1 ∧
    Nat.gcd (i.factorial - 1) (j.factorial - 1) ≤
        j.factorial / i.factorial - 1 ∧
    j.factorial / i.factorial - 1 < j ^ (j - i) := by
  sorry

/-- The terminal-block logarithmic segment inequality with its collision term. -/
theorem segment_inequality {N k : ℕ} (hk : 2 ≤ k) (hkN : k ≤ N - 1) :
    (∑ n ∈ Finset.Icc (N - k + 1) N,
        Real.log ((n.factorial - 1 : ℕ) : ℝ)) ≤
      Real.log (channelLCM N : ℝ) +
        ((k + 1).choose 3 : ℝ) * Real.log (N : ℝ) := by
  sorry

end Erdos249257.ExternalVerification68GapGcd
