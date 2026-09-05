import Mathlib

/-!
# Squared Lambert identities

Independent statements for the constant and totient weights. Both sums range
over positive integers. These interfaces assert identities, without importing
the separate q-Padé irrationality theorem.
-/

namespace Erdos249257.ExternalVerification249SquaredLambert

theorem tsum_one_div_mersenne_sq_eq_sigma_sub_tau_series :
    ∑' d : ℕ+, 1 / ((2 : ℝ) ^ (d : ℕ) - 1) ^ 2
      = ∑' n : ℕ+,
          ((∑ e ∈ (n : ℕ).divisors, (((n : ℕ) / e : ℕ) : ℝ)) -
            ((n : ℕ).divisors.card : ℝ)) * ((1 : ℝ) / 2) ^ (n : ℕ) := by
  sorry

theorem tsum_totient_div_mersenne_sq_eq_gcd_moment_series :
    ∑' d : ℕ+, (Nat.totient (d : ℕ) : ℝ) / ((2 : ℝ) ^ (d : ℕ) - 1) ^ 2
      = ∑' n : ℕ+,
          ((∑ e ∈ (n : ℕ).divisors, (Nat.totient e : ℝ) * (((n : ℕ) / e : ℕ) : ℝ))
            - ((n : ℕ) : ℝ)) * ((1 : ℝ) / 2) ^ (n : ℕ) := by
  sorry

end Erdos249257.ExternalVerification249SquaredLambert
