import Mathlib
import Erdos249257.GcdMomentCalculus

/-!
# Squared Lambert identities

The source proves the squared Lambert transform by summing over divisors and
then evaluates its geometric kernel at one half. Constant weight gives the
divisor-sum minus divisor-count coefficients; totient weight gives the gcd-sum
minus the index. The two exact evaluations below transport those proofs.
-/

namespace Erdos249257.ExternalVerification249SquaredLambert

theorem tsum_one_div_mersenne_sq_eq_sigma_sub_tau_series :
    ∑' d : ℕ+, 1 / ((2 : ℝ) ^ (d : ℕ) - 1) ^ 2
      = ∑' n : ℕ+,
          ((∑ e ∈ (n : ℕ).divisors, (((n : ℕ) / e : ℕ) : ℝ)) -
            ((n : ℕ).divisors.card : ℝ)) * ((1 : ℝ) / 2) ^ (n : ℕ) := by
  exact GcdMomentCalculus.tsum_one_div_mersenne_sq_eq_sigma_sub_tau_series

theorem tsum_totient_div_mersenne_sq_eq_gcd_moment_series :
    ∑' d : ℕ+, (Nat.totient (d : ℕ) : ℝ) / ((2 : ℝ) ^ (d : ℕ) - 1) ^ 2
      = ∑' n : ℕ+,
          ((∑ e ∈ (n : ℕ).divisors, (Nat.totient e : ℝ) * (((n : ℕ) / e : ℕ) : ℝ))
            - ((n : ℕ) : ℝ)) * ((1 : ℝ) / 2) ^ (n : ℕ) := by
  exact GcdMomentCalculus.tsum_totient_div_mersenne_sq_eq_gcd_moment_series

end Erdos249257.ExternalVerification249SquaredLambert
