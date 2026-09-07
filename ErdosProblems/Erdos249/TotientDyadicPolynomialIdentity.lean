import Mathlib.Data.Nat.Totient
import Mathlib.Tactic

/-!
# The quadratic relation of the two dyadic zero channels

ROUND-SIX CANDIDATE: NOT COMPILED. Target: Mathlib / Lean 4.29.1.
This proves the polynomial identity and its elementary reductions.
It does NOT prove that the quadratic generates every polynomial relation.
Completeness requires the ordinary density argument supplied separately.
-/

namespace ErdosProblems.Erdos249.TotientDyadicPolynomialIdentity

/-- The local dyadic branches give one quadratic relation, including n = 0. -/
theorem zero_channels_quadratic (n : ℕ) :
    ((Nat.totient (2 * n) : ℚ) - (Nat.totient n : ℚ)) *
      ((Nat.totient (2 * n) : ℚ) - 2 * (Nat.totient n : ℚ)) = 0 := by
  rcases Nat.even_or_odd n with heven | hodd
  · rw [Nat.totient_two_mul_of_even heven]
    norm_num
  · rw [Nat.totient_two_mul_of_odd hodd]
    ring

/-- Monic reduction of the square of the second zero channel. -/
theorem zero_channel_square_reduction (n : ℕ) :
    (Nat.totient (2 * n) : ℚ) ^ 2 =
      3 * (Nat.totient n : ℚ) * (Nat.totient (2 * n) : ℚ) -
      2 * (Nat.totient n : ℚ) ^ 2 := by
  nlinarith [zero_channels_quadratic n]

/-- The corresponding recurrence reduces all higher powers of that channel. -/
theorem zero_channel_power_reduction (n j : ℕ) :
    (Nat.totient (2 * n) : ℚ) ^ (j + 2) =
      3 * (Nat.totient n : ℚ) * (Nat.totient (2 * n) : ℚ) ^ (j + 1) -
      2 * (Nat.totient n : ℚ) ^ 2 * (Nat.totient (2 * n) : ℚ) ^ j := by
  have h := zero_channel_square_reduction n
  calc
    (Nat.totient (2 * n) : ℚ) ^ (j + 2) =
        (Nat.totient (2 * n) : ℚ) ^ 2 *
          (Nat.totient (2 * n) : ℚ) ^ j := by rw [pow_add]; ring
    _ = (3 * (Nat.totient n : ℚ) * (Nat.totient (2 * n) : ℚ) -
          2 * (Nat.totient n : ℚ) ^ 2) *
          (Nat.totient (2 * n) : ℚ) ^ j := by rw [h]
    _ = _ := by ring

end ErdosProblems.Erdos249.TotientDyadicPolynomialIdentity
