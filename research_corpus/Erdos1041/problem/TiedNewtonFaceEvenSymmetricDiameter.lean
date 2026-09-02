import Mathlib.Tactic

/-!
# Erdős #1041: all-degree even-symmetric diameter kernel

An even polynomial with nonpositive real coefficients and a strictly negative
constant term is strictly negative on the entire real axis.  The companion
note spends this as an opposite-end tied-face connector.
-/

namespace ErdosProblems.Erdos1041.TiedNewtonFaceEvenSymmetricDiameter

def evenConeValue
    (m : ℕ) (s : Finset ℕ) (coeff : ℕ → ℝ) (b x : ℝ) : ℝ :=
  -x ^ (2 * m) + ∑ k ∈ s, coeff k * x ^ (2 * k) + b

theorem evenConeValue_neg
    (m : ℕ) (s : Finset ℕ) (coeff : ℕ → ℝ) (b x : ℝ)
    (hcoeff : ∀ k ∈ s, coeff k ≤ 0) (hb : b < 0) :
    evenConeValue m s coeff b x < 0 := by
  have hevenpow (n : ℕ) : 0 ≤ x ^ (2 * n) := by
    rw [Nat.mul_comm 2 n, pow_mul]
    positivity
  have hlead : -x ^ (2 * m) ≤ 0 :=
    neg_nonpos.mpr (hevenpow m)
  have hsum : (∑ k ∈ s, coeff k * x ^ (2 * k)) ≤ 0 := by
    exact Finset.sum_nonpos fun k hk =>
      mul_nonpos_of_nonpos_of_nonneg (hcoeff k hk) (hevenpow k)
  dsimp [evenConeValue]
  linarith

theorem blockL1_realAxis_neg
    {a b x : ℝ} (ha : a ≤ 0) (hb : b < 0) :
    -x ^ 6 + a * x ^ 2 + b < 0 := by
  have h6pow : 0 ≤ x ^ 6 := by positivity
  have h6 : -x ^ 6 ≤ 0 := neg_nonpos.mpr h6pow
  have h2 : a * x ^ 2 ≤ 0 :=
    mul_nonpos_of_nonpos_of_nonneg ha (sq_nonneg x)
  linarith

theorem diameter_displacement (R : ℝ) : R - (-R) = 2 * R := by
  ring

theorem diameter_length_eq_two_mul
    {R : ℝ} (hR : 0 ≤ R) : |R - (-R)| = 2 * R := by
  rw [diameter_displacement, abs_of_nonneg]
  positivity

end ErdosProblems.Erdos1041.TiedNewtonFaceEvenSymmetricDiameter
