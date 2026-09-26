import Mathlib.Data.Real.Basic
import Mathlib.Algebra.Order.Ring.Pow
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum

/-!
# Removing a positive integer multiplier from a Lambert coefficient

Bernoulli's inequality controls the denominator after multiplying the exponent.
The resulting bound is uniform in the additional prime contribution.
-/

noncomputable section
namespace ErdosProblems.Erdos257

/-- Multiplying a positive exponent by a positive integer cannot increase
its Lambert coefficient. -/
theorem nat_mul_div_pow_mul_sub_one_le (b x u : ℕ)
    (hb : 2 ≤ b) (hx : 1 ≤ x) (hu : 1 ≤ u) :
    ((x * u : ℕ) : ℝ) / ((b : ℝ) ^ (x * u) - 1) ≤
      (x : ℝ) / ((b : ℝ) ^ x - 1) := by
  have hbR : (1 : ℝ) < b := by exact_mod_cast (lt_of_lt_of_le (by decide : 1 < 2) hb)
  have hx0 : x ≠ 0 := Nat.one_le_iff_ne_zero.mp hx
  have hu0 : u ≠ 0 := Nat.one_le_iff_ne_zero.mp hu
  have hbase : 1 < (b : ℝ) ^ x := one_lt_pow₀ hbR hx0
  have hsmall : 0 < (b : ℝ) ^ x - 1 := sub_pos.mpr hbase
  have hlarge : 0 < (b : ℝ) ^ (x * u) - 1 :=
    sub_pos.mpr (one_lt_pow₀ hbR (Nat.mul_ne_zero hx0 hu0))
  have hbern := one_add_mul_sub_le_pow (by linarith : (-1 : ℝ) ≤ (b : ℝ) ^ x) u
  have hden : (u : ℝ) * ((b : ℝ) ^ x - 1) ≤ (b : ℝ) ^ (x * u) - 1 := by
    rw [pow_mul]
    linarith only [hbern]
  apply (div_le_div_iff₀ hlarge hsmall).mpr
  simpa only [Nat.cast_mul, mul_assoc] using
    mul_le_mul_of_nonneg_left hden (Nat.cast_nonneg x)

#print axioms nat_mul_div_pow_mul_sub_one_le

end ErdosProblems.Erdos257
end
