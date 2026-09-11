import Erdos249257.PrimitiveSupportBridge

/-!
# Rational-gap supply for primitive shell pressure

`PrimitiveSupportBridge.prefixDenominator_shell_power_bound` and
`PrimitiveSupportBridge.nextSupport_power_bound` deliberately expose their
Diophantine lower bound as a hypothesis.  This file supplies that hypothesis
when the residual is the positive difference between a rational whole value
and a rational finite-prefix value.

The source is the existing exact rational-gap theorem
`one_div_den_mul_den_le_abs_sub`.  The only extra input is strict positivity
of the residual, which removes the absolute value.  Thus the multiplier seen
by the shell consumer is the product of the *actual reduced denominators*,
not a displayed or guessed denominator.

Consumer: `prefixDenominator_shell_power_bound` (and its next-support
counterpart).  Disconfirmation test: `whole = prefix`, or more generally a
nonpositive residual, must not enter this adapter; in that case the absolute
rational gap does not provide a positive residual lower bound.

The supported root `Erdos249257.lean` imports this adapter.  Its focused
validation target is `Erdos249257.PrimitiveRationalGapSupply`.
-/

namespace Erdos249257

/-- A positive rational difference is at least the reciprocal of the product
of the two reduced denominators. -/
theorem positive_rational_difference_lower_bound
    {whole pfx : ℚ} (hpositive : pfx < whole) :
    (1 : ℝ) /
        (((whole.den * pfx.den : ℕ) : ℝ)) ≤
      (whole : ℝ) - (pfx : ℝ) := by
  have hne : whole ≠ pfx := ne_of_gt hpositive
  have hgap := one_div_den_mul_den_le_abs_sub hne
  have hcastPositive : (0 : ℝ) < (whole : ℝ) - (pfx : ℝ) := by
    exact sub_pos.mpr (by exact_mod_cast hpositive)
  rw [abs_of_pos hcastPositive] at hgap
  simpa only [Nat.cast_mul] using hgap

/-- Direct supply adapter for the prefix-denominator shell consumer.  Once
the analytic shell/far-tail upper bound is known, rationality alone supplies
the matching lower bound with the actual reduced denominators. -/
theorem prefixDenominator_shell_power_bound_of_rational_difference
    (whole pfx : ℚ) (K X : ℕ)
    (hpositive : pfx < whole) (hX : 1 ≤ X)
    (hupper : (whole : ℝ) - (pfx : ℝ) ≤
      (K : ℝ) / (2 : ℝ) ^ X + 2 / (2 : ℝ) ^ (2 * X)) :
    (2 : ℝ) ^ X ≤
      ((whole.den * pfx.den : ℕ) : ℝ) * (K + 1) := by
  exact prefixDenominator_shell_power_bound
    whole.den pfx.den K X whole.den_pos pfx.den_pos hX
    ((whole : ℝ) - (pfx : ℝ))
    (positive_rational_difference_lower_bound hpositive) hupper

/-- Direct supply adapter for the next-support power consumer.  Any analytic
bound of the form `whole-prefix ≤ 4/2^m` forces the next exponent below the
product-denominator power barrier. -/
theorem nextSupport_power_bound_of_rational_difference
    (whole pfx : ℚ) (m : ℕ)
    (hpositive : pfx < whole)
    (hupper : (whole : ℝ) - (pfx : ℝ) ≤ 4 / (2 : ℝ) ^ m) :
    (2 : ℝ) ^ m ≤
      4 * ((whole.den * pfx.den : ℕ) : ℝ) := by
  exact nextSupport_power_bound
    whole.den pfx.den m whole.den_pos pfx.den_pos
    ((whole : ℝ) - (pfx : ℝ))
    (positive_rational_difference_lower_bound hpositive) hupper

end Erdos249257
