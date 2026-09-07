/-
Copyright (c) 2026 Will Cook. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Will Cook
-/
import Mathlib

/-!
# Trusted challenge for the Erdős #1041 disk-family separation threshold kernel

The ordinary paper theorem turns critical-value separation from a real centre
of the unit value segment into an analytic continuation disk and a squared
connector-length estimate with coefficient

`C(n, S, p) = (S/(n-1))^(2/n) * log((S^2 + S + p)/(S^2 - S + p))`.

The five checked endpoints below are exactly its formal numerical kernel: the
uniform threshold over every degree `n ≥ 3`, every radius `4/3 ≤ S ≤ 2` and
every centre parameter `p ≥ 0`, the branch-centred radius-two regime, the
degree-three radius `6/5` regime, the sign-free squared-length consumer, and
their composition.

The analytic continuation of the square-resolved inverse branch, its
univalence, the Bergman segment inequality, Pólya's area-capacity inequality,
and the exterior-fibre capacity gap remain ordinary mathematics in the
companion note.  Nothing here asserts the unrestricted Erdős #1041 conjecture.
-/

namespace Erdos249257.ExternalVerification1041DiskFamilySeparation

/-- The squared-length coefficient of the disk-family separation bound:
`(S / (n - 1))^(2/n) * log((S^2 + S + p)/(S^2 - S + p))`. -/
noncomputable def diskFamilyCoefficient (n : ℕ) (S p : ℝ) : ℝ :=
  (S / ((n : ℝ) - 1)) ^ ((2 : ℝ) / (n : ℝ)) *
    Real.log ((S ^ 2 + S + p) / (S ^ 2 - S + p))

/-- Uniform threshold: for every degree `n ≥ 3`, every radius `4/3 ≤ S ≤ 2`,
and every centre parameter `p ≥ 0`, the disk-family coefficient is strictly
below `2`. -/
theorem diskFamilyCoefficient_lt_two_of_uniform_separation {n : ℕ}
    (hn : 3 ≤ n) {S p : ℝ} (hS : 4 / 3 ≤ S) (hS2 : S ≤ 2)
    (hp0 : 0 ≤ p) :
    diskFamilyCoefficient n S p < 2 := by
  sorry

/-- The branch-centred radius-two regime holds in every degree `n ≥ 3`. -/
theorem diskFamilyCoefficient_radius_two_lt_two {n : ℕ} (hn : 3 ≤ n) :
    diskFamilyCoefficient n 2 0 < 2 := by
  sorry

/-- The degree-three radius `6/5` regime. -/
theorem diskFamilyCoefficient_three_six_fifths_lt_two :
    diskFamilyCoefficient 3 (6 / 5) 0 < 2 := by
  sorry

/-- Numerical consumer: a squared connector bound against twice a coefficient
strictly below two forces the connector strictly shorter than two, with no
sign hypothesis on the connector. -/
theorem diskFamily_length_lt_two_of_squared_bound
    {n : ℕ} {S p length : ℝ}
    (hbound : length ^ 2 ≤ 2 * diskFamilyCoefficient n S p)
    (hthreshold : diskFamilyCoefficient n S p < 2) :
    length < 2 := by
  sorry

/-- The uniform separation regime composed with the consumer. -/
theorem diskFamily_length_lt_two_of_uniform_separation {n : ℕ} (hn : 3 ≤ n)
    {S p length : ℝ} (hS : 4 / 3 ≤ S) (hS2 : S ≤ 2) (hp0 : 0 ≤ p)
    (hbound : length ^ 2 ≤ 2 * diskFamilyCoefficient n S p) :
    length < 2 := by
  sorry

end Erdos249257.ExternalVerification1041DiskFamilySeparation
