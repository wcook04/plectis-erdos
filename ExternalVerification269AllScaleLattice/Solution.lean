/-
Copyright (c) 2026 Will Cook. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Will Cook
-/
import ErdosProblems.Erdos269.RationalLatticeReduction

namespace Erdos249257.ExternalVerification269AllScaleLattice

open scoped BigOperators

abbrev smooth3Val := ErdosProblems.Erdos269.smooth3Val
abbrev threePrimeHeight := ErdosProblems.Erdos269.threePrimeHeight
abbrev strictSmoothExponents := ErdosProblems.Erdos269.strictSmoothExponents
abbrev strictSmoothShell := ErdosProblems.Erdos269.strictSmoothShell
abbrev dyadicSmoothShell235 := ErdosProblems.Erdos269.dyadicSmoothShell235
abbrev dyadicShellMassQ235 := ErdosProblems.Erdos269.dyadicShellMassQ235
abbrev dyadicShellMassR235 := ErdosProblems.Erdos269.dyadicShellMassR235
noncomputable abbrev dyadicShellTsumTailR235 :=
  ErdosProblems.Erdos269.dyadicShellTsumTailR235
noncomputable abbrev dyadicNormalizedTailStateR235 :=
  ErdosProblems.Erdos269.dyadicNormalizedTailStateR235
abbrev heightNormalizer235 := ErdosProblems.Erdos269.heightNormalizer235
abbrev dyadicSmoothWindowMassQ235 :=
  ErdosProblems.Erdos269.dyadicSmoothWindowMassQ235

theorem smoothHeight_mul_prime_dvd_boundaryHeight
    {p m x : ℕ} (hp : p = 2 ∨ p = 3 ∨ p = 5) (hx : 0 < x) (hlt : x < p ^ m) :
    p * threePrimeHeight 2 3 5 x ∣ threePrimeHeight 2 3 5 (p ^ m) :=
  ErdosProblems.Erdos269.smoothHeight_mul_prime_dvd_boundaryHeight hp hx hlt

theorem two_mul_heightNormalizer235 (a : ℕ) (ha : 1 ≤ a) :
    2 * heightNormalizer235 a = threePrimeHeight 2 3 5 (2 ^ a) :=
  ErdosProblems.Erdos269.two_mul_heightNormalizer235 a ha

theorem heightNormalizer235_mul_windowMass_eq_int (start count : ℕ) :
    ∃ z : ℕ,
      (heightNormalizer235 (start + count) : ℚ) *
        dyadicSmoothWindowMassQ235 start count = (z : ℚ) :=
  ErdosProblems.Erdos269.heightNormalizer235_mul_windowMass_eq_int start count

theorem dyadicShellTsumTailR235_eq_range_add (a k : ℕ) :
    dyadicShellTsumTailR235 a =
      ∑ i ∈ Finset.range k, dyadicShellMassR235 (a + i) +
        dyadicShellTsumTailR235 (a + k) :=
  ErdosProblems.Erdos269.dyadicShellTsumTailR235_eq_range_add a k

theorem qsmul_normalizedTailState_eq_int_of_value_eq_rat
    {p q : ℤ} (hq : 0 < q)
    (hval : dyadicShellTsumTailR235 1 = (p : ℝ) / (q : ℝ))
    {a : ℕ} (ha : 1 ≤ a) :
    ∃ k : ℤ,
      (q : ℝ) * dyadicNormalizedTailStateR235 dyadicShellTsumTailR235 a =
        (k : ℝ) :=
  ErdosProblems.Erdos269.qsmul_normalizedTailState_eq_int_of_value_eq_rat
    hq hval ha

theorem exists_normalizedTailState_collision_of_value_eq_rat
    {p q : ℤ} (hq : 0 < q)
    (hval : dyadicShellTsumTailR235 1 = (p : ℝ) / (q : ℝ)) :
    ∃ i j : ℕ, i < j ∧ ∃ z : ℤ,
      dyadicNormalizedTailStateR235 dyadicShellTsumTailR235 (1 + j) -
        dyadicNormalizedTailStateR235 dyadicShellTsumTailR235 (1 + i) =
          (z : ℝ) :=
  ErdosProblems.Erdos269.exists_normalizedTailState_collision_of_value_eq_rat
    hq hval

end Erdos249257.ExternalVerification269AllScaleLattice
