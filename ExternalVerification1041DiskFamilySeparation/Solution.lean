/-
Copyright (c) 2026 Will Cook. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Will Cook
-/
import ErdosProblems.Erdos1041.DiskFamilyCriticalValueSeparation

/-!
# Source transport for the Erdős #1041 disk-family separation threshold kernel

The declarations below restate the Mathlib-only challenge vocabulary and
transport the exact source theorems without strengthening their hypotheses.
-/

namespace Erdos249257.ExternalVerification1041DiskFamilySeparation

noncomputable def diskFamilyCoefficient (n : ℕ) (S p : ℝ) : ℝ :=
  (S / ((n : ℝ) - 1)) ^ ((2 : ℝ) / (n : ℝ)) *
    Real.log ((S ^ 2 + S + p) / (S ^ 2 - S + p))

theorem diskFamilyCoefficient_lt_two_of_uniform_separation {n : ℕ}
    (hn : 3 ≤ n) {S p : ℝ} (hS : 4 / 3 ≤ S) (hS2 : S ≤ 2)
    (hp0 : 0 ≤ p) :
    diskFamilyCoefficient n S p < 2 :=
  ErdosProblems.Erdos1041.diskFamilyCoefficient_lt_two_of_uniform_separation
    hn hS hS2 hp0

theorem diskFamilyCoefficient_radius_two_lt_two {n : ℕ} (hn : 3 ≤ n) :
    diskFamilyCoefficient n 2 0 < 2 :=
  ErdosProblems.Erdos1041.diskFamilyCoefficient_radius_two_lt_two hn

theorem diskFamilyCoefficient_three_six_fifths_lt_two :
    diskFamilyCoefficient 3 (6 / 5) 0 < 2 :=
  ErdosProblems.Erdos1041.diskFamilyCoefficient_three_six_fifths_lt_two

theorem diskFamily_length_lt_two_of_squared_bound
    {n : ℕ} {S p length : ℝ}
    (hbound : length ^ 2 ≤ 2 * diskFamilyCoefficient n S p)
    (hthreshold : diskFamilyCoefficient n S p < 2) :
    length < 2 :=
  ErdosProblems.Erdos1041.diskFamily_length_lt_two_of_squared_bound
    (n := n) (S := S) (p := p) (length := length) hbound hthreshold

theorem diskFamily_length_lt_two_of_uniform_separation {n : ℕ} (hn : 3 ≤ n)
    {S p length : ℝ} (hS : 4 / 3 ≤ S) (hS2 : S ≤ 2) (hp0 : 0 ≤ p)
    (hbound : length ^ 2 ≤ 2 * diskFamilyCoefficient n S p) :
    length < 2 :=
  ErdosProblems.Erdos1041.diskFamily_length_lt_two_of_uniform_separation
    (length := length) hn hS hS2 hp0 hbound

end Erdos249257.ExternalVerification1041DiskFamilySeparation
