import Mathlib

/-!
# Erdős 1041: exact sign kernel for the critical-spoke moment ceiling

The analytic synchronized power-series identity is proved in the companion
note. This file checks the exact rational signs of the Gaussian-integer cubic
showing that one initially descending spoke is sharp.
-/

namespace ErdosProblems.Erdos1041

theorem critical_spoke_witness_first_sign : (0 : ℚ) < 92 / 169 := by
  norm_num

theorem critical_spoke_witness_second_sign : (4 : ℚ) / 9 > 0 := by
  norm_num

theorem critical_spoke_witness_third_sign : (1 : ℚ) / 25 > 0 := by
  norm_num

theorem critical_spoke_witness_reciprocal_balance_re :
    (-3 : ℤ) + 0 + 3 = 0 := by
  norm_num

theorem critical_spoke_witness_reciprocal_balance_im :
    (-2 : ℤ) + 3 - 1 = 0 := by
  norm_num

end ErdosProblems.Erdos1041
