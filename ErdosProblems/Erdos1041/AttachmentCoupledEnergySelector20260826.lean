import Mathlib

/-!
# Erdős 1041: attachment-coupled selector kernels

This file formalizes the exact rational quartic margins and the scalar
common-ancestry factorization used by the companion note. It does not assert
the full weighted-tree selector or Erdős 1041.
-/

namespace ErdosProblems.Erdos1041

theorem quartic_terminal_inner_ratio_gt_four :
    (144 : ℚ) / 25 > 4 := by
  norm_num

theorem quartic_young_energy_fraction_lt_half :
    (144 : ℚ) / 769 < 1 / 2 := by
  norm_num

theorem quartic_young_energy_deficit :
    (1 : ℚ) / 2 - 144 / 769 = 481 / 1538 := by
  norm_num

/-- Common ancestry cancels from the pair's tree distance but reappears as an
exact common exponential factor in the singleton entrance-charge currency. -/
theorem common_ancestry_discount_exact (β w A B : ℝ) :
    β * w * Real.exp (-2 * (A + B))
      = (β * Real.exp (-2 * B)) * (w * Real.exp (-2 * A)) := by
  have hexp : Real.exp (-2 * (A + B))
      = Real.exp (-2 * A) * Real.exp (-2 * B) := by
    rw [← Real.exp_add]
    congr 1
    ring
  rw [hexp]
  ring

end ErdosProblems.Erdos1041
