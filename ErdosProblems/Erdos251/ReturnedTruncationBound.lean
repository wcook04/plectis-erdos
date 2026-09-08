import Mathlib

/-! Supplementary scalar estimates. The analytic tail estimates remain
explicit hypotheses here; see the accompanying ordinary proof. -/

namespace ErdosProblems.Erdos251.PaperR10

theorem discrepancy_of_bad_count
    (D B K M X : ℝ) (hX : 0 < X) (hM : 0 ≤ M)
    (hD : D ≤ 2 * M * (B / X)) (hB : B ≤ K) :
    D ≤ 2 * M * (K / X) := by
  apply le_trans hD
  apply mul_le_mul_of_nonneg_left
  · exact div_le_div_of_nonneg_right hB (le_of_lt hX)
  · positivity

theorem truncation_bound
    (a b ar br R eps ta tb : ℝ)
    (ha : |a - ar| ≤ ta)
    (hb : |b - br| ≤ tb)
    (hclip : |ar - br| ≤ 2 * R * eps) :
    |a - b| ≤ 2 * R * eps + ta + tb := by
  have heq : a - b = (a - ar) + (ar - br) + (br - b) := by ring
  rw [heq]
  calc
    |(a - ar) + (ar - br) + (br - b)| ≤
        |(a - ar) + (ar - br)| + |br - b| := abs_add_le _ _
    _ ≤ (|a - ar| + |ar - br|) + |br - b| := by
      linarith [abs_add_le (a - ar) (ar - br)]
    _ ≤ ta + (2 * R * eps) + tb := by
      rw [abs_sub_comm br b]
      linarith
    _ = 2 * R * eps + ta + tb := by ring

end ErdosProblems.Erdos251.PaperR10

#print axioms ErdosProblems.Erdos251.PaperR10.discrepancy_of_bad_count
#print axioms ErdosProblems.Erdos251.PaperR10.truncation_bound
