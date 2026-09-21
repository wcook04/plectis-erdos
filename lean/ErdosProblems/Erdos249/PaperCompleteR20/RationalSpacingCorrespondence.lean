import Erdos249257.PrimitiveRationalGapSupply

namespace ErdosProblems.Erdos249.PaperCompleteR20
open Erdos249257

theorem rational_difference_exact (u v : ℚ) :
    (v : ℝ) - u =
      ((v.num * (u.den : ℤ) - u.num * (v.den : ℤ) : ℤ) : ℝ) /
        ((v.den : ℝ) * u.den) := by
  have hu : (u.den : ℝ) ≠ 0 := by exact_mod_cast u.den_ne_zero
  have hv : (v.den : ℝ) ≠ 0 := by exact_mod_cast v.den_ne_zero
  rw [Rat.cast_def v, Rat.cast_def u]
  push_cast
  field_simp
  <;> ring

theorem rational_cross_numerator_positive {u v : ℚ} (h : u < v) :
    1 ≤ v.num * (u.den : ℤ) - u.num * (v.den : ℤ) := by
  have hr : (0 : ℝ) < (v : ℝ) - u := sub_pos.mpr (by exact_mod_cast h)
  rw [rational_difference_exact] at hr
  have hd : (0 : ℝ) < (v.den : ℝ) * u.den := by positivity
  have hn := (div_pos_iff_of_pos_right hd).mp hr
  have hi : (0 : ℤ) < v.num * (u.den : ℤ) - u.num * (v.den : ℤ) := by
    exact_mod_cast hn
  omega

theorem rational_error_denominator_bound {u v : ℚ} {ε : ℝ}
    (h : u < v) (he : (v : ℝ) - u ≤ ε) :
    1 / ((u.den : ℝ) * ε) ≤ v.den := by
  have hu : (0 : ℝ) < u.den := by exact_mod_cast u.den_pos
  have hv : (0 : ℝ) < v.den := by exact_mod_cast v.den_pos
  have hepos : 0 < ε := lt_of_lt_of_le (sub_pos.mpr (by exact_mod_cast h)) he
  have hg := le_trans (positive_rational_difference_lower_bound h) he
  push_cast at hg
  have hg' := (div_le_iff₀ (mul_pos hv hu)).mp hg
  apply (div_le_iff₀ (mul_pos hu hepos)).mpr
  nlinarith

end ErdosProblems.Erdos249.PaperCompleteR20
#print axioms ErdosProblems.Erdos249.PaperCompleteR20.rational_difference_exact
#print axioms ErdosProblems.Erdos249.PaperCompleteR20.rational_cross_numerator_positive
#print axioms ErdosProblems.Erdos249.PaperCompleteR20.rational_error_denominator_bound
#print axioms Erdos249257.positive_rational_difference_lower_bound
