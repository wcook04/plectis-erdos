import Mathlib.Tactic

/-!
# Erdős 1041: entrance-energy ratio bridge

The companion note proves the exact merge-tree exponent telescoping.  This
module checks the load-bearing scalar consequences after the attachment-age
factor has been assembled.
-/

namespace ErdosProblems.Erdos1041.EntranceEnergyRatioBridge

/-- Squaring the exact entrance-energy bridge produces the discounted leaf
energy appearing in the component aggregate. -/
theorem discounted_square_identity
    {q scale energyRow attenuation : ℝ}
    (h : q = scale * energyRow / attenuation) :
    q ^ 2 = scale ^ 2 * energyRow ^ 2 / attenuation ^ 2 := by
  rw [h]
  ring

/-- Attachment attenuation at least one makes singleton entrance energy no
larger than the corresponding propagated energy scale. -/
theorem discounted_square_le
    {q scale energyRow attenuation : ℝ}
    (hs : 0 <= scale) (ha : 1 <= attenuation)
    (h : q = scale * energyRow / attenuation) :
    q ^ 2 <= scale ^ 2 * energyRow ^ 2 := by
  rw [h]
  have ha0 : 0 < attenuation := lt_of_lt_of_le zero_lt_one ha
  have hsq : 1 <= attenuation ^ 2 := by nlinarith
  rw [div_pow]
  apply (div_le_iff₀ (sq_pos_of_pos ha0)).2
  nlinarith [sq_nonneg (scale * energyRow)]

/-- A uniform upper bound on attachment attenuation yields the exact lower
consumer used in the component inequality. -/
theorem discounted_square_lower_of_attenuation_le
    {q scale energyRow attenuation cap : ℝ}
    (ha : 0 < attenuation) (hac : attenuation <= cap)
    (hc : 0 < cap)
    (h : q = scale * energyRow / attenuation) :
    scale ^ 2 * energyRow ^ 2 / cap ^ 2 <= q ^ 2 := by
  rw [h, div_pow]
  have ha2 : 0 < attenuation ^ 2 := sq_pos_of_pos ha
  have hc2 : 0 < cap ^ 2 := sq_pos_of_pos hc
  apply (div_le_div_iff₀ hc2 ha2).2
  have hsq : attenuation ^ 2 ≤ cap ^ 2 := by
    nlinarith [mul_nonneg (sub_nonneg.mpr hac)
      (add_nonneg (le_of_lt ha) (le_of_lt hc))]
  have hscale : 0 ≤ scale ^ 2 * energyRow ^ 2 := by positivity
  calc
    scale ^ 2 * energyRow ^ 2 * attenuation ^ 2
        ≤ scale ^ 2 * energyRow ^ 2 * cap ^ 2 :=
      mul_le_mul_of_nonneg_left hsq hscale
    _ = (scale * energyRow) ^ 2 * cap ^ 2 := by ring

end ErdosProblems.Erdos1041.EntranceEnergyRatioBridge
