import ErdosProblems.Erdos243.PaperCompleteR11.CubicScaleArithmetic

/-!
# From an actual rational parameter to the integer scale

The numerator and denominator are obtained from the rational itself. In
particular, coprimality and positivity are proved here, not supplied as
additional assumptions on a purported parametrisation.
-/

namespace ErdosProblems.Erdos243.PaperCompleteR11

/-- The absolute value of a nonzero rational has its canonical positive,
reduced numerator and denominator. -/
theorem rational_abs_reduced_positive (w : ℚ) (hw : w ≠ 0) :
    0 < w.num.natAbs ∧ 0 < w.den ∧
      Nat.Coprime w.num.natAbs w.den ∧
      |w| = (w.num.natAbs : ℚ) / (w.den : ℚ) := by
  have hn : |(w.num : ℚ)| = (w.num.natAbs : ℚ) := by
    cases hnum : w.num with
    | ofNat n => simp
    | negSucc n =>
        rw [abs_of_nonpos]
        · norm_num
        · have hn : (0 : ℚ) ≤ n := Nat.cast_nonneg n
          norm_num
          linarith
  have habs : |w| = (w.num.natAbs : ℚ) / (w.den : ℚ) := by
    conv_lhs => rw [← Rat.num_div_den w]
    rw [abs_div, hn, abs_of_pos (by exact_mod_cast w.den_pos)]
  have hr : 0 < w.num.natAbs := by
    by_contra h
    have hz : w.num.natAbs = 0 := by omega
    have hz' : |w| = 0 := by simpa [hz] using habs
    exact hw (abs_eq_zero.mp hz')
  exact ⟨hr, w.den_pos, w.reduced, habs⟩

/-- Both reciprocal branches give precisely the positive natural-number
identities used by the denominator-divisibility argument. -/
theorem cubic_rational_parameter_cleared
    (m : ℕ) (c w : ℚ) (hm : 0 < m)
    (hc : c = 1 ∨ c = -1)
    (heq : (w^2 + 1)^2 = 8 * (6*c/(m : ℚ)) * w^3 ∨
      (w^2 + 1)^2 = 8 * (6*c/(m : ℚ)) * w) :
    m * (w.num.natAbs^2 + w.den^2)^2 =
        48 * w.num.natAbs^3 * w.den ∨
      m * (w.num.natAbs^2 + w.den^2)^2 =
        48 * w.num.natAbs * w.den^3 := by
  have hmpos : (0 : ℚ) < (m : ℚ) := by exact_mod_cast hm
  have hm0 : (m : ℚ) ≠ 0 := ne_of_gt hmpos
  have hspos : (0 : ℚ) < (w.den : ℚ) := by exact_mod_cast w.den_pos
  have hs0 : (w.den : ℚ) ≠ 0 := ne_of_gt hspos
  have hcabs : |c| = 1 := by rcases hc with rfl | rfl <;> norm_num
  have hn : |(w.num : ℚ)| = (w.num.natAbs : ℚ) := by
    cases hnum : w.num with
    | ofNat n => simp
    | negSucc n =>
        rw [abs_of_nonpos]
        · norm_num
        · have hn : (0 : ℚ) ≤ n := Nat.cast_nonneg n
          norm_num
          linarith
  have habs : |w| = (w.num.natAbs : ℚ) / (w.den : ℚ) := by
    conv_lhs => rw [← Rat.num_div_den w]
    rw [abs_div, hn, abs_of_pos hspos]
  have hleft : 0 < w^2 + 1 := by positivity
  rcases heq with heq | heq
  · left
    have hh := congrArg abs heq
    have habsEq : (|w|^2 + 1)^2 = 8 * (6/(m : ℚ)) * |w|^3 := by
      simpa only [abs_pow, abs_of_pos hleft, abs_mul, abs_div, hcabs,
        abs_of_pos hmpos, abs_of_pos (by norm_num : (0 : ℚ) < 8),
        abs_of_pos (by norm_num : (0 : ℚ) < 6), mul_one, sq_abs] using hh
    rw [habs] at habsEq
    field_simp [hm0, hs0] at habsEq
    have hrational : (m : ℚ) * ((w.num.natAbs : ℚ)^2 + (w.den : ℚ)^2)^2 =
        48 * (w.num.natAbs : ℚ)^3 * (w.den : ℚ) := by
      nlinarith [habsEq]
    exact_mod_cast hrational
  · right
    have hh := congrArg abs heq
    have habsEq : (|w|^2 + 1)^2 = 8 * (6/(m : ℚ)) * |w| := by
      simpa only [abs_pow, abs_of_pos hleft, abs_mul, abs_div, hcabs,
        abs_of_pos hmpos, abs_of_pos (by norm_num : (0 : ℚ) < 8),
        abs_of_pos (by norm_num : (0 : ℚ) < 6), mul_one, sq_abs] using hh
    rw [habs] at habsEq
    field_simp [hm0, hs0] at habsEq
    have hrational : (m : ℚ) * ((w.num.natAbs : ℚ)^2 + (w.den : ℚ)^2)^2 =
        48 * (w.num.natAbs : ℚ) * (w.den : ℚ)^3 := by
      nlinarith [habsEq]
    exact_mod_cast hrational

/-- The rational parameter itself, in either branch and with either sign,
forces the scale twelve. -/
theorem cubic_scale_rational_classification
    (m : ℕ) (c w : ℚ) (hm : 0 < m)
    (hc : c = 1 ∨ c = -1) (hw : w ≠ 0)
    (heq : (w^2 + 1)^2 = 8 * (6*c/(m : ℚ)) * w^3 ∨
      (w^2 + 1)^2 = 8 * (6*c/(m : ℚ)) * w) : m = 12 := by
  obtain ⟨hr, hs, hcop, _⟩ := rational_abs_reduced_positive w hw
  exact (cubic_scale_nat_classification m w.num.natAbs w.den hr hs hcop
    (cubic_rational_parameter_cleared m c w hm hc heq)).2.2

#print axioms rational_abs_reduced_positive
#print axioms cubic_rational_parameter_cleared
#print axioms cubic_scale_rational_classification

end ErdosProblems.Erdos243.PaperCompleteR11
