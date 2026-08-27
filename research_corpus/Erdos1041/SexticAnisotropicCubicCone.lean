import ErdosProblems.Erdos1041.SexticCubicTransitionCone
import Mathlib.Tactic

/-!
# Erdős #1041: the anisotropic sextic cubic transition cone

For `delta = s^6`, the natural low-mode scales are `s^5` for the linear mode
and `s^4` for the quadratic mode.  Two scaled Young factorizations and a
two-regime estimate for the paired radial errors give a uniform
half-deficit margin on every cubic-selected ray.
-/

namespace ErdosProblems.Erdos1041.SexticAnisotropicCubicCone

open ErdosProblems.Erdos1041.SexticCubicPairedDeficitCone

/-- Degree-six Young inequality for a quadratic mode. -/
theorem three_mul_fourth_mul_sq_le (r x : ℝ) :
    3 * r ^ 4 * x ^ 2 ≤ x ^ 6 + 2 * r ^ 6 := by
  have hfactor :
      x ^ 6 - 3 * r ^ 4 * x ^ 2 + 2 * r ^ 6 =
        (x ^ 2 - r ^ 2) ^ 2 * (x ^ 2 + 2 * r ^ 2) := by ring
  have hpoly : 0 ≤ x ^ 2 + 2 * r ^ 2 := by positivity
  nlinarith [mul_nonneg (sq_nonneg (x ^ 2 - r ^ 2)) hpoly]

/-- Approximate pairing reduces the four non-cubic modes to the two low
modes plus an explicit radial-error term. -/
theorem pairedModeValue_le
    {delta t e1 e2 e4 e5 modeValue : ℝ}
    (ht : 0 ≤ t) (ht1 : t ≤ 1)
    (he1 : 0 ≤ e1) (he2 : 0 ≤ e2)
    (h4 : e4 ≤ e2 + 2 * delta)
    (h5 : e5 ≤ e1 + 2 * delta)
    (hmode : modeValue ≤
      e1 * t + e2 * t ^ 2 + e4 * t ^ 4 + e5 * t ^ 5) :
    modeValue ≤
      2 * e1 * t + 2 * e2 * t ^ 2 + 2 * delta * (t ^ 4 + t ^ 5) := by
  have ht4 : t ^ 4 ≤ t ^ 2 :=
    ErdosProblems.Erdos1041.unitInterval_pow_anti
      (r := 2) (m := 4) ht ht1 (by omega)
  have ht5 : t ^ 5 ≤ t := by simpa using
    (ErdosProblems.Erdos1041.unitInterval_pow_anti
      (r := 1) (m := 5) ht ht1 (by omega))
  have h4mul := mul_le_mul_of_nonneg_right h4 (pow_nonneg ht 4)
  have h5mul := mul_le_mul_of_nonneg_right h5 (pow_nonneg ht 5)
  have he1pow := mul_le_mul_of_nonneg_left ht5 he1
  have he2pow := mul_le_mul_of_nonneg_left ht4 he2
  nlinarith

/-- At `s ≤ 1/64`, the paired radial errors cost at most one quarter of
the deficit and one sixty-fourth of the sextic baseline. -/
theorem pairedRadialError_le
    {delta s t : ℝ}
    (hs : 0 ≤ s) (hs64 : s ≤ 1 / 64)
    (ht : 0 ≤ t) (ht1 : t ≤ 1)
    (hdelta : delta = s ^ 6) :
    2 * delta * (t ^ 4 + t ^ 5) ≤ delta / 4 + t ^ 6 / 64 := by
  have ht5 : t ^ 5 ≤ t ^ 4 :=
    ErdosProblems.Erdos1041.unitInterval_pow_anti
      (r := 4) (m := 5) ht ht1 (by omega)
  have hdelta0 : 0 ≤ delta := by rw [hdelta]; positivity
  have hreduce :
      2 * delta * (t ^ 4 + t ^ 5) ≤ 4 * delta * t ^ 4 := by
    nlinarith [mul_le_mul_of_nonneg_left ht5 hdelta0]
  by_cases hsmall : t ≤ 1 / 2
  · have ht4 : t ^ 4 ≤ 1 / 16 := by
      have hp := pow_le_pow_left₀ ht hsmall 4
      norm_num at hp ⊢
      exact hp
    have : 4 * delta * t ^ 4 ≤ delta / 4 := by
      nlinarith [mul_le_mul_of_nonneg_left ht4 hdelta0]
    linarith [pow_nonneg ht 6]
  · have htHalf : 1 / 2 ≤ t := le_of_not_ge hsmall
    have hsPow : s ^ 6 ≤ (1 / 64 : ℝ) ^ 6 :=
      pow_le_pow_left₀ hs hs64 6
    have hdeltaSmall : delta ≤ 1 / 1024 := by
      rw [hdelta]
      norm_num at hsPow ⊢
      linarith
    have htSq : 1 / 4 ≤ t ^ 2 := by nlinarith
    have hcompare : 256 * delta ≤ t ^ 2 := by nlinarith
    have hmul := mul_le_mul_of_nonneg_right hcompare (pow_nonneg ht 4)
    have hhigh : 4 * delta * t ^ 4 ≤ t ^ 6 / 64 := by
      nlinarith
    linarith

/-- The anisotropic low-mode hypotheses give a uniform half-deficit ray
margin after selecting a nonpositive cubic projection. -/
theorem anisotropic_selectedRay_margin
    {delta s t e1 e2 e4 e5 modeValue cubic : ℝ}
    (hs : 0 ≤ s) (hs64 : s ≤ 1 / 64)
    (ht : 0 ≤ t) (ht1 : t ≤ 1)
    (hdelta : delta = s ^ 6)
    (he1 : 0 ≤ e1) (he2 : 0 ≤ e2)
    (he1small : e1 ≤ 3 * s ^ 5 / 2048)
    (he2small : e2 ≤ 3 * s ^ 4 / 2048)
    (h4 : e4 ≤ e2 + 2 * delta)
    (h5 : e5 ≤ e1 + 2 * delta)
    (hmode : modeValue ≤
      e1 * t + e2 * t ^ 2 + e4 * t ^ 4 + e5 * t ^ 5)
    (hcubic : cubic ≤ 0) :
    -delta + modeValue + cubic - t ^ 6 ≤ -delta / 2 := by
  have hpaired := pairedModeValue_le ht ht1 he1 he2 h4 h5 hmode
  have hfirst :
      2 * e1 * t ≤ t ^ 6 / 64 + 5 * delta / 4096 := by
    have hcoeff : 2 * e1 ≤ 3 * s ^ 5 / 1024 := by linarith
    have hmul := mul_le_mul_of_nonneg_right hcoeff ht
    have hyoung := six_mul_fifth_mul_le (s / 4) (t / 2)
      (by positivity) (by positivity)
    rw [hdelta]
    nlinarith
  have hsecond :
      2 * e2 * t ^ 2 ≤ t ^ 6 / 64 + 2 * delta / 4096 := by
    have hcoeff : 2 * e2 ≤ 3 * s ^ 4 / 1024 := by linarith
    have hmul := mul_le_mul_of_nonneg_right hcoeff (pow_nonneg ht 2)
    have hyoung := three_mul_fourth_mul_sq_le (s / 4) (t / 2)
    rw [hdelta]
    nlinarith
  have herror := pairedRadialError_le hs hs64 ht ht1 hdelta
  nlinarith

/-- Once the inner nuisance, cubic, and baseline budgets are separately
reduced to the displayed fractions, the inner disk has half-deficit margin. -/
theorem anisotropic_innerDisk_margin
    {delta nuisance cubic baseline : ℝ}
    (hdelta : 0 ≤ delta)
    (hnuisance : nuisance ≤ delta / 32)
    (hcubic : cubic ≤ delta / 64)
    (hbaseline : baseline ≤ delta / 64) :
    -delta + nuisance + cubic + baseline ≤ -delta / 2 := by
  linarith

end ErdosProblems.Erdos1041.SexticAnisotropicCubicCone
