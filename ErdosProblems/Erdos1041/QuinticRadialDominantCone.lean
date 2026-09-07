import ErdosProblems.Erdos1041.FormACutQuantitativeExpansion
import Mathlib.Tactic

/-!
# Erdős #1041: the radial-dominant quintic Fourier cone

This module formalizes the scalar inequalities behind the radial-dominant
degree-five model.  Approximate tangent pairing and low-mode dominance reduce
the four Fourier norms to `5 * Delta`; a factorized weighted Young inequality
then gives a uniform `Delta / 2` margin on every fifth-root ray, while the
inner disk has margin `2 * Delta / 5`.
-/

namespace ErdosProblems.Erdos1041.QuinticRadialDominantCone

/-- Weighted Young inequality in exactly the form needed on a quintic ray.
The proof records the nonnegative factorization and its double equality. -/
theorem five_mul_fourth_mul_le (s t : ℝ) (hs : 0 ≤ s) (ht : 0 ≤ t) :
    5 * s ^ 4 * t ≤ t ^ 5 + 4 * s ^ 5 := by
  have hfactor :
      t ^ 5 - 5 * s ^ 4 * t + 4 * s ^ 5 =
        (t - s) ^ 2 * (t ^ 3 + 2 * s * t ^ 2 + 3 * s ^ 2 * t + 4 * s ^ 3) := by
    ring
  have hpoly : 0 ≤ t ^ 3 + 2 * s * t ^ 2 + 3 * s ^ 2 * t + 4 * s ^ 3 := by
    positivity
  nlinarith [mul_nonneg (sq_nonneg (t - s)) hpoly]

/-- A fourth-root scale at most `1/8` turns the weighted Young excess into at
most half of the radial deficit. -/
theorem radialRay_margin {delta s t projection : ℝ}
    (hs : 0 ≤ s) (hs8 : s ≤ 1 / 8) (ht : 0 ≤ t)
    (hdelta : delta = s ^ 4)
    (hprojection : projection ≤ 5 * delta * t) :
    -delta + projection - t ^ 5 ≤ -delta / 2 := by
  have hdelta0 : 0 ≤ delta := by rw [hdelta]; positivity
  have hscale : 4 * s * delta ≤ delta / 2 := by
    have : 4 * s ≤ (1 / 2 : ℝ) := by linarith
    have hmul := mul_le_mul_of_nonneg_right this hdelta0
    nlinarith
  have hyoung := five_mul_fourth_mul_le s t hs ht
  rw [hdelta] at hprojection hscale ⊢
  nlinarith

/-- Approximate tangent pairing plus `4 rho³ ≤ Delta` bounds the sum of all
four nonconstant Fourier norms by `5 Delta`. -/
theorem fourierNormSum_le_five_delta
    {delta rho e1 e2 e3 e4 : ℝ}
    (hrho : 0 ≤ rho) (hrho1 : rho ≤ 1)
    (hdom : 4 * rho ^ 3 ≤ delta)
    (h1 : e1 ≤ rho ^ 4) (h2 : e2 ≤ rho ^ 3)
    (h3 : e3 ≤ e2 + 2 * delta) (h4 : e4 ≤ e1 + 2 * delta) :
    e1 + e2 + e3 + e4 ≤ 5 * delta := by
  have hrho4 : rho ^ 4 ≤ rho ^ 3 := by
    have hnonneg : 0 ≤ rho ^ 3 * (1 - rho) :=
      mul_nonneg (pow_nonneg hrho 3) (sub_nonneg.mpr hrho1)
    nlinarith
  nlinarith

/-- On `[0,1]`, four nonnegative mode budgets with sum at most `5 Delta`
contribute at most `5 Delta * t`. -/
theorem fourModes_le_linear
    {delta t e1 e2 e3 e4 modeValue : ℝ}
    (ht : 0 ≤ t) (ht1 : t ≤ 1)
    (he2 : 0 ≤ e2) (he3 : 0 ≤ e3) (he4 : 0 ≤ e4)
    (hsum : e1 + e2 + e3 + e4 ≤ 5 * delta)
    (hmode : modeValue ≤ e1 * t + e2 * t ^ 2 + e3 * t ^ 3 + e4 * t ^ 4) :
    modeValue ≤ 5 * delta * t := by
  have ht2 : t ^ 2 ≤ t := by nlinarith [mul_nonneg ht (sub_nonneg.mpr ht1)]
  have ht3 : t ^ 3 ≤ t := by
    calc
      t ^ 3 ≤ t ^ 2 := by
        nlinarith [mul_nonneg (sq_nonneg t) (sub_nonneg.mpr ht1)]
      _ ≤ t := ht2
  have ht4 : t ^ 4 ≤ t := by
    calc
      t ^ 4 ≤ t ^ 3 := by
        nlinarith [mul_nonneg (pow_nonneg ht 3) (sub_nonneg.mpr ht1)]
      _ ≤ t := ht3
  have hweighted :
      e1 * t + e2 * t ^ 2 + e3 * t ^ 3 + e4 * t ^ 4 ≤
        (e1 + e2 + e3 + e4) * t := by
    nlinarith [mul_le_mul_of_nonneg_left ht2 he2,
      mul_le_mul_of_nonneg_left ht3 he3,
      mul_le_mul_of_nonneg_left ht4 he4]
  have hsumWeighted := mul_le_mul_of_nonneg_right hsum ht
  nlinarith

/-- The whole disk of radius `Delta/10` has a strict `2 Delta/5` margin once
the mode budget is `5 Delta`.  `baseline` is the upper bound for `-Re z⁵`. -/
theorem innerDisk_margin {delta u modeValue baseline : ℝ}
    (hdelta : 0 ≤ delta) (hdelta1 : delta ≤ 1)
    (huradius : u ≤ delta / 10)
    (hmode : modeValue ≤ 5 * delta * u)
    (hbaseline : baseline ≤ u) :
    -delta + modeValue + baseline ≤ -(2 * delta / 5) := by
  have hdeltaSq : delta ^ 2 ≤ delta := by
    nlinarith [mul_nonneg hdelta (sub_nonneg.mpr hdelta1)]
  have hmode' : modeValue ≤ delta / 2 := by
    calc
      modeValue ≤ 5 * delta * u := hmode
      _ ≤ 5 * delta * (delta / 10) := by gcongr
      _ ≤ delta / 2 := by nlinarith
  nlinarith

end ErdosProblems.Erdos1041.QuinticRadialDominantCone
