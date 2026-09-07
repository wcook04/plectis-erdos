import ErdosProblems.Erdos1041.SexticCubicRadialDeficitCone
import Mathlib.Tactic

/-!
# Erdős #1041: the paired radial-deficit cone at the sextic cubic face

Approximate tangent pairing bounds the fourth and fifth Fourier modes by the
second and first modes, respectively, up to twice the radial deficit.  Thus a
low-mode budget `e1 + e2 ≤ delta` gives a total non-cubic budget `≤ 6 delta`.
An exact degree-six weighted Young factorization absorbs this larger budget
when `delta = s^5` and `s ≤ 1/10`.  The result is a uniform `delta / 2` margin
on the parity-selected rays and on a small inner disk.
-/

namespace ErdosProblems.Erdos1041.SexticCubicPairedDeficitCone

open ErdosProblems.Erdos1041.SexticCubicRadialDeficitCone

/-- Approximate tangent pairing reduces low-mode dominance to a six-deficit
budget for all four non-cubic modes. -/
theorem paired_fourierNormSum_le_six_delta
    {delta e1 e2 e4 e5 : ℝ}
    (hlow : e1 + e2 ≤ delta)
    (h4 : e4 ≤ e2 + 2 * delta)
    (h5 : e5 ≤ e1 + 2 * delta) :
    e1 + e2 + e4 + e5 ≤ 6 * delta := by
  linarith

/-- Weighted Young's inequality in the exact degree-six form needed here.
The factorization also identifies the unique equality scale `t = s`. -/
theorem six_mul_fifth_mul_le (s t : ℝ) (hs : 0 ≤ s) (ht : 0 ≤ t) :
    6 * s ^ 5 * t ≤ t ^ 6 + 5 * s ^ 6 := by
  have hfactor :
      t ^ 6 - 6 * s ^ 5 * t + 5 * s ^ 6 =
        (t - s) ^ 2 *
          (t ^ 4 + 2 * s * t ^ 3 + 3 * s ^ 2 * t ^ 2 +
            4 * s ^ 3 * t + 5 * s ^ 4) := by
    ring
  have hpoly :
      0 ≤ t ^ 4 + 2 * s * t ^ 3 + 3 * s ^ 2 * t ^ 2 +
        4 * s ^ 3 * t + 5 * s ^ 4 := by
    positivity
  nlinarith [mul_nonneg (sq_nonneg (t - s)) hpoly]

/-- A fifth-root scale at most `1/10` converts the six-deficit nuisance budget
into a uniform half-deficit margin on every selected ray. -/
theorem selectedRay_margin
    {delta s t nuisance cubic : ℝ}
    (hs : 0 ≤ s) (hs10 : s ≤ 1 / 10)
    (ht : 0 ≤ t) (hdelta : delta = s ^ 5)
    (hnuisance : nuisance ≤ 6 * delta * t)
    (hcubic : cubic ≤ 0) :
    -delta + nuisance + cubic - t ^ 6 ≤ -delta / 2 := by
  have hdelta0 : 0 ≤ delta := by rw [hdelta]; positivity
  have hscale : 5 * s * delta ≤ delta / 2 := by
    have hsHalf : 5 * s ≤ (1 / 2 : ℝ) := by linarith
    have := mul_le_mul_of_nonneg_right hsHalf hdelta0
    nlinarith
  have hyoung := six_mul_fifth_mul_le s t hs ht
  rw [hdelta] at hnuisance hscale ⊢
  nlinarith

/-- The same paired hypotheses directly supply the ray margin after the four
mode values are bounded term-by-term on the unit interval. -/
theorem paired_selectedRay_margin
    {delta s t e1 e2 e4 e5 nuisance cubic : ℝ}
    (hs : 0 ≤ s) (hs10 : s ≤ 1 / 10)
    (ht : 0 ≤ t) (ht1 : t ≤ 1)
    (he2 : 0 ≤ e2) (he4 : 0 ≤ e4) (he5 : 0 ≤ e5)
    (hdelta : delta = s ^ 5)
    (hlow : e1 + e2 ≤ delta)
    (h4 : e4 ≤ e2 + 2 * delta)
    (h5 : e5 ≤ e1 + 2 * delta)
    (hnuisance : nuisance ≤
      e1 * t + e2 * t ^ 2 + e4 * t ^ 4 + e5 * t ^ 5)
    (hcubic : cubic ≤ 0) :
    -delta + nuisance + cubic - t ^ 6 ≤ -delta / 2 := by
  have hsum := paired_fourierNormSum_le_six_delta hlow h4 h5
  have hlinear := fourModes_le_linear (e1 := e1) ht ht1 he2 he4 he5
  have hweighted := mul_le_mul_of_nonneg_right hsum ht
  refine selectedRay_margin (delta := delta) (s := s) (t := t)
    (nuisance := nuisance) (cubic := cubic) hs hs10 ht hdelta ?_ hcubic
  nlinarith

/-- At radius `delta/16`, a six-deficit nuisance budget and a unit-bounded
cubic term are absorbed with a uniform half-deficit margin. -/
theorem paired_innerDisk_margin
    {delta u nuisance cubic baseline : ℝ}
    (hdelta : 0 < delta) (hdelta1 : delta ≤ 1)
    (hu : 0 ≤ u) (huradius : u ≤ delta / 16)
    (hnuisance : nuisance ≤ 6 * delta * u)
    (hcubic : cubic ≤ u ^ 3)
    (hbaseline : baseline ≤ u ^ 6) :
    -delta + nuisance + cubic + baseline ≤ -delta / 2 := by
  have hdelta0 : 0 ≤ delta := le_of_lt hdelta
  have hu16 : u ≤ 1 / 16 := by linarith
  have hu1 : u ≤ 1 := by linarith
  have huSq : u ^ 2 ≤ 1 / 256 := by
    nlinarith [mul_nonneg hu (sub_nonneg.mpr hu16)]
  have huCube : u ^ 3 ≤ delta / 4096 := by
    calc
      u ^ 3 = u ^ 2 * u := by ring
      _ ≤ (1 / 256 : ℝ) * u := mul_le_mul_of_nonneg_right huSq hu
      _ ≤ (1 / 256 : ℝ) * (delta / 16) :=
        mul_le_mul_of_nonneg_left huradius (by norm_num)
      _ = delta / 4096 := by ring
  have huSixLeCube : u ^ 6 ≤ u ^ 3 :=
    ErdosProblems.Erdos1041.unitInterval_pow_anti
      (r := 3) (m := 6) hu hu1 (by omega)
  have hnuisance' : nuisance ≤ 3 * delta / 8 := by
    calc
      nuisance ≤ 6 * delta * u := hnuisance
      _ ≤ 6 * delta * (delta / 16) := by gcongr
      _ ≤ 3 * delta / 8 := by
        nlinarith [mul_nonneg hdelta0 (sub_nonneg.mpr hdelta1)]
  nlinarith

/-- The low-mode branch and its transverse complement form an exhaustive
normalization dichotomy. -/
theorem lowMode_or_transverse (delta e1 e2 : ℝ) :
    e1 + e2 ≤ delta ∨ delta < e1 + e2 := by
  exact le_or_gt (e1 + e2) delta

end ErdosProblems.Erdos1041.SexticCubicPairedDeficitCone
