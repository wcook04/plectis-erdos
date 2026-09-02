import ErdosProblems.Erdos1041.SexticCubicPairedDeficitCone
import Mathlib.Tactic

/-!
# Erdős #1041: the sextic cubic-to-transverse transition cone

Writing the radial deficit as `delta = s^6`, this module enlarges the paired
low-mode cone from the scale `delta` to the natural transition scale `s^5`.
If `e1 + e2 ≤ s^5 / 16` and `s ≤ 1/64`, approximate tangent pairing makes
the total nuisance budget at most `3 s^5 / 16 = 6 (s/2)^5`.  The exact
degree-six Young factorization then leaves a uniform half-deficit margin.
-/

namespace ErdosProblems.Erdos1041.SexticCubicTransitionCone

open ErdosProblems.Erdos1041.SexticCubicRadialDeficitCone
open ErdosProblems.Erdos1041.SexticCubicPairedDeficitCone

/-- Pairing turns low-mode control at the natural transition scale into the
exact nuisance budget consumed by Young's inequality at scale `s/2`. -/
theorem transition_fourierNormSum
    {delta s e1 e2 e4 e5 : ℝ}
    (hs : 0 ≤ s) (hs64 : s ≤ 1 / 64)
    (hdelta : delta = s ^ 6)
    (hlow : e1 + e2 ≤ s ^ 5 / 16)
    (h4 : e4 ≤ e2 + 2 * delta)
    (h5 : e5 ≤ e1 + 2 * delta) :
    e1 + e2 + e4 + e5 ≤ 3 * s ^ 5 / 16 := by
  have hsix_le : s ^ 6 ≤ s ^ 5 / 64 := by
    have hmul := mul_le_mul_of_nonneg_left hs64 (pow_nonneg hs 5)
    simpa [pow_succ] using hmul
  rw [hdelta] at h4 h5
  linarith

/-- At transition scale, the selected-ray value has a half-deficit margin.
The sharper calculation actually gives `-59 delta / 64`. -/
theorem transition_selectedRay_margin
    {delta s t nuisance cubic : ℝ}
    (hs : 0 ≤ s) (ht : 0 ≤ t)
    (hdelta : delta = s ^ 6)
    (hnuisance : nuisance ≤ (3 * s ^ 5 / 16) * t)
    (hcubic : cubic ≤ 0) :
    -delta + nuisance + cubic - t ^ 6 ≤ -delta / 2 := by
  have hyoung := six_mul_fifth_mul_le (s / 2) t (by positivity) ht
  have hscale : 5 * (s / 2) ^ 6 ≤ delta / 2 := by
    rw [hdelta]
    nlinarith [pow_nonneg hs 6]
  have hcoefficient : 6 * (s / 2) ^ 5 = 3 * s ^ 5 / 16 := by ring
  rw [hcoefficient] at hyoung
  nlinarith

/-- Pairing, low-mode transition control, and the termwise unit-interval
bound imply the selected-ray half-margin directly. -/
theorem paired_transition_selectedRay_margin
    {delta s t e1 e2 e4 e5 nuisance cubic : ℝ}
    (hs : 0 ≤ s) (hs64 : s ≤ 1 / 64)
    (ht : 0 ≤ t) (ht1 : t ≤ 1)
    (he2 : 0 ≤ e2) (he4 : 0 ≤ e4) (he5 : 0 ≤ e5)
    (hdelta : delta = s ^ 6)
    (hlow : e1 + e2 ≤ s ^ 5 / 16)
    (h4 : e4 ≤ e2 + 2 * delta)
    (h5 : e5 ≤ e1 + 2 * delta)
    (hnuisance : nuisance ≤
      e1 * t + e2 * t ^ 2 + e4 * t ^ 4 + e5 * t ^ 5)
    (hcubic : cubic ≤ 0) :
    -delta + nuisance + cubic - t ^ 6 ≤ -delta / 2 := by
  have hsum := transition_fourierNormSum hs hs64 hdelta hlow h4 h5
  have hlinear := fourModes_le_linear (e1 := e1) ht ht1 he2 he4 he5
  have hweighted := mul_le_mul_of_nonneg_right hsum ht
  refine transition_selectedRay_margin (delta := delta) (s := s) (t := t)
    (nuisance := nuisance) (cubic := cubic) hs ht hdelta ?_ hcubic
  nlinarith

/-- The disk of radius `s^2/4` has a uniform half-deficit margin under the
same transition nuisance budget and a unit-bounded cubic coefficient. -/
theorem transition_innerDisk_margin
    {delta s u nuisance cubic baseline : ℝ}
    (hs : 0 ≤ s) (hs1 : s ≤ 1)
    (hdelta : delta = s ^ 6)
    (hu : 0 ≤ u) (huradius : u ≤ s ^ 2 / 4)
    (hnuisance : nuisance ≤ (3 * s ^ 5 / 16) * u)
    (hcubic : cubic ≤ u ^ 3)
    (hbaseline : baseline ≤ u ^ 6) :
    -delta + nuisance + cubic + baseline ≤ -delta / 2 := by
  have hu1 : u ≤ 1 := by
    have hsSq : s ^ 2 ≤ 1 := by
      nlinarith [mul_nonneg hs (sub_nonneg.mpr hs1)]
    linarith
  have huCube : u ^ 3 ≤ delta / 64 := by
    calc
      u ^ 3 ≤ (s ^ 2 / 4) ^ 3 := by gcongr
      _ = s ^ 6 / 64 := by ring
      _ = delta / 64 := by rw [hdelta]
  have huSixLeCube : u ^ 6 ≤ u ^ 3 :=
    ErdosProblems.Erdos1041.unitInterval_pow_anti
      (r := 3) (m := 6) hu hu1 (by omega)
  have hsSeven : s ^ 7 ≤ s ^ 6 :=
    ErdosProblems.Erdos1041.unitInterval_pow_anti
      (r := 6) (m := 7) hs hs1 (by omega)
  have hnuisance' : nuisance ≤ 3 * delta / 64 := by
    calc
      nuisance ≤ (3 * s ^ 5 / 16) * u := hnuisance
      _ ≤ (3 * s ^ 5 / 16) * (s ^ 2 / 4) := by gcongr
      _ = 3 * s ^ 7 / 64 := by ring
      _ ≤ 3 * s ^ 6 / 64 := by gcongr
      _ = 3 * delta / 64 := by rw [hdelta]
  nlinarith

/-- The transition cone and its quantitatively transverse complement are
exhaustive. -/
theorem transition_or_transverse (s e1 e2 : ℝ) :
    e1 + e2 ≤ s ^ 5 / 16 ∨ s ^ 5 / 16 < e1 + e2 := by
  exact le_or_gt (e1 + e2) (s ^ 5 / 16)

end ErdosProblems.Erdos1041.SexticCubicTransitionCone
