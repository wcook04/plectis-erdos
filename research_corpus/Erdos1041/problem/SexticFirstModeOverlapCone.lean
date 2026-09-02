import ErdosProblems.Erdos1041.SexticFirstModeDominantTangentCone
import Mathlib.Tactic

/-!
# Erdős #1041: overlap of the first- and second-mode sextic charts

The first-mode adjacent-ray selector remains valid beyond strict first-mode
dominance.  If `4 B ≤ 5 A` and `B ≤ 1`, the sextic baseline absorbs the
remaining mid-radius bump.  Thus the closed tangent chart extends from
`B ≤ A` to `B ≤ 5 A / 4`.
-/

namespace ErdosProblems.Erdos1041.SexticFirstModeOverlapCone

open ErdosProblems.Erdos1041.SexticFirstModeDominantTangentCone
open ErdosProblems.Erdos1041.SexticCanonicalMixedSlice

/-- The auxiliary cubic is strictly positive on the nonnegative ray. -/
theorem cubicAux_pos {t : ℝ} (ht : 0 ≤ t) :
    0 < 5 * t ^ 3 - 5 * t + 2 := by
  let s := sqrtThree
  have hs : 0 < s := sqrtThree_pos
  have hs2 : s ^ 2 = 3 := sqrtThree_sq
  have hconst : 0 < 6 * s - 10 := by
    have hsgt := sqrtThree_gt_fifty_div_twentyNine
    dsimp [s]
    nlinarith
  have hlinear : 0 < s * t + 2 := by positivity
  have hid :
      s ^ 3 * (5 * t ^ 3 - 5 * t + 2) =
        5 * (s * t - 1) ^ 2 * (s * t + 2) + 6 * s - 10 := by
    ring_nf at hs2 ⊢
    linear_combination (-5 * s * t + 2 * s) * hs2
  have hprod : 0 < s ^ 3 * (5 * t ^ 3 - 5 * t + 2) := by
    rw [hid]
    nlinarith [mul_nonneg (mul_nonneg (by norm_num : (0 : ℝ) ≤ 5)
      (sq_nonneg (s * t - 1))) (le_of_lt hlinear)]
  rcases (mul_pos_iff.mp hprod) with hpos | hneg
  · exact hpos.2
  · have hsCube : 0 < s ^ 3 := pow_pos hs 3
    linarith

/-- The rational overlap polynomial is nonnegative on `[0,1]`. -/
theorem overlapPolynomial_nonneg {t : ℝ} (ht : 0 ≤ t) :
    0 ≤ 5 * t ^ 5 - 2 * t ^ 4 + 5 * t ^ 3 - 5 * t + 2 := by
  by_cases hsmall : t ≤ 2 / 5
  · have hquad : 0 ≤ 5 * t ^ 2 - 2 * t + 5 := by
      nlinarith [sq_nonneg (5 * t - 1)]
    have hid :
        5 * t ^ 5 - 2 * t ^ 4 + 5 * t ^ 3 - 5 * t + 2 =
          t ^ 3 * (5 * t ^ 2 - 2 * t + 5) + (2 - 5 * t) := by ring
    rw [hid]
    have htail : 0 ≤ 2 - 5 * t := by linarith
    exact add_nonneg (mul_nonneg (pow_nonneg ht 3) hquad) htail
  · have hlarge : 2 / 5 ≤ t := le_of_not_ge hsmall
    have hlin : 0 ≤ 5 * t - 2 := by linarith
    have hcubic : 0 ≤ 5 * t ^ 3 - 5 * t + 2 :=
      le_of_lt (cubicAux_pos ht)
    have hid :
        5 * t ^ 5 - 2 * t ^ 4 + 5 * t ^ 3 - 5 * t + 2 =
          t ^ 4 * (5 * t - 2) + (5 * t ^ 3 - 5 * t + 2) := by ring
    rw [hid]
    positivity

/-- The normalized worst overlap ray, corresponding to `A=4/5`, is safe. -/
theorem normalizedOverlapRay_nonpos {t : ℝ}
    (ht : 0 ≤ t) :
    -(2 / 5 : ℝ) * (t - t ^ 5) + (t ^ 2 - t ^ 4) - t ^ 6 ≤ 0 := by
  have hp := overlapPolynomial_nonneg ht
  have hid :
      -(2 / 5 : ℝ) * (t - t ^ 5) + (t ^ 2 - t ^ 4) - t ^ 6 =
        -t * (5 * t ^ 5 - 2 * t ^ 4 + 5 * t ^ 3 - 5 * t + 2) / 5 := by
    ring
  rw [hid]
  nlinarith [mul_nonneg ht hp]

/-- If the first-mode norm is at least four fifths of the normalized
second-mode norm, the selected adjacent ray remains safe. -/
theorem pairedTangentRay_overlap_nonpos
    {A B a b t : ℝ}
    (hB : 0 ≤ B) (hB1 : B ≤ 1)
    (hBA : 4 * B ≤ 5 * A)
    (ht : 0 ≤ t) (ht1 : t ≤ 1)
    (ha : a ≤ -A / 2) (hb : b ≤ B) :
    pairedTangentRay a b t ≤ 0 := by
  have ht5 : t ^ 5 ≤ t := by simpa using
    (ErdosProblems.Erdos1041.unitInterval_pow_anti
      (r := 1) (m := 5) ht ht1 (by omega))
  have ht4 : t ^ 4 ≤ t ^ 2 :=
    ErdosProblems.Erdos1041.unitInterval_pow_anti
      (r := 2) (m := 4) ht ht1 (by omega)
  have hfirst := mul_le_mul_of_nonneg_left ha (sub_nonneg.mpr ht5)
  have hsecond := mul_le_mul_of_nonneg_left hb (sub_nonneg.mpr ht4)
  have hAcoeff : -A / 2 ≤ -(2 * B / 5) := by linarith
  have hfirstCoeff := mul_le_mul_of_nonneg_right hAcoeff (sub_nonneg.mpr ht5)
  let bracket := -(2 / 5 : ℝ) * (t - t ^ 5) + (t ^ 2 - t ^ 4)
  have hupper : pairedTangentRay a b t ≤ B * bracket - t ^ 6 := by
    dsimp [bracket]
    unfold pairedTangentRay
    nlinarith
  by_cases hbracket : bracket ≤ 0
  · have hmul : B * bracket ≤ 0 := mul_nonpos_of_nonneg_of_nonpos hB hbracket
    have ht6 : 0 ≤ t ^ 6 := pow_nonneg ht 6
    linarith
  · have hbracket0 : 0 ≤ bracket := le_of_not_ge hbracket
    have hmul := mul_le_mul_of_nonneg_right hB1 hbracket0
    have hnormalized := normalizedOverlapRay_nonpos ht
    dsimp [bracket] at hupper hmul hnormalized
    nlinarith

/-- The small joining chord also survives throughout the overlap
`B ≤ 5 A / 4`. -/
theorem overlapChord_strict
    {A B C u linear quadratic cubic quartic quintic baseline : ℝ}
    (hA : 0 < A) (hB : 0 ≤ B) (hBA : 4 * B ≤ 5 * A)
    (hu : 0 < u) (hu16 : u ≤ 1 / 16)
    (hlinear : linear ≤ -A * u / 2)
    (hquadratic : quadratic ≤ B * u ^ 2)
    (hcubic : cubic ≤ C * u ^ 3)
    (hquartic : quartic ≤ B * u ^ 4)
    (hquintic : quintic ≤ A * u ^ 5)
    (hbaseline : baseline ≤ u ^ 6)
    (hCscale : 8 * C * u ^ 2 ≤ A)
    (hbaseScale : 8 * u ^ 5 ≤ A) :
    linear + quadratic + cubic + quartic + quintic + baseline < 0 := by
  have hu0 : 0 ≤ u := le_of_lt hu
  have hu1 : u ≤ 1 := by linarith
  have huSq : u ^ 2 ≤ u / 16 := by
    nlinarith [mul_nonneg hu0 (sub_nonneg.mpr hu16)]
  have hu4 : u ^ 4 ≤ u ^ 2 :=
    ErdosProblems.Erdos1041.unitInterval_pow_anti
      (r := 2) (m := 4) hu0 hu1 (by omega)
  have hu5 : u ^ 5 ≤ u ^ 2 :=
    ErdosProblems.Erdos1041.unitInterval_pow_anti
      (r := 2) (m := 5) hu0 hu1 (by omega)
  have hA0 : 0 ≤ A := le_of_lt hA
  have hBupper : B ≤ 5 * A / 4 := by linarith
  have hquadratic' : quadratic ≤ 5 * A * u / 64 := by
    calc
      quadratic ≤ B * u ^ 2 := hquadratic
      _ ≤ (5 * A / 4) * u ^ 2 :=
        mul_le_mul_of_nonneg_right hBupper (sq_nonneg u)
      _ ≤ (5 * A / 4) * (u / 16) := by gcongr
      _ = 5 * A * u / 64 := by ring
  have hquartic' : quartic ≤ 5 * A * u / 64 := by
    calc
      quartic ≤ B * u ^ 4 := hquartic
      _ ≤ B * u ^ 2 := mul_le_mul_of_nonneg_left hu4 hB
      _ ≤ (5 * A / 4) * u ^ 2 :=
        mul_le_mul_of_nonneg_right hBupper (sq_nonneg u)
      _ ≤ (5 * A / 4) * (u / 16) := by gcongr
      _ = 5 * A * u / 64 := by ring
  have hquintic' : quintic ≤ A * u / 16 := by
    calc
      quintic ≤ A * u ^ 5 := hquintic
      _ ≤ A * u ^ 2 := mul_le_mul_of_nonneg_left hu5 hA0
      _ ≤ A * (u / 16) := mul_le_mul_of_nonneg_left huSq hA0
      _ = A * u / 16 := by ring
  have hcubic' : cubic ≤ A * u / 8 := by
    have hmul := mul_le_mul_of_nonneg_right hCscale (by positivity : 0 ≤ u / 8)
    nlinarith
  have hbaseline' : baseline ≤ A * u / 8 := by
    have hmul := mul_le_mul_of_nonneg_right hbaseScale (by positivity : 0 ≤ u / 8)
    nlinarith
  nlinarith [mul_pos hA hu]

end ErdosProblems.Erdos1041.SexticFirstModeOverlapCone
