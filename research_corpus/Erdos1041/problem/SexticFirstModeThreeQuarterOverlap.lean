import ErdosProblems.Erdos1041.SexticFirstModeOverlapCone
import Mathlib.Tactic

/-!
# Erdős #1041: the sextic first-mode overlap reaches three quarters

The previous rational overlap used `4 B ≤ 5 A`.  A sharper degree-five
positivity certificate proves the selected adjacent rays safe under
`3 B ≤ 4 A`.  The small joining-chord budget also survives this larger
second-mode allowance.  Thus the unresolved normalized mixed annulus begins
strictly below `|E₁| / |E₂| = 3/4`.
-/

namespace ErdosProblems.Erdos1041.SexticFirstModeThreeQuarterOverlap

open ErdosProblems.Erdos1041.SexticFirstModeDominantTangentCone

/-- The degree-five polynomial governing the normalized `3/4` ray. -/
def threeQuarterPolynomial (t : ℝ) : ℝ :=
  8 * t ^ 5 - 3 * t ^ 4 + 8 * t ^ 3 - 8 * t + 3

/-- On the left half-interval, the polynomial has a positive Bernstein
certificate after the substitution `x = 2t`. -/
noncomputable def threeQuarterLeftBernstein (x : ℝ) : ℝ :=
    3 * (1 - x) ^ 5
  + (11 / 5 : ℝ) * (5 * x * (1 - x) ^ 4)
  + (7 / 5 : ℝ) * (10 * x ^ 2 * (1 - x) ^ 3)
  + (7 / 10 : ℝ) * (10 * x ^ 3 * (1 - x) ^ 2)
  + (13 / 80 : ℝ) * (5 * x ^ 4 * (1 - x))
  + (1 / 16 : ℝ) * x ^ 5

theorem threeQuarter_left_identity (t : ℝ) :
    threeQuarterPolynomial t = threeQuarterLeftBernstein (2 * t) := by
  unfold threeQuarterPolynomial threeQuarterLeftBernstein
  ring

theorem threeQuarterLeftBernstein_nonneg {x : ℝ}
    (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    0 ≤ threeQuarterLeftBernstein x := by
  unfold threeQuarterLeftBernstein
  have hsub : 0 ≤ 1 - x := sub_nonneg.mpr hx1
  positivity

/-- The normalized ray polynomial is positive throughout the unit interval.
The left half uses Bernstein positivity; on the right half, putting
`x = 2t-1` leaves a positive quadratic plus positive monomials. -/
theorem threeQuarterPolynomial_pos {t : ℝ}
    (ht : 0 ≤ t) (ht1 : t ≤ 1) :
    0 < threeQuarterPolynomial t := by
  by_cases hhalf : t ≤ 1 / 2
  · rw [threeQuarter_left_identity]
    have hx0 : 0 ≤ 2 * t := by positivity
    have hx1 : 2 * t ≤ 1 := by linarith
    unfold threeQuarterLeftBernstein
    have hprefix : 0 ≤ (3 : ℝ) * (1 - 2 * t) ^ 5 +
        (11 / 5 : ℝ) * (5 * (2 * t) * (1 - 2 * t) ^ 4) +
        (7 / 5 : ℝ) * (10 * (2 * t) ^ 2 * (1 - 2 * t) ^ 3) +
        (7 / 10 : ℝ) * (10 * (2 * t) ^ 3 * (1 - 2 * t) ^ 2) +
        (13 / 80 : ℝ) * (5 * (2 * t) ^ 4 * (1 - 2 * t)) := by
      have hsub : 0 ≤ 1 - 2 * t := by linarith
      positivity
    by_cases ht0 : t = 0
    · subst t
      norm_num
    · have htpos : 0 < t := lt_of_le_of_ne ht (Ne.symm ht0)
      have hlast : 0 < (1 / 16 : ℝ) * (2 * t) ^ 5 := by positivity
      nlinarith
  · let x := 2 * t - 1
    have hx : 0 ≤ x := by dsimp [x]; linarith
    have hquad : 0 < 70 * x ^ 2 - 8 * x + 1 := by
      have hsquare := sq_nonneg (x - 2 / 35)
      nlinarith
    have hrest : 0 ≤ 4 * x ^ 5 + 17 * x ^ 4 + 44 * x ^ 3 := by
      positivity
    have hid : threeQuarterPolynomial t =
        (4 * x ^ 5 + 17 * x ^ 4 + 44 * x ^ 3 +
          (70 * x ^ 2 - 8 * x + 1)) / 16 := by
      dsimp [x]
      unfold threeQuarterPolynomial
      ring
    rw [hid]
    positivity

/-- The worst normalized ray at `A/B = 3/4` is nonpositive. -/
theorem normalizedThreeQuarterRay_nonpos {t : ℝ}
    (ht : 0 ≤ t) (ht1 : t ≤ 1) :
    -(3 / 8 : ℝ) * (t - t ^ 5) + (t ^ 2 - t ^ 4) - t ^ 6 ≤ 0 := by
  have hp := le_of_lt (threeQuarterPolynomial_pos ht ht1)
  have hid :
      -(3 / 8 : ℝ) * (t - t ^ 5) + (t ^ 2 - t ^ 4) - t ^ 6 =
        -t * threeQuarterPolynomial t / 8 := by
    unfold threeQuarterPolynomial
    ring
  rw [hid]
  have hnum : -t * threeQuarterPolynomial t ≤ 0 := by
    nlinarith [mul_nonneg ht hp]
  exact div_nonpos_of_nonpos_of_nonneg hnum (by norm_num)

/-- If `|E₁| / |E₂| ≥ 3/4`, the adjacent first-mode selector's two rays
remain safe after normalizing `|E₂| ≤ 1`. -/
theorem pairedTangentRay_threeQuarter_nonpos
    {A B a b t : ℝ}
    (hB : 0 ≤ B) (hB1 : B ≤ 1)
    (hBA : 3 * B ≤ 4 * A)
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
  have hAcoeff : -A / 2 ≤ -(3 * B / 8) := by linarith
  have hfirstCoeff := mul_le_mul_of_nonneg_right hAcoeff (sub_nonneg.mpr ht5)
  let bracket := -(3 / 8 : ℝ) * (t - t ^ 5) + (t ^ 2 - t ^ 4)
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
    have hnormalized := normalizedThreeQuarterRay_nonpos ht ht1
    dsimp [bracket] at hupper hmul hnormalized
    nlinarith

/-- The joining chord also survives the sharper overlap.  At `u ≤ 1/16`,
the two `B`-terms cost at most `A u/6`; the remaining nuisance budget is
`5 A u/16`, leaving a strict `A u/48` margin. -/
theorem threeQuarterChord_strict
    {A B C u linear quadratic cubic quartic quintic baseline : ℝ}
    (hA : 0 < A) (hB : 0 ≤ B) (hBA : 3 * B ≤ 4 * A)
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
  have hBupper : B ≤ 4 * A / 3 := by linarith
  have hquadratic' : quadratic ≤ A * u / 12 := by
    calc
      quadratic ≤ B * u ^ 2 := hquadratic
      _ ≤ (4 * A / 3) * u ^ 2 :=
        mul_le_mul_of_nonneg_right hBupper (sq_nonneg u)
      _ ≤ (4 * A / 3) * (u / 16) := by gcongr
      _ = A * u / 12 := by ring
  have hquartic' : quartic ≤ A * u / 12 := by
    calc
      quartic ≤ B * u ^ 4 := hquartic
      _ ≤ B * u ^ 2 := mul_le_mul_of_nonneg_left hu4 hB
      _ ≤ (4 * A / 3) * u ^ 2 :=
        mul_le_mul_of_nonneg_right hBupper (sq_nonneg u)
      _ ≤ (4 * A / 3) * (u / 16) := by gcongr
      _ = A * u / 12 := by ring
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

end ErdosProblems.Erdos1041.SexticFirstModeThreeQuarterOverlap
