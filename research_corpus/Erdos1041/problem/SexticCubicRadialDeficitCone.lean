import ErdosProblems.Erdos1041.CyclicTrinomialFiberCase
import ErdosProblems.Erdos1041.SexticCanonicalMixedSlice
import Mathlib.Tactic

/-!
# Erdős #1041: a radial-deficit staple around the sextic cubic face

For the finite sextic Fourier model

`G(z) = -delta + Re(E₁ z + E₂ z² + E₃ z³ + E₄ z⁴ + E₅ z⁵ - z⁶)`,

assume the four non-cubic mode norms sum to at most `delta`, while the cubic
coefficient has norm at most one.  Put `s = delta / 4`.  One parity class of
sixth-root directions makes the cubic projection nonpositive.  On those three
rays the nuisance modes spend at most the radial deficit, and the entire disk
of radius `s` has a uniform `delta / 2` margin.  Two rays of that parity and a
chord through the inner disk therefore form a strict short staple.

The companion analytic note supplies the sixth-root geometry.  This module
checks the scalar mode budgets, inner-disk absorption, ray margin, parity
selection, and strict metric slack.
-/

namespace ErdosProblems.Erdos1041.SexticCubicRadialDeficitCone

noncomputable section

abbrev sqrtThree : ℝ :=
  ErdosProblems.Erdos1041.SexticCanonicalMixedSlice.sqrtThree

/-- Four nonnegative nuisance-mode budgets on `[0,1]` are bounded by their
sum times the radius. -/
theorem fourModes_le_linear
    {t e1 e2 e4 e5 : ℝ}
    (ht : 0 ≤ t) (ht1 : t ≤ 1)
    (he2 : 0 ≤ e2) (he4 : 0 ≤ e4) (he5 : 0 ≤ e5) :
    e1 * t + e2 * t ^ 2 + e4 * t ^ 4 + e5 * t ^ 5 ≤
      (e1 + e2 + e4 + e5) * t := by
  have ht2 : t ^ 2 ≤ t :=
    by simpa using
      (ErdosProblems.Erdos1041.unitInterval_pow_anti
        (r := 1) (m := 2) ht ht1 (by omega))
  have ht4 : t ^ 4 ≤ t :=
    by simpa using
      (ErdosProblems.Erdos1041.unitInterval_pow_anti
        (r := 1) (m := 4) ht ht1 (by omega))
  have ht5 : t ^ 5 ≤ t :=
    by simpa using
      (ErdosProblems.Erdos1041.unitInterval_pow_anti
        (r := 1) (m := 5) ht ht1 (by omega))
  nlinarith [mul_le_mul_of_nonneg_left ht2 he2,
    mul_le_mul_of_nonneg_left ht4 he4,
    mul_le_mul_of_nonneg_left ht5 he5]

/-- If the four nuisance norms spend at most `delta`, their value on the unit
disk is at most `delta * t`. -/
theorem fourModes_le_delta_mul
    {delta t e1 e2 e4 e5 modeValue : ℝ}
    (ht : 0 ≤ t) (ht1 : t ≤ 1)
    (he2 : 0 ≤ e2) (he4 : 0 ≤ e4) (he5 : 0 ≤ e5)
    (hsum : e1 + e2 + e4 + e5 ≤ delta)
    (hmode : modeValue ≤ e1 * t + e2 * t ^ 2 + e4 * t ^ 4 + e5 * t ^ 5) :
    modeValue ≤ delta * t := by
  have hweighted := fourModes_le_linear (e1 := e1) ht ht1 he2 he4 he5
  have hsumWeighted := mul_le_mul_of_nonneg_right hsum ht
  nlinarith

/-- At radius at most `delta/4`, the radial deficit absorbs every nuisance
mode, the unit-bounded cubic mode, and the sextic baseline with margin
`delta/2`. -/
theorem innerDisk_margin
    {delta u nuisance cubic baseline : ℝ}
    (hdelta : 0 < delta) (hdelta1 : delta ≤ 1)
    (hu : 0 ≤ u) (huradius : u ≤ delta / 4)
    (hnuisance : nuisance ≤ delta * u)
    (hcubic : cubic ≤ u ^ 3)
    (hbaseline : baseline ≤ u ^ 6) :
    -delta + nuisance + cubic + baseline ≤ -delta / 2 := by
  have hdelta0 : 0 ≤ delta := le_of_lt hdelta
  have huQuarter : u ≤ 1 / 4 := by linarith
  have hu1 : u ≤ 1 := by linarith
  have huSq : u ^ 2 ≤ 1 / 16 := by
    nlinarith [mul_nonneg hu (sub_nonneg.mpr huQuarter)]
  have huCube : u ^ 3 ≤ delta / 64 := by
    calc
      u ^ 3 = u ^ 2 * u := by ring
      _ ≤ (1 / 16 : ℝ) * u := mul_le_mul_of_nonneg_right huSq hu
      _ ≤ (1 / 16 : ℝ) * (delta / 4) :=
        mul_le_mul_of_nonneg_left huradius (by norm_num)
      _ = delta / 64 := by ring
  have huSixLeCube : u ^ 6 ≤ u ^ 3 :=
    ErdosProblems.Erdos1041.unitInterval_pow_anti (r := 3) (m := 6) hu hu1 (by omega)
  have hdeltaU : delta * u ≤ delta / 4 := by
    have := mul_le_mul_of_nonneg_left huQuarter hdelta0
    nlinarith
  nlinarith

/-- On a parity-selected ray the cubic term is nonpositive.  The nuisance
budget can spend the whole radial deficit and the strict sextic term still
forces negativity away from the origin. -/
theorem selectedRay_strict
    {delta t nuisance cubic : ℝ}
    (hdelta : 0 < delta) (ht : 0 < t) (ht1 : t ≤ 1)
    (hnuisance : nuisance ≤ delta * t) (hcubic : cubic ≤ 0) :
    -delta + nuisance + cubic - t ^ 6 < 0 := by
  have ht0 : 0 ≤ t := le_of_lt ht
  have hdelta0 : 0 ≤ delta := le_of_lt hdelta
  have hspend : delta * t ≤ delta := by
    nlinarith [mul_nonneg hdelta0 (sub_nonneg.mpr ht1)]
  have hsix : 0 < t ^ 6 := pow_pos ht 6
  linarith

/-- Multiplication by one of the two parity signs always makes a real cubic
projection nonpositive. -/
theorem exists_parity_sign_nonpos (x : ℝ) :
    ∃ epsilon : ℝ, (epsilon = 1 ∨ epsilon = -1) ∧ epsilon * x ≤ 0 := by
  by_cases hx : 0 ≤ x
  · refine ⟨-1, Or.inr rfl, ?_⟩
    linarith
  · refine ⟨1, Or.inl rfl, ?_⟩
    simp
    exact le_of_not_ge hx

/-- Two same-parity sixth-root directions have chord factor `sqrt 3`, so a
staple truncated at any positive radius is strictly shorter than two. -/
theorem sameParity_staple_length_lt_two {s : ℝ} (hs : 0 < s) :
    2 * (1 - s) + sqrtThree * s < 2 := by
  have hsqrt0 : 0 ≤ sqrtThree := le_of_lt
    ErdosProblems.Erdos1041.SexticCanonicalMixedSlice.sqrtThree_pos
  have hsqrtSq : sqrtThree ^ 2 = 3 :=
    ErdosProblems.Erdos1041.SexticCanonicalMixedSlice.sqrtThree_sq
  have hsqrtLt : sqrtThree < 2 := by
    nlinarith
  nlinarith

/-- The canonical truncation radius is positive and at most one quarter. -/
theorem truncationRadius_bounds {delta : ℝ}
    (hdelta : 0 < delta) (hdelta1 : delta ≤ 1) :
    0 < delta / 4 ∧ delta / 4 ≤ 1 / 4 := by
  constructor <;> linarith

end

end ErdosProblems.Erdos1041.SexticCubicRadialDeficitCone
