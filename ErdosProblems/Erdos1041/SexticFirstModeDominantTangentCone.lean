import ErdosProblems.Erdos1041.SexticCubicTransitionCone
import Mathlib.Tactic

/-!
# Erdős #1041: the first-mode-dominant sextic tangent cone

For a pure tangent perturbation, conjugate Fourier modes pair exactly.  On a
sixth-root ray the cubic mode vanishes and the first two pairs reduce to

`(t - t^5) a + (t^2 - t^4) b`.

Two adjacent directions have first-mode projections at most `-A/2`.  If the
second-mode norm is at most `A`, a factorization makes both complete rays
nonpositive.  A sufficiently small adjacent chord is strictly negative.
The module also checks positivity of the radial geometric kernel that makes
inward root motion favourable on sixth-root rays.
-/

namespace ErdosProblems.Erdos1041.SexticFirstModeDominantTangentCone

/-- The paired tangent value on a sixth-root ray. -/
def pairedTangentRay (a b t : ℝ) : ℝ :=
  (t - t ^ 5) * a + (t ^ 2 - t ^ 4) * b - t ^ 6

/-- First-mode dominance makes every ray with first projection at most
`-A/2` safe, independently of the phase of the second mode. -/
theorem pairedTangentRay_nonpos
    {A a b t : ℝ}
    (hA : 0 ≤ A) (ht : 0 ≤ t) (ht1 : t ≤ 1)
    (ha : a ≤ -A / 2) (hb : b ≤ A) :
    pairedTangentRay a b t ≤ 0 := by
  have ht5 : t ^ 5 ≤ t :=
    by simpa using
      (ErdosProblems.Erdos1041.unitInterval_pow_anti
        (r := 1) (m := 5) ht ht1 (by omega))
  have ht4 : t ^ 4 ≤ t ^ 2 :=
    ErdosProblems.Erdos1041.unitInterval_pow_anti
      (r := 2) (m := 4) ht ht1 (by omega)
  have hfirst := mul_le_mul_of_nonneg_left ha (sub_nonneg.mpr ht5)
  have hsecond := mul_le_mul_of_nonneg_left hb (sub_nonneg.mpr ht4)
  have htSq : 0 ≤ 1 - t ^ 2 := by nlinarith [sq_nonneg t]
  have hfactor : 0 ≤ A * t * (1 - t ^ 2) * (t - 1) ^ 2 := by positivity
  have hidentity :
      (-A / 2) * (t - t ^ 5) + A * (t ^ 2 - t ^ 4) - t ^ 6 =
        -(A * t * (1 - t ^ 2) * (t - 1) ^ 2) / 2 - t ^ 6 := by
    ring
  unfold pairedTangentRay
  rw [hidentity] at *
  nlinarith [pow_nonneg ht 6]

/-- Six translates of `[2π/3,π]` cover one phase period.  In that sector
the chosen direction and its adjacent successor both have cosine at most
`-1/2`. -/
theorem sixPhaseSector_cover {phi : ℝ}
    (hphi0 : 0 ≤ phi) (hphi1 : phi ≤ 2 * Real.pi) :
    (2 * Real.pi / 3 ≤ phi + 2 * Real.pi / 3 ∧
      phi + 2 * Real.pi / 3 ≤ Real.pi) ∨
    (2 * Real.pi / 3 ≤ phi + Real.pi / 3 ∧
      phi + Real.pi / 3 ≤ Real.pi) ∨
    (2 * Real.pi / 3 ≤ phi ∧ phi ≤ Real.pi) ∨
    (2 * Real.pi / 3 ≤ phi - Real.pi / 3 ∧
      phi - Real.pi / 3 ≤ Real.pi) ∨
    (2 * Real.pi / 3 ≤ phi - 2 * Real.pi / 3 ∧
      phi - 2 * Real.pi / 3 ≤ Real.pi) ∨
    (2 * Real.pi / 3 ≤ phi - Real.pi ∧
      phi - Real.pi ≤ Real.pi) := by
  by_cases h0 : phi ≤ Real.pi / 3
  · exact Or.inl ⟨by linarith, by linarith⟩
  by_cases h1 : phi ≤ 2 * Real.pi / 3
  · exact Or.inr (Or.inl ⟨by linarith, by linarith⟩)
  by_cases h2 : phi ≤ Real.pi
  · exact Or.inr (Or.inr (Or.inl ⟨by linarith, h2⟩))
  by_cases h3 : phi ≤ 4 * Real.pi / 3
  · exact Or.inr (Or.inr (Or.inr (Or.inl ⟨by linarith, by linarith⟩)))
  by_cases h4 : phi ≤ 5 * Real.pi / 3
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨by linarith, by linarith⟩))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr ⟨by linarith, by linarith⟩))))

/-- A small chord between the two selected adjacent rays is strictly safe.
The hypotheses are explicit scale conditions; positive `A` always admits a
positive `u` satisfying them. -/
theorem adjacentChord_strict
    {A C u linear quadratic cubic quartic quintic baseline : ℝ}
    (hA : 0 < A)
    (hu : 0 < u) (hu16 : u ≤ 1 / 16)
    (hlinear : linear ≤ -A * u / 2)
    (hquadratic : quadratic ≤ A * u ^ 2)
    (hcubic : cubic ≤ C * u ^ 3)
    (hquartic : quartic ≤ A * u ^ 4)
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
  have hquadratic' : quadratic ≤ A * u / 16 := by
    calc
      quadratic ≤ A * u ^ 2 := hquadratic
      _ ≤ A * (u / 16) := mul_le_mul_of_nonneg_left huSq hA0
      _ = A * u / 16 := by ring
  have hquartic' : quartic ≤ A * u / 16 := by
    calc
      quartic ≤ A * u ^ 4 := hquartic
      _ ≤ A * u ^ 2 := mul_le_mul_of_nonneg_left hu4 hA0
      _ ≤ A * (u / 16) := mul_le_mul_of_nonneg_left huSq hA0
      _ = A * u / 16 := by ring
  have hquintic' : quintic ≤ A * u / 16 := by
    calc
      quintic ≤ A * u ^ 5 := hquintic
      _ ≤ A * u ^ 2 := mul_le_mul_of_nonneg_left hu5 hA0
      _ ≤ A * (u / 16) := mul_le_mul_of_nonneg_left huSq hA0
      _ = A * u / 16 := by ring
  have hpaired :
      quadratic + quartic + quintic ≤ 3 * A * u / 16 := by
    nlinarith
  have hcubic' : cubic ≤ A * u / 8 := by
    have hmul := mul_le_mul_of_nonneg_right hCscale (by positivity : 0 ≤ u / 8)
    nlinarith
  have hbaseline' : baseline ≤ A * u / 8 := by
    have hmul := mul_le_mul_of_nonneg_right hbaseScale (by positivity : 0 ≤ u / 8)
    nlinarith
  nlinarith [mul_pos hA hu]

/-- The denominator in the real-part formula for a unit-circle geometric
kernel is positive inside the unit disk. -/
theorem geometricKernel_den_pos
  {t c : ℝ} (ht : 0 ≤ t) (ht1 : t < 1) (hc : c ≤ 1) :
    0 < 1 - 2 * t * c + t ^ 2 := by
  have htc : 0 ≤ 2 * t * (1 - c) :=
    mul_nonneg (mul_nonneg (by norm_num) ht) (sub_nonneg.mpr hc)
  have hone : 0 < (1 - t) ^ 2 := sq_pos_of_pos (sub_pos.mpr ht1)
  nlinarith

/-- The numerator in the same kernel formula is positive. -/
theorem geometricKernel_num_pos
    {t c : ℝ} (ht : 0 ≤ t) (ht1 : t < 1) (hc : c ≤ 1) :
    0 < (1 - t ^ 6) * (1 - t * c) := by
  have htc : t * c ≤ t := by
    simpa using (mul_le_mul_of_nonneg_left hc ht)
  have hsecond : 0 < 1 - t * c := by linarith
  have hpoly : 0 < 1 + t + t ^ 2 + t ^ 3 + t ^ 4 + t ^ 5 := by positivity
  have hfirst : 0 < 1 - t ^ 6 := by
    have hid : 1 - t ^ 6 =
        (1 - t) * (1 + t + t ^ 2 + t ^ 3 + t ^ 4 + t ^ 5) := by ring
    rw [hid]
    exact mul_pos (sub_pos.mpr ht1) hpoly
  exact mul_pos hfirst hsecond

/-- Therefore the real part of the length-six geometric kernel is positive;
`c` is the real part of the relevant sixth root. -/
theorem geometricKernel_real_pos
    {t c : ℝ} (ht : 0 ≤ t) (ht1 : t < 1) (hc : c ≤ 1) :
    0 < ((1 - t ^ 6) * (1 - t * c)) /
      (1 - 2 * t * c + t ^ 2) := by
  exact div_pos (geometricKernel_num_pos ht ht1 hc)
    (geometricKernel_den_pos ht ht1 hc)

end ErdosProblems.Erdos1041.SexticFirstModeDominantTangentCone
