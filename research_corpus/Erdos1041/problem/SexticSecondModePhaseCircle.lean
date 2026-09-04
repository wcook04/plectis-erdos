import ErdosProblems.Erdos1041.SexticCanonicalMixedSlice
import Mathlib.Tactic

/-!
# Erdős #1041: the all-phase pure second-mode sextic circle

The canonical square-contact certificate at coefficient phase `π` and its
sixth-root rotation at phase `π/3` bound every intermediate phase.  This
module formalizes the three-rotation phase cover, the two-half cosine
envelope, the ray bound at the canonical algebraic radius, and the fan-in to
the existing canonical chord carrier.
-/

namespace ErdosProblems.Erdos1041.SexticSecondModePhaseCircle

open ErdosProblems.Erdos1041.SexticCanonicalMixedSlice

/-- Polar scalar form of `Re (exp(iθ) z² - z⁶)`. -/
noncomputable def phaseModel (rho alpha theta : ℝ) : ℝ :=
  rho ^ 2 * Real.cos (theta + 2 * alpha) - rho ^ 6 * Real.cos (6 * alpha)

/-- On the first half of an adjacent sixth-root chord, the largest
second-mode phase contribution over `[π/3,π]` occurs at `π/3`. -/
theorem phaseModel_le_leftBoundary
    {rho alpha theta : ℝ}
    (halpha0 : 0 ≤ alpha) (halpha1 : alpha ≤ Real.pi / 6)
    (htheta0 : Real.pi / 3 ≤ theta) (htheta1 : theta ≤ Real.pi) :
    phaseModel rho alpha theta ≤
      phaseModel rho alpha (Real.pi / 3) := by
  let x := theta + 2 * alpha
  let y := Real.pi / 3 + 2 * alpha
  have hxy : y ≤ x := by dsimp [x, y]; linarith
  have hsum0 : 0 ≤ (x + y) / 2 := by
    dsimp [x, y]
    nlinarith [Real.pi_pos.le]
  have hsumpi : (x + y) / 2 ≤ Real.pi := by
    dsimp [x, y]
    nlinarith [Real.pi_pos.le]
  have hdiff0 : 0 ≤ (x - y) / 2 := by linarith
  have hdiffpi : (x - y) / 2 ≤ Real.pi := by
    dsimp [x, y]
    nlinarith [Real.pi_pos.le]
  have hs1 : 0 ≤ Real.sin ((x + y) / 2) :=
    Real.sin_nonneg_of_nonneg_of_le_pi hsum0 hsumpi
  have hs2 : 0 ≤ Real.sin ((x - y) / 2) :=
    Real.sin_nonneg_of_nonneg_of_le_pi hdiff0 hdiffpi
  have hcos : Real.cos x ≤ Real.cos y := by
    have hid := Real.cos_sub_cos x y
    nlinarith [mul_nonneg hs1 hs2]
  unfold phaseModel
  exact sub_le_sub_right
    (mul_le_mul_of_nonneg_left hcos (sq_nonneg rho)) _

/-- On the second half, the largest phase contribution occurs at `π`. -/
theorem phaseModel_le_rightBoundary
    {rho alpha theta : ℝ}
    (halpha0 : Real.pi / 6 ≤ alpha) (halpha1 : alpha ≤ Real.pi / 3)
    (htheta0 : Real.pi / 3 ≤ theta) (htheta1 : theta ≤ Real.pi) :
    phaseModel rho alpha theta ≤ phaseModel rho alpha Real.pi := by
  let x := theta + 2 * alpha
  let y := Real.pi + 2 * alpha
  have hxy : x ≤ y := by dsimp [x, y]; linarith
  have hsumPi : Real.pi ≤ (x + y) / 2 := by
    dsimp [x, y]
    nlinarith [Real.pi_pos.le]
  have hsumTwoPi : (x + y) / 2 ≤ 2 * Real.pi := by
    dsimp [x, y]
    nlinarith [Real.pi_pos.le]
  have hsumShift0 : (x + y) / 2 - 2 * Real.pi ≤ 0 := by linarith
  have hsumShiftPi : -Real.pi ≤ (x + y) / 2 - 2 * Real.pi := by linarith
  have hs1 : Real.sin ((x + y) / 2) ≤ 0 := by
    rw [← Real.sin_sub_two_pi]
    exact Real.sin_nonpos_of_nonpos_of_neg_pi_le hsumShift0 hsumShiftPi
  have hdiff0 : (x - y) / 2 ≤ 0 := by linarith
  have hdiffPi : -Real.pi ≤ (x - y) / 2 := by
    dsimp [x, y]
    nlinarith [Real.pi_pos.le]
  have hs2 : Real.sin ((x - y) / 2) ≤ 0 :=
    Real.sin_nonpos_of_nonpos_of_neg_pi_le hdiff0 hdiffPi
  have hcos : Real.cos x ≤ Real.cos y := by
    have hid := Real.cos_sub_cos x y
    nlinarith [mul_nonneg_of_nonpos_of_nonpos hs1 hs2]
  unfold phaseModel
  exact sub_le_sub_right
    (mul_le_mul_of_nonneg_left hcos (sq_nonneg rho)) _

/-- Three second-mode phase rotations cover the full circle by the base
sector `[π/3,π]`; the fourth displayed alternative handles wrap-around. -/
theorem threeRotationSector_cover {phi : ℝ}
    (hphi0 : 0 ≤ phi) (hphi1 : phi ≤ 2 * Real.pi) :
    (Real.pi / 3 ≤ phi + 2 * Real.pi / 3 ∧
      phi + 2 * Real.pi / 3 ≤ Real.pi) ∨
    (Real.pi / 3 ≤ phi ∧ phi ≤ Real.pi) ∨
    (Real.pi / 3 ≤ phi - 2 * Real.pi / 3 ∧
      phi - 2 * Real.pi / 3 ≤ Real.pi) ∨
    (Real.pi / 3 ≤ phi - 4 * Real.pi / 3 ∧
      phi - 4 * Real.pi / 3 ≤ Real.pi) := by
  by_cases h0 : phi ≤ Real.pi / 3
  · exact Or.inl ⟨by linarith, by linarith⟩
  by_cases h1 : phi ≤ Real.pi
  · exact Or.inr (Or.inl ⟨by linarith, h1⟩)
  by_cases h2 : phi ≤ 5 * Real.pi / 3
  · exact Or.inr (Or.inr (Or.inl ⟨by linarith, by linarith⟩))
  · exact Or.inr (Or.inr (Or.inr ⟨by linarith, by linarith⟩))

/-- A ray whose second-mode projection is at most `1/2` is safe outward from
the canonical radius because `radius^4=q>1/2`. -/
theorem secondModeRay_nonpos
    {p x : ℝ} (hp : p ≤ 1 / 2)
    (hx : radius ≤ x) :
    x ^ 2 * p - x ^ 6 ≤ 0 := by
  have hx0 : 0 ≤ x := radius_nonneg.trans hx
  have hxpow : radius ^ 4 ≤ x ^ 4 :=
    pow_le_pow_left₀ radius_nonneg hx 4
  rw [radius_fourth] at hxpow
  have hpq0 : p ≤ q := hp.trans (le_of_lt half_lt_q)
  have hpq : p ≤ x ^ 4 := hpq0.trans hxpow
  have hfactor : x ^ 2 * p - x ^ 6 = x ^ 2 * (p - x ^ 4) := by ring
  rw [hfactor]
  exact mul_nonpos_of_nonneg_of_nonpos (sq_nonneg x) (sub_nonpos.mpr hpq)

/-- The existing canonical carrier gives the `π` boundary chord. -/
theorem rightBoundaryCarrier_nonpos {r t value : ℝ}
    (ht0 : 0 ≤ t) (ht1 : t ≤ 1)
    (hvalue : value = -(r ^ 2) * chordCarrier t) :
    value ≤ 0 := by
  rw [hvalue]
  have hc := chordCarrier_nonneg ht0 ht1
  nlinarith [mul_nonneg (sq_nonneg r) hc]

/-- Rotation and chord reversal give the `π/3` boundary from the same
canonical carrier. -/
theorem leftBoundaryCarrier_nonpos {r t value : ℝ}
    (ht0 : 0 ≤ t) (ht1 : t ≤ 1)
    (hvalue : value = -(r ^ 2) * chordCarrier (1 - t)) :
    value ≤ 0 := by
  rw [hvalue]
  have hc := chordCarrier_nonneg (sub_nonneg.mpr ht1) (by linarith)
  nlinarith [mul_nonneg (sq_nonneg r) hc]

/-- Fan-in theorem: the two canonical boundary identities and the phase
envelope prove every phase in the base sector. -/
theorem phaseCircle_chord_nonpos
    {rho alpha theta t : ℝ}
    (halpha0 : 0 ≤ alpha) (halpha1 : alpha ≤ Real.pi / 3)
    (htheta0 : Real.pi / 3 ≤ theta) (htheta1 : theta ≤ Real.pi)
    (ht0 : 0 ≤ t) (ht1 : t ≤ 1)
    (hleft : phaseModel rho alpha (Real.pi / 3) =
      -(rho ^ 2) * chordCarrier (1 - t))
    (hright : phaseModel rho alpha Real.pi =
      -(rho ^ 2) * chordCarrier t) :
    phaseModel rho alpha theta ≤ 0 := by
  by_cases halpha : alpha ≤ Real.pi / 6
  · have henvelope := phaseModel_le_leftBoundary
      halpha0 halpha htheta0 htheta1 (rho := rho)
    have hboundary := leftBoundaryCarrier_nonpos
      (r := rho) (t := t) (value := phaseModel rho alpha (Real.pi / 3))
      ht0 ht1 hleft
    linarith
  · have halpha' : Real.pi / 6 ≤ alpha := le_of_not_ge halpha
    have henvelope := phaseModel_le_rightBoundary
      halpha' halpha1 htheta0 htheta1 (rho := rho)
    have hboundary := rightBoundaryCarrier_nonpos
      (r := rho) (t := t) (value := phaseModel rho alpha Real.pi)
      ht0 ht1 hright
    linarith

end ErdosProblems.Erdos1041.SexticSecondModePhaseCircle
