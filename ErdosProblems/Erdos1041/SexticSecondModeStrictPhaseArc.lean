import ErdosProblems.Erdos1041.SexticSecondModePhaseCircle
import Mathlib.Tactic

/-!
# Erdős #1041: strictness away from canonical second-mode phases

The all-phase pure second-mode connector can touch its boundary only at the
two canonical endpoint phases of the reduced sector.  Every interior phase
has a strictly negative chord.  This supplies the open stability collar used
by the mixed sextic atlas away from the canonical null-box charts.
-/

namespace ErdosProblems.Erdos1041.SexticSecondModeStrictPhaseArc

open ErdosProblems.Erdos1041.SexticCanonicalMixedSlice
open ErdosProblems.Erdos1041.SexticSecondModePhaseCircle

/-- Strict first-half phase envelope for an interior coefficient phase. -/
theorem phaseModel_lt_leftBoundary
    {rho alpha theta : ℝ}
    (hrho : 0 < rho)
    (halpha0 : 0 ≤ alpha) (halpha1 : alpha ≤ Real.pi / 6)
    (htheta0 : Real.pi / 3 < theta) (htheta1 : theta < Real.pi) :
    phaseModel rho alpha theta < phaseModel rho alpha (Real.pi / 3) := by
  let x := theta + 2 * alpha
  let y := Real.pi / 3 + 2 * alpha
  have hxy : y < x := by dsimp [x, y]; linarith
  have hsum0 : 0 < (x + y) / 2 := by
    dsimp [x, y]
    nlinarith [Real.pi_pos]
  have hsumpi : (x + y) / 2 < Real.pi := by
    dsimp [x, y]
    nlinarith [Real.pi_pos]
  have hdiff0 : 0 < (x - y) / 2 := by linarith
  have hdiffpi : (x - y) / 2 < Real.pi := by
    dsimp [x, y]
    nlinarith [Real.pi_pos]
  have hs1 : 0 < Real.sin ((x + y) / 2) :=
    Real.sin_pos_of_pos_of_lt_pi hsum0 hsumpi
  have hs2 : 0 < Real.sin ((x - y) / 2) :=
    Real.sin_pos_of_pos_of_lt_pi hdiff0 hdiffpi
  have hcos : Real.cos x < Real.cos y := by
    have hid := Real.cos_sub_cos x y
    nlinarith [mul_pos hs1 hs2]
  unfold phaseModel
  have hrhoSq : 0 < rho ^ 2 := sq_pos_of_pos hrho
  exact sub_lt_sub_right (mul_lt_mul_of_pos_left hcos hrhoSq) _

/-- Strict second-half phase envelope for an interior coefficient phase. -/
theorem phaseModel_lt_rightBoundary
    {rho alpha theta : ℝ}
    (hrho : 0 < rho)
    (halpha0 : Real.pi / 6 ≤ alpha) (halpha1 : alpha ≤ Real.pi / 3)
    (htheta0 : Real.pi / 3 < theta) (htheta1 : theta < Real.pi) :
    phaseModel rho alpha theta < phaseModel rho alpha Real.pi := by
  let x := theta + 2 * alpha
  let y := Real.pi + 2 * alpha
  have hxy : x < y := by dsimp [x, y]; linarith
  have hsumPi : Real.pi < (x + y) / 2 := by
    dsimp [x, y]
    nlinarith [Real.pi_pos]
  have hsumTwoPi : (x + y) / 2 < 2 * Real.pi := by
    dsimp [x, y]
    nlinarith [Real.pi_pos]
  have hsumShift0 : (x + y) / 2 - 2 * Real.pi < 0 := by linarith
  have hsumShiftPi : -Real.pi < (x + y) / 2 - 2 * Real.pi := by linarith
  have hs1 : Real.sin ((x + y) / 2) < 0 := by
    rw [← Real.sin_sub_two_pi]
    exact Real.sin_neg_of_neg_of_neg_pi_lt hsumShift0 hsumShiftPi
  have hdiff0 : (x - y) / 2 < 0 := by linarith
  have hdiffPi : -Real.pi < (x - y) / 2 := by
    dsimp [x, y]
    nlinarith [Real.pi_pos]
  have hs2 : Real.sin ((x - y) / 2) < 0 :=
    Real.sin_neg_of_neg_of_neg_pi_lt hdiff0 hdiffPi
  have hcos : Real.cos x < Real.cos y := by
    have hid := Real.cos_sub_cos x y
    nlinarith [mul_pos_of_neg_of_neg hs1 hs2]
  unfold phaseModel
  have hrhoSq : 0 < rho ^ 2 := sq_pos_of_pos hrho
  exact sub_lt_sub_right (mul_lt_mul_of_pos_left hcos hrhoSq) _

/-- Every interior phase in the reduced sector has a strictly negative
canonical-radius chord. -/
theorem interiorPhase_chord_strict
    {rho alpha theta t : ℝ}
    (hrho : 0 < rho)
    (halpha0 : 0 ≤ alpha) (halpha1 : alpha ≤ Real.pi / 3)
    (htheta0 : Real.pi / 3 < theta) (htheta1 : theta < Real.pi)
    (ht0 : 0 ≤ t) (ht1 : t ≤ 1)
    (hleft : phaseModel rho alpha (Real.pi / 3) =
      -(rho ^ 2) * chordCarrier (1 - t))
    (hright : phaseModel rho alpha Real.pi =
      -(rho ^ 2) * chordCarrier t) :
    phaseModel rho alpha theta < 0 := by
  by_cases halpha : alpha ≤ Real.pi / 6
  · have henvelope := phaseModel_lt_leftBoundary
      hrho halpha0 halpha htheta0 htheta1
    have hboundary := leftBoundaryCarrier_nonpos
      (r := rho) (t := t) (value := phaseModel rho alpha (Real.pi / 3))
      ht0 ht1 hleft
    linarith
  · have halpha' : Real.pi / 6 ≤ alpha := le_of_not_ge halpha
    have henvelope := phaseModel_lt_rightBoundary
      hrho halpha' halpha1 htheta0 htheta1
    have hboundary := rightBoundaryCarrier_nonpos
      (r := rho) (t := t) (value := phaseModel rho alpha Real.pi)
      ht0 ht1 hright
    linarith

/-- Equality in the phase-envelope route can occur only at an endpoint phase
of the reduced sector. -/
theorem equality_forces_canonical_phase
    {theta : ℝ} (htheta0 : Real.pi / 3 ≤ theta)
    (htheta1 : theta ≤ Real.pi)
    (hnotInterior : ¬ (Real.pi / 3 < theta ∧ theta < Real.pi)) :
    theta = Real.pi / 3 ∨ theta = Real.pi := by
  by_cases hleft : theta = Real.pi / 3
  · exact Or.inl hleft
  · right
    have hleftStrict : Real.pi / 3 < theta := lt_of_le_of_ne htheta0 (Ne.symm hleft)
    by_contra hright
    have hrightStrict : theta < Real.pi := lt_of_le_of_ne htheta1 hright
    exact hnotInterior ⟨hleftStrict, hrightStrict⟩

end ErdosProblems.Erdos1041.SexticSecondModeStrictPhaseArc
