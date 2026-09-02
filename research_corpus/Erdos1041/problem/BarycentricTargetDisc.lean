import Mathlib.Tactic

/-!
# Erdős #1041: augmented inverse-square target-disc kernels

The companion note proves the target-level disc by weighted AM--GM.  This
module checks the completed-square/radius transport, the exact ray reach and
boundary stall, and the scalar action estimate.  It does not assert a global
arclength bound or the unrestricted theorem.
-/

namespace ErdosProblems.Erdos1041.BarycentricTargetDisc

/-- Scalar form of the augmented completed-square implication. -/
theorem targetDisc_transport
    {S pSq zDistSq targetRatio yDistSq : ℝ}
    (hS : 0 < S)
    (hz : S * zDistSq = pSq / S)
    (hy : yDistSq ≤ zDistSq + (targetRatio - 1) / S) :
    1 + (S * yDistSq - pSq / S) ≤ targetRatio := by
  rw [← hz]
  have hmul := mul_le_mul_of_nonneg_left hy (le_of_lt hS)
  have hcancel : S * ((targetRatio - 1) / S) = targetRatio - 1 := by
    field_simp [ne_of_gt hS]
  rw [mul_add, hcancel] at hmul
  linarith

/-- The positive root of `s²-2αs-σ²=0`. -/
theorem rayReach_quadratic_identity {alpha sigmaSq : ℝ}
    (hsigma : 0 ≤ sigmaSq) :
    let reach := alpha + Real.sqrt (alpha ^ 2 + sigmaSq)
    reach ^ 2 - 2 * alpha * reach - sigmaSq = 0 := by
  dsimp
  have hrad : 0 ≤ alpha ^ 2 + sigmaSq := by positivity
  have hsqrt := Real.sq_sqrt hrad
  nlinarith

/-- Target-level slack gives positive certified reach in every direction. -/
theorem rayReach_pos_of_targetSlack {alpha sigmaSq : ℝ}
    (hsigma : 0 < sigmaSq) :
    0 < alpha + Real.sqrt (alpha ^ 2 + sigmaSq) := by
  have hsq : alpha ^ 2 < alpha ^ 2 + sigmaSq := by linarith
  have habs : |alpha| < Real.sqrt (alpha ^ 2 + sigmaSq) := by
    rw [← Real.sqrt_sq_eq_abs alpha]
    exact Real.sqrt_lt_sqrt (sq_nonneg alpha) hsq
  rcases le_total 0 alpha with ha | ha
  · positivity
  · rw [abs_of_nonpos ha] at habs
    linarith

/-- At zero target slack, an outward/noninward ray has no positive certified
reach.  This is the endpoint KKT stall in scalar form. -/
theorem boundary_stall
    {alpha s : ℝ} (halpha : alpha ≤ 0) (hs : 0 ≤ s)
    (hdisc : s ^ 2 - 2 * alpha * s ≤ 0) :
    s = 0 := by
  nlinarith [mul_nonpos_of_nonpos_of_nonneg halpha hs]

/-- The AM--GM lower bound `F*S ≥ n` turns the exact dissipation identity
`n*(-F')=2*F*S*speed²` into a quadratic-action estimate. -/
theorem energy_controls_action
    {F S n speedSq dissipation : ℝ}
    (hn : 0 < n) (hFS : n ≤ F * S) (hspeed : 0 ≤ speedSq)
    (hdiss : n * dissipation = 2 * F * S * speedSq) :
    2 * speedSq ≤ dissipation := by
  have hmul : 2 * n * speedSq ≤ n * dissipation := by
    rw [hdiss]
    nlinarith [mul_le_mul_of_nonneg_right hFS hspeed]
  nlinarith

/-- Strict mass slack and positive speed give strict action control. -/
theorem energy_controls_action_strict_of_strict_mass
    {F S n speedSq dissipation : ℝ}
    (hn : 0 < n) (hFS : n < F * S) (hspeed : 0 < speedSq)
    (hdiss : n * dissipation = 2 * F * S * speedSq) :
    2 * speedSq < dissipation := by
  have hmul : n * speedSq < F * S * speedSq :=
    mul_lt_mul_of_pos_right hFS hspeed
  have hbound : 2 * n * speedSq < n * dissipation := by
    rw [hdiss]
    nlinarith [hmul]
  by_contra hnot
  have hge : dissipation ≤ 2 * speedSq := le_of_not_gt hnot
  have hmul_le : n * dissipation ≤ n * (2 * speedSq) :=
    mul_le_mul_of_nonneg_left hge (le_of_lt hn)
  nlinarith [hbound, hmul_le]

end ErdosProblems.Erdos1041.BarycentricTargetDisc
