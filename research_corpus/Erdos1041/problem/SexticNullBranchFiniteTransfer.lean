import ErdosProblems.Erdos1041.SexticNullBranchSecondOrderAtlas

/-!
# Erdős #1041: quantitative finite transfer of the sextic null atlas

This module formalizes the load-bearing selection and remainder absorption for
the finite-beta homogeneous sextic family.  The companion exact checker
verifies that the explicit chord functions satisfy the analytic budgets used
here on the stated coefficient box.
-/

namespace ErdosProblems.Erdos1041.SexticNullBranchFiniteTransfer

noncomputable section

open ErdosProblems.Erdos1041.SexticNullBranchSecondOrderAtlas

def betaCutoff : ℝ := 1 / 1000000000
def localRemainderBudget : ℝ := 40500000

theorem betaCutoff_nonneg : 0 ≤ betaCutoff := by
  norm_num [betaCutoff]

theorem remainder_absorbed {β : ℝ} (_hβ0 : 0 ≤ β) (hβ : β ≤ betaCutoff) :
    localRemainderBudget * β ≤ (1 / 20 : ℝ) := by
  unfold localRemainderBudget betaCutoff at *
  nlinarith

/-- A limiting profile below `-3/5` retains a finite margin after the explicit
third-order remainder budget is paid. -/
theorem localEnvelope_transfer {β profile actual : ℝ}
    (hβ0 : 0 ≤ β) (hβ : β ≤ betaCutoff)
    (hprofile : profile ≤ (-3 / 5 : ℝ))
    (hactual : actual ≤ β ^ 2 * (profile + localRemainderBudget * β)) :
    actual ≤ -(β ^ 2) / 2 := by
  have hrem := remainder_absorbed hβ0 hβ
  have hsq : 0 ≤ β ^ 2 := sq_nonneg β
  have hsum : profile + localRemainderBudget * β ≤ (-11 / 20 : ℝ) := by
    linarith
  have hmul := mul_le_mul_of_nonneg_left hsum hsq
  nlinarith

/-- The coarse outer-region estimate is already strongly negative once the
contact displacement is at least `100 * beta`. -/
theorem outerEnvelope_transfer {β y actual : ℝ}
    (hβ0 : 0 ≤ β) (hβ : β ≤ betaCutoff) (hy : 100 * β ≤ y)
    (hactual :
      actual ≤ -(2 / 5 : ℝ) * y ^ 2 + 24 * β * y +
        1000 * β ^ 2 + 1000 * β ^ 3) :
    actual ≤ -(β ^ 2) / 2 := by
  have hy0 : 0 ≤ y := by nlinarith
  have hβy : 100 * β * y ≤ y ^ 2 := by
    have := mul_le_mul_of_nonneg_right hy hy0
    nlinarith
  have hβ2 : 100 * β ^ 2 ≤ β * y := by
    have hm := mul_le_mul_of_nonneg_left hy hβ0
    nlinarith
  have hsq : 10000 * β ^ 2 ≤ y ^ 2 := by
    nlinarith
  have hsmall : 1000 * β ≤ 1 := by
    unfold betaCutoff at hβ
    nlinarith
  have hcubic : 1000 * β ^ 3 ≤ β ^ 2 := by
    have hm := mul_le_mul_of_nonneg_left hsmall (sq_nonneg β)
    nlinarith
  nlinarith

/-- The second-order atlas plus the finite remainder envelope selects one
whole connector with margin `-beta^2/2`. -/
theorem finiteBeta_four_connector_cover
    {β p q r : ℝ} {fPP fNP fNN fPN : ℝ → ℝ}
    (hβ0 : 0 ≤ β) (hβ : β ≤ betaCutoff)
    (hPP : ∀ t, fPP t ≤ β ^ 2 *
      (profilePP p q r + localRemainderBudget * β))
    (hNP : ∀ t, fNP t ≤ β ^ 2 *
      (profileNP p q r + localRemainderBudget * β))
    (hNN : ∀ t, fNN t ≤ β ^ 2 *
      (profileNN p q r + localRemainderBudget * β))
    (hPN : ∀ t, fPN t ≤ β ^ 2 *
      (profilePN p q r + localRemainderBudget * β)) :
    (∀ t, fPP t ≤ -(β ^ 2) / 2) ∨
    (∀ t, fNP t ≤ -(β ^ 2) / 2) ∨
    (∀ t, fNN t ≤ -(β ^ 2) / 2) ∨
    (∀ t, fPN t ≤ -(β ^ 2) / 2) := by
  rcases secondOrder_four_connector_cover p q r with h | h | h | h
  · exact Or.inl (fun t => localEnvelope_transfer hβ0 hβ h (hPP t))
  · exact Or.inr (Or.inl (fun t => localEnvelope_transfer hβ0 hβ h (hNP t)))
  · exact Or.inr (Or.inr (Or.inl
      (fun t => localEnvelope_transfer hβ0 hβ h (hNN t))))
  · exact Or.inr (Or.inr (Or.inr
      (fun t => localEnvelope_transfer hβ0 hβ h (hPN t))))

theorem fixedRaySlack_absorb {base perturb actual : ℝ}
    (hbase : base ≤ (-1 / 100 : ℝ))
    (hperturb : perturb ≤ (1 / 200 : ℝ))
    (hactual : actual ≤ base + perturb) :
    actual ≤ (-1 / 200 : ℝ) := by
  linarith

theorem adjacentConnectorLength_lt_two {ρ : ℝ} (hρ : 0 < ρ) :
    2 - ρ < (2 : ℝ) := by
  linarith

end

end ErdosProblems.Erdos1041.SexticNullBranchFiniteTransfer
