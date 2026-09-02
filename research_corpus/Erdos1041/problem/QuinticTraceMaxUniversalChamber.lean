import Mathlib

/-!
# Erdős 1041: exact algebra for the quintic trace-max universal chamber

This module checks the proof-bearing polynomial identities in
`QuinticTraceMaxUniversalChamber.md`.  The compactness/Rouché argument and the
inverse-branch excess functional remain ordinary complex analysis.
-/

namespace ErdosProblems.Erdos1041

/-- Taylor expansion of a low-mode quintic at a critical point. -/
theorem quintic_center_at_critical
    (c b₁ b₂ x : ℂ)
    (hc : 5 * c ^ 4 + 2 * b₂ * c + b₁ = 0) :
    (c + x) ^ 5 + b₂ * (c + x) ^ 2 + b₁ * (c + x)
        - (c ^ 5 + b₂ * c ^ 2 + b₁ * c) =
      x ^ 2 * (x ^ 3 + 5 * c * x ^ 2 + 10 * c ^ 2 * x + 10 * c ^ 3 + b₂) := by
  linear_combination x * hc

/-- After scaling a nonzero critical hub to one, the entire value-ray shape
depends on the single complex parameter `μ = b₂/c³`. -/
theorem quintic_universal_shape_identity
    (c μ x : ℂ) :
    let b₂ := μ * c ^ 3
    let b₁ := -(5 + 2 * μ) * c ^ 4
    (c * (1 + x)) ^ 5 + b₂ * (c * (1 + x)) ^ 2 + b₁ * (c * (1 + x))
        - (c ^ 5 + b₂ * c ^ 2 + b₁ * c) =
      c ^ 5 * x ^ 2 * (x ^ 3 + 5 * x ^ 2 + 10 * x + 10 + μ) := by
  dsimp
  ring

/-- The derivative factors into the selected critical point and a universal
cubic locating the other three critical points. -/
theorem quintic_universal_derivative_identity
    (c μ x : ℂ) :
    let b₂ := μ * c ^ 3
    let b₁ := -(5 + 2 * μ) * c ^ 4
    5 * (c * (1 + x)) ^ 4 + 2 * b₂ * (c * (1 + x)) + b₁ =
      c ^ 4 * x * (5 * x ^ 3 + 20 * x ^ 2 + 30 * x + 20 + 2 * μ) := by
  dsimp
  ring

/-- On the other-critical cubic, the selected-to-other critical-value gap
loses `μ` and becomes a fixed quintic polynomial of the displacement. -/
theorem quintic_universal_critical_gap
    (μ x : ℂ)
    (hx : 5 * x ^ 3 + 20 * x ^ 2 + 30 * x + 20 + 2 * μ = 0) :
    -(x ^ 2 * (x ^ 3 + 5 * x ^ 2 + 10 * x + 10 + μ)) =
      (1 / 2 : ℂ) * x ^ 3 * (3 * x ^ 2 + 10 * x + 10) := by
  linear_combination -(x ^ 2 / 2) * hx

/-- The exact rational inequalities used by the explicit Rouché outer bound. -/
theorem quintic_universal_chamber_rational_budget :
    (52997 : ℚ) / 337500 < 5043 / 31250 ∧
      (4074569711 : ℚ) / 8437500000 < 1 / 2 := by
  norm_num

end ErdosProblems.Erdos1041
