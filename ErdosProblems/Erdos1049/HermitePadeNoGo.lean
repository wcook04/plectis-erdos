import Mathlib.Analysis.Real.Pi.Bounds

/-!
# Erdős #1049: rectangular Hermite--Padé threshold no-go

This module formalizes the exact optimisation returned in the research packet
for the standard rectangular two-function Hermite--Padé family.  Its decay,
height, and cyclotomic-saving exponents give a rational-base threshold which
never exceeds the classical one-function margin `1 / 2 - 1 / pi^2`.

The formal result is slightly stronger than the packet formulation: the upper
bound `rho <= 1` is unnecessary.  For every `rho >= 0` and
`sigma >= 1 + rho`, equality occurs only at the one-function endpoint
`rho = 0`, `sigma = 1`.
-/

namespace ErdosProblems.Erdos1049

/-- Quadratic Archimedean decay exponent of the rectangular family. -/
noncomputable def hpDecay (rho sigma : ℝ) : ℝ :=
  (1 + rho ^ 2) / 2 + sigma

/-- Homogeneous polynomial-width exponent of the rectangular family. -/
noncomputable def hpHeight (rho sigma : ℝ) : ℝ :=
  (1 + rho) ^ 2 / 2 + sigma * (1 + rho)

/-- Cyclotomic denominator saving in the rectangular family. -/
noncomputable def hpCyclotomicSaving (sigma : ℝ) : ℝ :=
  3 * sigma ^ 2 / Real.pi ^ 2

/-- Rational-base height threshold produced by the rectangular family. -/
noncomputable def hpThreshold (rho sigma : ℝ) : ℝ :=
  (hpDecay rho sigma - hpCyclotomicSaving sigma) /
    (hpHeight rho sigma + hpDecay rho sigma)

/-- The denominator-cleared difference between the rectangular threshold and
the classical one-function threshold. -/
noncomputable def hpClearedGap (rho sigma : ℝ) : ℝ :=
  (Real.pi ^ 2 + 2) * hpDecay rho sigma - 6 * sigma ^ 2 -
    (Real.pi ^ 2 - 2) * hpHeight rho sigma

/-- Exact polynomial identity after writing `sigma = 1 + rho + u`. -/
theorem hpClearedGap_expansion (rho u : ℝ) :
    hpClearedGap rho (1 + rho + u) =
      -Real.pi ^ 2 * rho ^ 2 - Real.pi ^ 2 * rho * u -
        2 * Real.pi ^ 2 * rho - 2 * rho ^ 2 - 10 * rho * u -
        4 * rho - 6 * u ^ 2 - 8 * u := by
  unfold hpClearedGap hpDecay hpHeight
  ring

/-- In the admissible rectangular regime, every term in the cleared gap is
nonpositive. -/
theorem hpClearedGap_nonpos (rho sigma : ℝ)
    (hrho : 0 ≤ rho) (hsigma : 1 + rho ≤ sigma) :
    hpClearedGap rho sigma ≤ 0 := by
  let u := sigma - 1 - rho
  have hu : 0 ≤ u := by
    dsimp [u]
    linarith
  have hsigmaEq : sigma = 1 + rho + u := by
    dsimp [u]
    ring
  rw [hsigmaEq, hpClearedGap_expansion]
  have hpiSq : 0 ≤ Real.pi ^ 2 := sq_nonneg _
  nlinarith [mul_nonneg hpiSq (sq_nonneg rho),
    mul_nonneg hpiSq (mul_nonneg hrho hu), mul_nonneg hpiSq hrho,
    sq_nonneg rho, mul_nonneg hrho hu, sq_nonneg u]

/-- The cleared gap vanishes only at the one-function endpoint. -/
theorem hpClearedGap_eq_zero_iff (rho sigma : ℝ)
    (hrho : 0 ≤ rho) (hsigma : 1 + rho ≤ sigma) :
    hpClearedGap rho sigma = 0 ↔ rho = 0 ∧ sigma = 1 := by
  let u := sigma - 1 - rho
  have hu : 0 ≤ u := by
    dsimp [u]
    linarith
  have hsigmaEq : sigma = 1 + rho + u := by
    dsimp [u]
    ring
  constructor
  · rw [hsigmaEq, hpClearedGap_expansion]
    intro h
    have hpiSq : 0 < Real.pi ^ 2 := sq_pos_of_pos Real.pi_pos
    have hpiRho : 0 ≤ Real.pi ^ 2 * rho := mul_nonneg hpiSq.le hrho
    have hrhoU : 0 ≤ rho * u := mul_nonneg hrho hu
    have huSq : 0 ≤ u ^ 2 := sq_nonneg u
    have hrhoSq : 0 ≤ rho ^ 2 := sq_nonneg rho
    constructor
    · nlinarith
    · dsimp [u] at *
      nlinarith
  · rintro ⟨rfl, rfl⟩
    unfold hpClearedGap hpDecay hpHeight
    ring

/-- The standard rectangular two-function Hermite--Padé threshold is never
better than the classical one-function threshold.  No hypothesis
`rho <= 1` is needed. -/
theorem rectangular_hp_threshold_le_classical (rho sigma : ℝ)
    (hrho : 0 ≤ rho) (hsigma : 1 + rho ≤ sigma) :
    hpThreshold rho sigma ≤ 1 / 2 - 1 / Real.pi ^ 2 := by
  have hpiSqPos : 0 < Real.pi ^ 2 := sq_pos_of_pos Real.pi_pos
  have hcPos : 0 < hpDecay rho sigma := by
    unfold hpDecay
    nlinarith [sq_nonneg rho]
  have hhNonneg : 0 ≤ hpHeight rho sigma := by
    unfold hpHeight
    nlinarith [sq_nonneg (1 + rho)]
  have hdenPos : 0 < hpHeight rho sigma + hpDecay rho sigma := by
    nlinarith
  have hgap := hpClearedGap_nonpos rho sigma hrho hsigma
  unfold hpThreshold
  apply (div_le_iff₀ hdenPos).2
  apply le_of_mul_le_mul_left (a := Real.pi ^ 2) (by
    unfold hpClearedGap hpDecay hpHeight at hgap
    unfold hpDecay hpHeight hpCyclotomicSaving
    field_simp
    nlinarith) hpiSqPos

/-- Equality in the threshold bound characterizes the classical endpoint. -/
theorem rectangular_hp_threshold_eq_classical_iff (rho sigma : ℝ)
    (hrho : 0 ≤ rho) (hsigma : 1 + rho ≤ sigma) :
    hpThreshold rho sigma = 1 / 2 - 1 / Real.pi ^ 2 ↔
      rho = 0 ∧ sigma = 1 := by
  have hpiSqPos : 0 < Real.pi ^ 2 := sq_pos_of_pos Real.pi_pos
  have hcPos : 0 < hpDecay rho sigma := by
    unfold hpDecay
    nlinarith [sq_nonneg rho]
  have hhNonneg : 0 ≤ hpHeight rho sigma := by
    unfold hpHeight
    nlinarith [sq_nonneg (1 + rho)]
  have hdenPos : 0 < hpHeight rho sigma + hpDecay rho sigma := by
    nlinarith
  constructor
  · intro heq
    unfold hpThreshold at heq
    have hscaled := (div_eq_iff hdenPos.ne').1 heq
    apply (hpClearedGap_eq_zero_iff rho sigma hrho hsigma).1
    unfold hpClearedGap hpDecay hpHeight
    unfold hpDecay hpHeight hpCyclotomicSaving at hscaled
    field_simp at hscaled ⊢
    nlinarith
  · rintro ⟨rfl, rfl⟩
    unfold hpThreshold hpDecay hpHeight hpCyclotomicSaving
    field_simp
    ring

end ErdosProblems.Erdos1049
