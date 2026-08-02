import Mathlib.Analysis.Real.Pi.Bounds

/-!
# Erdős #1049: a rectangular Hermite--Padé threshold comparison

The functions below encode the decay, height, and cyclotomic-saving exponents
of one rectangular two-function Hermite--Padé model.  In the admissible region
`rho ≥ 0` and `sigma ≥ 1 + rho`, its threshold never exceeds the classical
one-function margin `1 / 2 - 1 / π²`.  Equality occurs only at
`rho = 0`, `sigma = 1`; no upper bound on `rho` is needed.

This is a comparison theorem for the explicit exponent model defined here.
It constructs no approximating polynomials or remainders, does not show that
every rational-base method has this form, and does not decide the arithmetic
nature of the Lambert value at `3 / 2`.
-/

namespace ErdosProblems.Erdos1049

/-- Quadratic Archimedean decay expression in the rectangular exponent
model. -/
noncomputable def hpDecay (rho sigma : ℝ) : ℝ :=
  (1 + rho ^ 2) / 2 + sigma

/-- Homogeneous polynomial-width expression in the rectangular exponent
model. -/
noncomputable def hpHeight (rho sigma : ℝ) : ℝ :=
  (1 + rho) ^ 2 / 2 + sigma * (1 + rho)

/-- Cyclotomic denominator-saving expression in the rectangular exponent
model. -/
noncomputable def hpCyclotomicSaving (sigma : ℝ) : ℝ :=
  3 * sigma ^ 2 / Real.pi ^ 2

/-- Rational-base height threshold associated with the explicit exponent
model above. -/
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

/-- If `rho ≥ 0` and `sigma ≥ 1 + rho`, then the cleared threshold gap is
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

/-- In the explicit rectangular regime above, the two-function threshold is
never larger than the classical one-function threshold. -/
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

/-- Equality holds exactly at the classical endpoint
`rho = 0`, `sigma = 1`. -/
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
