import Mathlib.Tactic

/-!
# Erdős #1041: the sharp quintic mixed-mode transition

The mixed model `Re(Az + Bz² - z⁵)` has a sharp equality chart.  At its two
simultaneous-zero directions the paired third Fourier mode has opposite signs.
This module kernel-checks that trigonometric tie-breaking mechanism, the exact
algebraic transition amplitude, and the quantitative lexicographic stability
lemma used by the accompanying analytic note.
-/

namespace ErdosProblems.Erdos1041.QuinticMixedTransitionResolution

/-- Exact Fourier pairing for a tangent perturbation: conjugating a purely
imaginary coefficient changes its sign.  Taking `ξ_k = ω^{-km}` identifies the
left side with the complementary mode `E_{n-m}`. -/
theorem tangentFourier_pair {ι : Type*} (s : Finset ι) (y : ι → ℝ) (ξ : ι → ℂ) :
    (∑ k ∈ s, Complex.I * (y k : ℂ) * (starRingEnd ℂ) (ξ k)) =
      -(starRingEnd ℂ) (∑ k ∈ s, Complex.I * (y k : ℂ) * ξ k) := by
  rw [map_sum]
  simp [map_mul, Finset.sum_neg_distrib]

/-- The sharp mixed leading model in polar coordinates for coefficient phases
`arg A = 2π/5` and `arg B = 13π/10`. -/
noncomputable def mixedLeadingValue (ρ u α : ℝ) : ℝ :=
  ρ * u * Real.cos (2 * Real.pi / 5 + α) +
    ρ ^ 2 * Real.cos (13 * Real.pi / 10 + 2 * α) -
      ρ ^ 5 * Real.cos (5 * α)

/-- The tangent Fourier-pairing correction `E₃ = -conj(E₂)` has coefficient
phase `17π/10`. -/
noncomputable def pairedThirdCorrection (ρ α : ℝ) : ℝ :=
  ρ ^ 3 * Real.cos (17 * Real.pi / 10 + 3 * α)

private theorem cos_three_pi_div_two : Real.cos (3 * Real.pi / 2) = 0 := by
  rw [show 3 * Real.pi / 2 = Real.pi + Real.pi / 2 by ring]
  rw [Real.cos_add, Real.cos_pi, Real.cos_pi_div_two, Real.sin_pi,
    Real.sin_pi_div_two]
  norm_num

private theorem cos_neg_nine_pi_div_two : Real.cos (-9 * Real.pi / 2) = 0 := by
  have h := Real.cos_add_int_mul_two_pi (-Real.pi / 2) (-2)
  rw [show -Real.pi / 2 + (-2 : ℤ) * (2 * Real.pi) = -9 * Real.pi / 2 by
    push_cast
    ring] at h
  calc
    Real.cos (-9 * Real.pi / 2) = Real.cos (-Real.pi / 2) := h
    _ = Real.cos (-(Real.pi / 2)) := by congr 2 <;> ring
    _ = Real.cos (Real.pi / 2) := Real.cos_neg (Real.pi / 2)
    _ = 0 := Real.cos_pi_div_two

private theorem cos_neg_pi_div_two : Real.cos (-Real.pi / 2) = 0 := by
  calc
    Real.cos (-Real.pi / 2) = Real.cos (-(Real.pi / 2)) := by congr 2 <;> ring
    _ = Real.cos (Real.pi / 2) := Real.cos_neg (Real.pi / 2)
    _ = 0 := Real.cos_pi_div_two

/-- At the first exceptional direction every term of the leading model is
purely imaginary, so its real part vanishes for every radius and amplitude. -/
theorem mixedLeadingValue_at_positive_zero (ρ u : ℝ) :
    mixedLeadingValue ρ u (Real.pi / 10) = 0 := by
  unfold mixedLeadingValue
  rw [show 2 * Real.pi / 5 + Real.pi / 10 = Real.pi / 2 by ring]
  rw [show 13 * Real.pi / 10 + 2 * (Real.pi / 10) = 3 * Real.pi / 2 by ring]
  rw [show 5 * (Real.pi / 10) = Real.pi / 2 by ring]
  rw [Real.cos_pi_div_two, cos_three_pi_div_two]
  ring

/-- The antipodal exceptional direction is also an exact leading-order zero. -/
theorem mixedLeadingValue_at_negative_zero (ρ u : ℝ) :
    mixedLeadingValue ρ u (-9 * Real.pi / 10) = 0 := by
  unfold mixedLeadingValue
  rw [show 2 * Real.pi / 5 + (-9 * Real.pi / 10) = -Real.pi / 2 by ring]
  rw [show 13 * Real.pi / 10 + 2 * (-9 * Real.pi / 10) = -Real.pi / 2 by ring]
  rw [show 5 * (-9 * Real.pi / 10) = -9 * Real.pi / 2 by ring]
  rw [cos_neg_pi_div_two, cos_neg_nine_pi_div_two]
  ring

/-- The paired third mode is positive at the first leading-order zero. -/
theorem pairedThirdCorrection_at_positive_zero (ρ : ℝ) :
    pairedThirdCorrection ρ (Real.pi / 10) = ρ ^ 3 := by
  unfold pairedThirdCorrection
  rw [show 17 * Real.pi / 10 + 3 * (Real.pi / 10) = 2 * Real.pi by ring]
  rw [Real.cos_two_pi]
  ring

/-- The paired third mode is negative at the antipodal leading-order zero.
This is the decisive lexicographic tie-break. -/
theorem pairedThirdCorrection_at_negative_zero (ρ : ℝ) :
    pairedThirdCorrection ρ (-9 * Real.pi / 10) = -(ρ ^ 3) := by
  unfold pairedThirdCorrection
  rw [show 17 * Real.pi / 10 + 3 * (-9 * Real.pi / 10) = -Real.pi by ring]
  rw [Real.cos_neg, Real.cos_pi]
  ring

/-- The exact transition amplitude is the unique positive root of
`u³ = 27/320`; in particular it lies in the compact interval `(2/5,1/2)`. -/
theorem transitionAmplitude_bounds {u : ℝ} (hu0 : 0 ≤ u)
    (hu : u ^ 3 = (27 : ℝ) / 320) :
    (2 : ℝ) / 5 < u ∧ u < (1 : ℝ) / 2 := by
  have hlow : 0 < u ^ 3 - ((2 : ℝ) / 5) ^ 3 := by rw [hu]; norm_num
  have hhigh : 0 < ((1 : ℝ) / 2) ^ 3 - u ^ 3 := by rw [hu]; norm_num
  have hqLow : 0 < u ^ 2 + ((2 : ℝ) / 5) * u + ((2 : ℝ) / 5) ^ 2 := by
    nlinarith [sq_nonneg (u + (1 : ℝ) / 5)]
  have hqHigh : 0 < u ^ 2 + ((1 : ℝ) / 2) * u + ((1 : ℝ) / 2) ^ 2 := by
    nlinarith [sq_nonneg (u + (1 : ℝ) / 4)]
  constructor
  · have hfac : u ^ 3 - ((2 : ℝ) / 5) ^ 3 =
        (u - (2 : ℝ) / 5) *
          (u ^ 2 + ((2 : ℝ) / 5) * u + ((2 : ℝ) / 5) ^ 2) := by ring
    rw [hfac] at hlow
    exact sub_pos.mp (pos_of_mul_pos_left hlow hqLow.le)
  · have hfac : ((1 : ℝ) / 2) ^ 3 - u ^ 3 =
        ((1 : ℝ) / 2 - u) *
          (((1 : ℝ) / 2) ^ 2 + ((1 : ℝ) / 2) * u + u ^ 2) := by ring
    rw [hfac] at hhigh
    have hq : 0 < ((1 : ℝ) / 2) ^ 2 + ((1 : ℝ) / 2) * u + u ^ 2 := by
      nlinarith
    exact sub_pos.mp (pos_of_mul_pos_left hhigh hq.le)

/-- A nonpositive leading model plus the negative paired correction stays
strictly negative when the remaining error spends at most half the correction
margin. -/
theorem pairedCorrection_resolves_tie {L ε ρ R : ℝ}
    (hL : L ≤ 0) (hε : 0 < ε) (hρ : 0 < ρ)
    (hR : |R| ≤ ε * ρ ^ 3 / 2) :
    L + ε * (-(ρ ^ 3)) + R < 0 := by
  have hρ3 : 0 < ρ ^ 3 := pow_pos hρ 3
  have hRup : R ≤ ε * ρ ^ 3 / 2 := (abs_le.mp hR).2
  nlinarith [mul_pos hε hρ3]

end ErdosProblems.Erdos1041.QuinticMixedTransitionResolution
