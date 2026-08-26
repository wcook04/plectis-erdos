import Mathlib.Tactic

/-!
# Erdős #1041: the all-phase quintic second-mode connector

This module kernel-checks the scalar certificate behind the all-phase path for
`H_A(z) = Re (A z^2 - z^5)`, `|A| = 1`.  A five-sector phase selection reduces
every coefficient phase to one fundamental sector.  On that sector a cosine
envelope reduces the chord to its two boundary phases, and the boundary chord
polynomial is certified negative by a degree-13 Bernstein expansion.
-/

namespace ErdosProblems.Erdos1041.QuinticSecondModeConnector

set_option maxHeartbeats 2000000

/-- The scalar value of `Re(z^2-z^5)` on a fifth-root ray with second-mode
projection `p`. -/
def secondModeRay (p t : ℝ) : ℝ := t ^ 2 * p - t ^ 5

/-- Every ray whose second-mode projection is strictly below one is strictly
safe from the balance radius one outwards. -/
theorem secondModeRay_strict {p t : ℝ} (hp : p < 1) (ht : 1 ≤ t) :
    secondModeRay p t < 0 := by
  have ht0 : 0 < t := lt_of_lt_of_le zero_lt_one ht
  have ht3 : 1 ≤ t ^ 3 := one_le_pow₀ ht
  have ht2 : 0 < t ^ 2 := pow_pos ht0 2
  have hpt : p < t ^ 3 := lt_of_lt_of_le hp ht3
  unfold secondModeRay
  calc
    t ^ 2 * p - t ^ 5 = t ^ 2 * (p - t ^ 3) := by ring
    _ < 0 := mul_neg_of_pos_of_neg ht2 (sub_neg.mpr hpt)

/-- The power-basis chord polynomial obtained from
`Re((((1-t)ω+tω²)^2)-(((1-t)ω+tω²)^5))`, where `ω=e^(2πi/5)` and
`s=sqrt 5`. -/
noncomputable def chordPolynomial (s t : ℝ) : ℝ :=
    (-25 / 4 + 25 * s / 4) *
      (t ^ 4 - 2 * t ^ 3 + (11 / 10 - 9 * s / 50) * t ^ 2 +
        s * t / 5 - 3 * s / 50 - 1 / 10)

/-- The exact degree-13 Bernstein certificate for the chord polynomial, modulo
the defining quadratic relation of `sqrt 5`. -/
theorem chordPolynomial_bernstein (s t : ℝ) (hs : s ^ 2 = 5) :
    chordPolynomial s t =
      ((-5 - s) / 4) * (1 - t) ^ 13 +
      ((-9 * s - 20) / 26) * (13 * t * (1 - t) ^ 12) +
      ((-53 * s - 70) / 156) * (78 * t ^ 2 * (1 - t) ^ 11) +
      ((-157 * s - 140) / 572) * (286 * t ^ 3 * (1 - t) ^ 10) +
      ((-53 * s - 35) / 286) * (715 * t ^ 4 * (1 - t) ^ 9) +
      ((-169 * s - 95) / 1716) * (1287 * t ^ 5 * (1 - t) ^ 8) +
      (3 * (-6 * s - 5) / 572) * (1716 * t ^ 6 * (1 - t) ^ 7) +
      ((-15 + 4 * s) / 572) * (1716 * t ^ 7 * (1 - t) ^ 6) +
      ((-95 + 29 * s) / 1716) * (1287 * t ^ 8 * (1 - t) ^ 5) +
      ((-35 + 2 * s) / 286) * (715 * t ^ 9 * (1 - t) ^ 4) +
      ((-140 - 3 * s) / 572) * (286 * t ^ 10 * (1 - t) ^ 3) +
      ((-70 + s) / 156) * (78 * t ^ 11 * (1 - t) ^ 2) +
      ((-10 + s) / 13) * (13 * t ^ 12 * (1 - t)) +
      ((-5 + s) / 4) * t ^ 13 := by
  unfold chordPolynomial
  ring_nf at hs ⊢
  linear_combination (-3 / 8 + 5 * t / 4 - 9 * t ^ 2 / 8) * hs

/-- The Bernstein basis of degree thirteen is a nonnegative partition of
unity on the unit interval. -/
theorem bernstein13_partition (t : ℝ) :
    (1 - t) ^ 13 + 13 * t * (1 - t) ^ 12 +
      78 * t ^ 2 * (1 - t) ^ 11 + 286 * t ^ 3 * (1 - t) ^ 10 +
      715 * t ^ 4 * (1 - t) ^ 9 + 1287 * t ^ 5 * (1 - t) ^ 8 +
      1716 * t ^ 6 * (1 - t) ^ 7 + 1716 * t ^ 7 * (1 - t) ^ 6 +
      1287 * t ^ 8 * (1 - t) ^ 5 + 715 * t ^ 9 * (1 - t) ^ 4 +
      286 * t ^ 10 * (1 - t) ^ 3 + 78 * t ^ 11 * (1 - t) ^ 2 +
      13 * t ^ 12 * (1 - t) + t ^ 13 = 1 := by
  ring

/-- The quintic boundary-phase connector has a uniform rational negative
margin on the complete closed chord parameter interval. -/
theorem chordPolynomial_sqrtFive_le {t : ℝ} (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    chordPolynomial (Real.sqrt 5) t ≤ -(1 : ℝ) / 1000 := by
  let s := Real.sqrt 5
  have hs0 : 0 ≤ s := Real.sqrt_nonneg 5
  have hs_sq : s ^ 2 = 5 := by
    dsimp [s]
    norm_num
  have hs2 : 2 < s := by nlinarith
  have hs3 : s < 3 := by nlinarith
  have hmt : 0 ≤ 1 - t := sub_nonneg.mpr ht1
  let a0 := (1 - t) ^ 13
  let a1 := 13 * t * (1 - t) ^ 12
  let a2 := 78 * t ^ 2 * (1 - t) ^ 11
  let a3 := 286 * t ^ 3 * (1 - t) ^ 10
  let a4 := 715 * t ^ 4 * (1 - t) ^ 9
  let a5 := 1287 * t ^ 5 * (1 - t) ^ 8
  let a6 := 1716 * t ^ 6 * (1 - t) ^ 7
  let a7 := 1716 * t ^ 7 * (1 - t) ^ 6
  let a8 := 1287 * t ^ 8 * (1 - t) ^ 5
  let a9 := 715 * t ^ 9 * (1 - t) ^ 4
  let a10 := 286 * t ^ 10 * (1 - t) ^ 3
  let a11 := 78 * t ^ 11 * (1 - t) ^ 2
  let a12 := 13 * t ^ 12 * (1 - t)
  let a13 := t ^ 13
  have ha0 : 0 ≤ a0 := by dsimp [a0]; positivity
  have ha1 : 0 ≤ a1 := by dsimp [a1]; positivity
  have ha2 : 0 ≤ a2 := by dsimp [a2]; positivity
  have ha3 : 0 ≤ a3 := by dsimp [a3]; positivity
  have ha4 : 0 ≤ a4 := by dsimp [a4]; positivity
  have ha5 : 0 ≤ a5 := by dsimp [a5]; positivity
  have ha6 : 0 ≤ a6 := by dsimp [a6]; positivity
  have ha7 : 0 ≤ a7 := by dsimp [a7]; positivity
  have ha8 : 0 ≤ a8 := by dsimp [a8]; positivity
  have ha9 : 0 ≤ a9 := by dsimp [a9]; positivity
  have ha10 : 0 ≤ a10 := by dsimp [a10]; positivity
  have ha11 : 0 ≤ a11 := by dsimp [a11]; positivity
  have ha12 : 0 ≤ a12 := by dsimp [a12]; positivity
  have ha13 : 0 ≤ a13 := by dsimp [a13]; positivity
  have hsum : a0 + a1 + a2 + a3 + a4 + a5 + a6 + a7 + a8 + a9 +
      a10 + a11 + a12 + a13 = 1 := by
    dsimp [a0, a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11, a12, a13]
    exact bernstein13_partition t
  have hb0 : (-5 - s) / 4 ≤ -(1 : ℝ) / 1000 := by linarith
  have hb1 : (-9 * s - 20) / 26 ≤ -(1 : ℝ) / 1000 := by linarith
  have hb2 : (-53 * s - 70) / 156 ≤ -(1 : ℝ) / 1000 := by linarith
  have hb3 : (-157 * s - 140) / 572 ≤ -(1 : ℝ) / 1000 := by linarith
  have hb4 : (-53 * s - 35) / 286 ≤ -(1 : ℝ) / 1000 := by linarith
  have hb5 : (-169 * s - 95) / 1716 ≤ -(1 : ℝ) / 1000 := by linarith
  have hb6 : 3 * (-6 * s - 5) / 572 ≤ -(1 : ℝ) / 1000 := by linarith
  have hb7 : (-15 + 4 * s) / 572 ≤ -(1 : ℝ) / 1000 := by linarith
  have hb8 : (-95 + 29 * s) / 1716 ≤ -(1 : ℝ) / 1000 := by linarith
  have hb9 : (-35 + 2 * s) / 286 ≤ -(1 : ℝ) / 1000 := by linarith
  have hb10 : (-140 - 3 * s) / 572 ≤ -(1 : ℝ) / 1000 := by linarith
  have hb11 : (-70 + s) / 156 ≤ -(1 : ℝ) / 1000 := by linarith
  have hb12 : (-10 + s) / 13 ≤ -(1 : ℝ) / 1000 := by linarith
  have hb13 : (-5 + s) / 4 ≤ -(1 : ℝ) / 1000 := by linarith
  have hrepr : chordPolynomial s t =
      ((-5 - s) / 4) * a0 + ((-9 * s - 20) / 26) * a1 +
      ((-53 * s - 70) / 156) * a2 + ((-157 * s - 140) / 572) * a3 +
      ((-53 * s - 35) / 286) * a4 + ((-169 * s - 95) / 1716) * a5 +
      (3 * (-6 * s - 5) / 572) * a6 + ((-15 + 4 * s) / 572) * a7 +
      ((-95 + 29 * s) / 1716) * a8 + ((-35 + 2 * s) / 286) * a9 +
      ((-140 - 3 * s) / 572) * a10 + ((-70 + s) / 156) * a11 +
      ((-10 + s) / 13) * a12 + ((-5 + s) / 4) * a13 := by
    dsimp [a0, a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11, a12, a13]
    exact chordPolynomial_bernstein s t hs_sq
  have h0 := mul_le_mul_of_nonneg_right hb0 ha0
  have h1 := mul_le_mul_of_nonneg_right hb1 ha1
  have h2 := mul_le_mul_of_nonneg_right hb2 ha2
  have h3 := mul_le_mul_of_nonneg_right hb3 ha3
  have h4 := mul_le_mul_of_nonneg_right hb4 ha4
  have h5 := mul_le_mul_of_nonneg_right hb5 ha5
  have h6 := mul_le_mul_of_nonneg_right hb6 ha6
  have h7 := mul_le_mul_of_nonneg_right hb7 ha7
  have h8 := mul_le_mul_of_nonneg_right hb8 ha8
  have h9 := mul_le_mul_of_nonneg_right hb9 ha9
  have h10 := mul_le_mul_of_nonneg_right hb10 ha10
  have h11 := mul_le_mul_of_nonneg_right hb11 ha11
  have h12 := mul_le_mul_of_nonneg_right hb12 ha12
  have h13 := mul_le_mul_of_nonneg_right hb13 ha13
  rw [hrepr]
  nlinarith

/-- Strict form of the uniform boundary-phase chord certificate. -/
theorem chordPolynomial_sqrtFive_strict {t : ℝ} (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    chordPolynomial (Real.sqrt 5) t < 0 :=
  (chordPolynomial_sqrtFive_le ht0 ht1).trans_lt (by norm_num)

/-- The reflected boundary phase has the same uniform certificate. -/
theorem chordPolynomial_sqrtFive_reflected_le {t : ℝ} (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    chordPolynomial (Real.sqrt 5) (1 - t) ≤ -(1 : ℝ) / 1000 :=
  chordPolynomial_sqrtFive_le (sub_nonneg.mpr ht1) (by linarith)

/-- Polar-coordinate scalar form of `Re (exp(iθ) z² - z⁵)` for
`z = ρ exp(iα)`. -/
noncomputable def phaseModel (ρ α θ : ℝ) : ℝ :=
  ρ ^ 2 * Real.cos (θ + 2 * α) - ρ ^ 5 * Real.cos (5 * α)

/-- On the first half of the fundamental fifth-root chord sector, the largest
second-mode phase contribution occurs at the left endpoint `2π/5`. -/
theorem phaseModel_le_leftEndpoint {ρ α θ : ℝ}
    (hα0 : 0 ≤ α) (hα1 : α ≤ Real.pi / 5)
    (hθ0 : 2 * Real.pi / 5 ≤ θ) (hθ1 : θ ≤ 4 * Real.pi / 5) :
    phaseModel ρ α θ ≤ phaseModel ρ α (2 * Real.pi / 5) := by
  let x := θ + 2 * α
  let y := 2 * Real.pi / 5 + 2 * α
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
  have hρ2 : 0 ≤ ρ ^ 2 := sq_nonneg ρ
  exact sub_le_sub_right (mul_le_mul_of_nonneg_left hcos hρ2) _

/-- On the second half of the fundamental fifth-root chord sector, the largest
second-mode phase contribution occurs at the right endpoint `4π/5`. -/
theorem phaseModel_le_rightEndpoint {ρ α θ : ℝ}
    (hα0 : Real.pi / 5 ≤ α) (hα1 : α ≤ 2 * Real.pi / 5)
    (hθ0 : 2 * Real.pi / 5 ≤ θ) (hθ1 : θ ≤ 4 * Real.pi / 5) :
    phaseModel ρ α θ ≤ phaseModel ρ α (4 * Real.pi / 5) := by
  let x := θ + 2 * α
  let y := 4 * Real.pi / 5 + 2 * α
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
  have hρ2 : 0 ≤ ρ ^ 2 := sq_nonneg ρ
  exact sub_le_sub_right (mul_le_mul_of_nonneg_left hcos hρ2) _

/-- Five translates of the fundamental phase interval `[2π/5,4π/5]` cover
one complete phase period.  The five alternatives correspond to rotating the
chosen adjacent root pair. -/
theorem fivePhaseSector_cover {φ : ℝ} (hφ0 : 0 ≤ φ) (hφ1 : φ ≤ 2 * Real.pi) :
    (2 * Real.pi / 5 ≤ φ + 2 * Real.pi / 5 ∧
      φ + 2 * Real.pi / 5 ≤ 4 * Real.pi / 5) ∨
    (2 * Real.pi / 5 ≤ φ ∧ φ ≤ 4 * Real.pi / 5) ∨
    (2 * Real.pi / 5 ≤ φ - 2 * Real.pi / 5 ∧
      φ - 2 * Real.pi / 5 ≤ 4 * Real.pi / 5) ∨
    (2 * Real.pi / 5 ≤ φ - 4 * Real.pi / 5 ∧
      φ - 4 * Real.pi / 5 ≤ 4 * Real.pi / 5) ∨
    (2 * Real.pi / 5 ≤ φ - 6 * Real.pi / 5 ∧
      φ - 6 * Real.pi / 5 ≤ 4 * Real.pi / 5) := by
  by_cases h0 : φ ≤ 2 * Real.pi / 5
  · exact Or.inl ⟨by linarith, by linarith⟩
  by_cases h1 : φ ≤ 4 * Real.pi / 5
  · exact Or.inr (Or.inl ⟨by linarith, h1⟩)
  by_cases h2 : φ ≤ 6 * Real.pi / 5
  · exact Or.inr (Or.inr (Or.inl ⟨by linarith, by linarith⟩))
  by_cases h3 : φ ≤ 8 * Real.pi / 5
  · exact Or.inr (Or.inr (Or.inr (Or.inl ⟨by linarith, by linarith⟩)))
  · exact Or.inr (Or.inr (Or.inr (Or.inr ⟨by linarith, by linarith⟩)))

end ErdosProblems.Erdos1041.QuinticSecondModeConnector
