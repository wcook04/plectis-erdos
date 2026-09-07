import Mathlib.Tactic

/-!
# Erdős #1041: a tied Newton face with no safe model spoke

For the quintic homogeneous model

`H(z) = Re (z + 10 z^2 - z^5)`,

the five fifth-root rays have only three scalar restrictions, by conjugate
symmetry.  This module checks an explicit positive witness on every type and
therefore rules out a proof of tied-face closure by selecting even one complete
safe model spoke.

The complex root-of-unity reduction is written out in the companion note.  The
Lean theorem is the exact radical-inequality kernel it consumes.  It does not
refute truncated connectors, Form A-cut, or Erdős #1041.
-/

namespace ErdosProblems.Erdos1041.TiedNewtonFaceTwoSpokeNoGo

noncomputable def sqrtFive : ℝ := Real.sqrt 5

noncomputable def rayZero (t : ℝ) : ℝ := t + 10 * t ^ 2 - t ^ 5

noncomputable def rayOne (t : ℝ) : ℝ :=
  ((sqrtFive - 1) / 4) * t - 10 * ((sqrtFive + 1) / 4) * t ^ 2 - t ^ 5

noncomputable def rayTwo (t : ℝ) : ℝ :=
  -((sqrtFive + 1) / 4) * t + 10 * ((sqrtFive - 1) / 4) * t ^ 2 - t ^ 5

theorem sqrtFive_gt_eleven_fifths : (11 / 5 : ℝ) < sqrtFive := by
  have hs : sqrtFive ^ 2 = 5 := by
    rw [sqrtFive, Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 5)]
  have hnonneg : 0 ≤ sqrtFive := by exact Real.sqrt_nonneg 5
  nlinarith

theorem sqrtFive_lt_three : sqrtFive < 3 := by
  have hs : sqrtFive ^ 2 = 5 := by
    rw [sqrtFive, Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 5)]
  have hnonneg : 0 ≤ sqrtFive := by exact Real.sqrt_nonneg 5
  nlinarith

/-- The positive real fifth-root direction escapes immediately. -/
theorem rayZero_witness :
    0 < (1 / 10 : ℝ) ∧ (1 / 10 : ℝ) < 1 ∧ 0 < rayZero (1 / 10) := by
  norm_num [rayZero]

/-- The two directions with angles `2π/5` and `8π/5` escape at `t=1/1000`. -/
theorem rayOne_witness :
    0 < (1 / 1000 : ℝ) ∧ (1 / 1000 : ℝ) < 1 ∧
      0 < rayOne (1 / 1000) := by
  constructor
  · norm_num
  constructor
  · norm_num
  · have hlo := sqrtFive_gt_eleven_fifths
    have hhi := sqrtFive_lt_three
    dsimp [rayOne]
    norm_num at ⊢
    nlinarith

/-- The two directions with angles `4π/5` and `6π/5` have a later positive
bump, witnessed at `t=3/10`. -/
theorem rayTwo_witness :
    0 < (3 / 10 : ℝ) ∧ (3 / 10 : ℝ) < 1 ∧
      0 < rayTwo (3 / 10) := by
  constructor
  · norm_num
  constructor
  · norm_num
  · have hlo := sqrtFive_gt_eleven_fifths
    dsimp [rayTwo]
    norm_num at ⊢
    nlinarith

/-- The exact scalar restriction of the model to the five root directions. -/
noncomputable def modelRayValue (j : Fin 5) (t : ℝ) : ℝ :=
  if j = 0 then rayZero t else if j = 1 ∨ j = 4 then rayOne t else rayTwo t

/-- Every fifth-root ray has a point in the open positive set of the model. -/
theorem every_model_ray_has_positive_point (j : Fin 5) :
    ∃ t : ℝ, 0 < t ∧ t < 1 ∧ 0 < modelRayValue j t := by
  fin_cases j
  · exact ⟨1 / 10, by simpa [modelRayValue] using rayZero_witness⟩
  · exact ⟨1 / 1000, by simpa [modelRayValue] using rayOne_witness⟩
  · exact ⟨3 / 10, by simpa [modelRayValue] using rayTwo_witness⟩
  · exact ⟨3 / 10, by simpa [modelRayValue] using rayTwo_witness⟩
  · exact ⟨1 / 1000, by simpa [modelRayValue] using rayOne_witness⟩

/-- Consequently there is no fifth-root direction on which the tied-face model
is nonpositive throughout the whole unit radial interval. -/
theorem no_complete_safe_model_ray :
    ¬ ∃ j : Fin 5, ∀ t : ℝ, 0 ≤ t → t ≤ 1 → modelRayValue j t ≤ 0 := by
  rintro ⟨j, hj⟩
  obtain ⟨t, ht0, ht1, hpos⟩ := every_model_ray_has_positive_point j
  have := hj t ht0.le ht1.le
  linarith

/-! ## The exact connector rescue -/

/-- Scalar restriction of `H` to the chord joining `2*omega` to `2*omega^2`,
with affine parameter `u`.  The companion note derives this polynomial from
the fifth-root identities. -/
noncomputable def chordAtTwo (u : ℝ) : ℝ :=
  (-200 + 200 * sqrtFive) * u ^ 4 +
  (400 - 400 * sqrtFive) * u ^ 3 +
  (-400 + 260 * sqrtFive) * u ^ 2 +
  (200 - 41 * sqrtFive) * u -
  85 / 2 - 19 * sqrtFive / 2

/-- A quartic written in Bernstein form is nonpositive when all five
coefficients are nonpositive. -/
theorem bernsteinQuartic_nonpos
    {v b₀ b₁ b₂ b₃ b₄ : ℝ}
    (hv0 : 0 ≤ v) (hv1 : v ≤ 1)
    (hb₀ : b₀ ≤ 0) (hb₁ : b₁ ≤ 0) (hb₂ : b₂ ≤ 0)
    (hb₃ : b₃ ≤ 0) (hb₄ : b₄ ≤ 0) :
    b₀ * (1 - v) ^ 4 +
      4 * b₁ * v * (1 - v) ^ 3 +
      6 * b₂ * v ^ 2 * (1 - v) ^ 2 +
      4 * b₃ * v ^ 3 * (1 - v) + b₄ * v ^ 4 ≤ 0 := by
  have hnv : 0 ≤ 1 - v := by linarith
  have hB₀ : 0 ≤ (1 - v) ^ 4 := by positivity
  have hB₁ : 0 ≤ v * (1 - v) ^ 3 := by positivity
  have hB₂ : 0 ≤ v ^ 2 * (1 - v) ^ 2 := by positivity
  have hB₃ : 0 ≤ v ^ 3 * (1 - v) := by positivity
  have hB₄ : 0 ≤ v ^ 4 := by positivity
  have h₀ := mul_nonpos_of_nonpos_of_nonneg hb₀ hB₀
  have h₁ := mul_nonpos_of_nonpos_of_nonneg hb₁ hB₁
  have h₂ := mul_nonpos_of_nonpos_of_nonneg hb₂ hB₂
  have h₃ := mul_nonpos_of_nonpos_of_nonneg hb₃ hB₃
  have h₄ := mul_nonpos_of_nonpos_of_nonneg hb₄ hB₄
  nlinarith

/-- The adjacent connector has a large uniform strict margin.  Splitting the
parameter interval at one half makes every quartic Bernstein coefficient at
most zero after adding five. -/
theorem chordAtTwo_le_neg_five {u : ℝ} (hu0 : 0 ≤ u) (hu1 : u ≤ 1) :
    chordAtTwo u ≤ -5 := by
  have hs0 : 0 ≤ sqrtFive := Real.sqrt_nonneg 5
  have hs3 := sqrtFive_lt_three
  by_cases hleft : u ≤ 1 / 2
  · let v := 2 * u
    have hv0 : 0 ≤ v := by dsimp [v]; linarith
    have hv1 : v ≤ 1 := by dsimp [v]; linarith
    have hbern := bernsteinQuartic_nonpos (v := v)
      (b₀ := -75 / 2 - 19 * sqrtFive / 2)
      (b₁ := -25 / 2 - 117 * sqrtFive / 8)
      (b₂ := -25 / 6 - 107 * sqrtFive / 12)
      (b₃ := -39 * sqrtFive / 8)
      (b₄ := -5 * sqrtFive / 2)
      hv0 hv1 (by nlinarith) (by nlinarith) (by nlinarith)
      (by nlinarith) (by nlinarith)
    have hid :
        chordAtTwo u + 5 =
          (-75 / 2 - 19 * sqrtFive / 2) * (1 - v) ^ 4 +
          4 * (-25 / 2 - 117 * sqrtFive / 8) * v * (1 - v) ^ 3 +
          6 * (-25 / 6 - 107 * sqrtFive / 12) * v ^ 2 * (1 - v) ^ 2 +
          4 * (-39 * sqrtFive / 8) * v ^ 3 * (1 - v) +
          (-5 * sqrtFive / 2) * v ^ 4 := by
      dsimp [chordAtTwo, v]
      ring
    linarith [hid, hbern]
  · let v := 2 * u - 1
    have hv0 : 0 ≤ v := by dsimp [v]; linarith
    have hv1 : v ≤ 1 := by dsimp [v]; linarith
    have hb₂ : -25 / 6 + 7 * sqrtFive / 12 ≤ 0 := by nlinarith
    have hb₄ : -75 / 2 + 19 * sqrtFive / 2 ≤ 0 := by nlinarith
    have hbern := bernsteinQuartic_nonpos (v := v)
      (b₀ := -5 * sqrtFive / 2)
      (b₁ := -sqrtFive / 8)
      (b₂ := -25 / 6 + 7 * sqrtFive / 12)
      (b₃ := -25 / 2 - 3 * sqrtFive / 8)
      (b₄ := -75 / 2 + 19 * sqrtFive / 2)
      hv0 hv1 (by nlinarith) (by nlinarith) hb₂ (by nlinarith) hb₄
    have hid :
        chordAtTwo u + 5 =
          (-5 * sqrtFive / 2) * (1 - v) ^ 4 +
          4 * (-sqrtFive / 8) * v * (1 - v) ^ 3 +
          6 * (-25 / 6 + 7 * sqrtFive / 12) * v ^ 2 * (1 - v) ^ 2 +
          4 * (-25 / 2 - 3 * sqrtFive / 8) * v ^ 3 * (1 - v) +
          (-75 / 2 + 19 * sqrtFive / 2) * v ^ 4 := by
      dsimp [chordAtTwo, v]
      ring
    linarith [hid, hbern]

/-- After radius two, the first selected ray type stays strictly safe. -/
theorem rayOne_neg_of_two_le {t : ℝ} (ht : 2 ≤ t) : rayOne t < 0 := by
  have hslo := sqrtFive_gt_eleven_fifths
  have hshi := sqrtFive_lt_three
  have ht0 : 0 < t := by linarith
  have ht4 : 0 ≤ t ^ 4 := by positivity
  have hbracket :
      (sqrtFive - 1) / 4 - 10 * ((sqrtFive + 1) / 4) * t - t ^ 4 < 0 := by
    nlinarith
  rw [show rayOne t = t *
      ((sqrtFive - 1) / 4 - 10 * ((sqrtFive + 1) / 4) * t - t ^ 4) by
        dsimp [rayOne]; ring]
  exact mul_neg_of_pos_of_neg ht0 hbracket

/-- After radius two, the second selected ray type stays strictly safe. -/
theorem rayTwo_neg_of_two_le {t : ℝ} (ht : 2 ≤ t) : rayTwo t < 0 := by
  have hs0 : 0 ≤ sqrtFive := Real.sqrt_nonneg 5
  have hshi := sqrtFive_lt_three
  have ht0 : 0 < t := by linarith
  have hquad : 0 ≤ t ^ 2 + 2 * t + 4 := by nlinarith [sq_nonneg (t + 1)]
  have hfac : 0 ≤ (t - 2) * (t ^ 2 + 2 * t + 4) :=
    mul_nonneg (by linarith) hquad
  have ht3 : 8 ≤ t ^ 3 := by nlinarith [hfac]
  have ht3' : 5 ≤ t ^ 3 := ht3.trans' (by norm_num)
  have ht2 : 0 ≤ t ^ 2 := by positivity
  have hpow : 5 * t ^ 2 ≤ t ^ 5 := by
    have := mul_le_mul_of_nonneg_left ht3' ht2
    nlinarith
  have hbracket :
      -((sqrtFive + 1) / 4) + 10 * ((sqrtFive - 1) / 4) * t - t ^ 4 < 0 := by
    have hscaled : 10 * ((sqrtFive - 1) / 4) * t ^ 2 < 5 * t ^ 2 := by
      have hc : 10 * ((sqrtFive - 1) / 4) < 5 := by nlinarith
      exact mul_lt_mul_of_pos_right hc (by positivity)
    nlinarith
  rw [show rayTwo t = t *
      (-((sqrtFive + 1) / 4) + 10 * ((sqrtFive - 1) / 4) * t - t ^ 4) by
        dsimp [rayTwo]; ring]
  exact mul_neg_of_pos_of_neg ht0 hbracket

/-- The same face that defeats every complete spoke is rescued exactly by the
adjacent ray types `1,2` and their radius-two connector. -/
theorem exact_connector_rescues_tied_face :
    (∀ t : ℝ, 2 ≤ t → rayOne t < 0) ∧
    (∀ t : ℝ, 2 ≤ t → rayTwo t < 0) ∧
    (∀ u : ℝ, 0 ≤ u → u ≤ 1 → chordAtTwo u ≤ -5) := by
  exact ⟨fun _ ht ↦ rayOne_neg_of_two_le ht,
    fun _ ht ↦ rayTwo_neg_of_two_le ht,
    fun _ hu0 hu1 ↦ chordAtTwo_le_neg_five hu0 hu1⟩

end ErdosProblems.Erdos1041.TiedNewtonFaceTwoSpokeNoGo
