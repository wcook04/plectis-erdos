import Mathlib

/-!
# Erdős #1041: the decoupled chord-covering criterion for the paired sextic model

For the paired homogeneous sextic tangent model

  `H_{A,B,C}(z) = Re (A z + B z^2 + i C z^3 - conj B z^4 - conj A z^5 - z^6)`

every adjacent unit sixth-root chord carries an exact normal form

  `64 H = -64 + (1 - x^2) N(x)`,

with `N` an explicit quartic in the chord coordinate.  Three things are
formalised here.

* The normal form itself, through explicit powers of the half-chord point.
* Every sixth-root direction has `H = -1`, independently of `A`, `B`, `C`:
  the paired model pins all six root directions at the same depth, so the
  endpoints never bind and chord safety is an interior question.
* The scalar gap polynomial `chordGap` left after the extremal second-mode
  phase estimate and the rational majorant `sqrt (t^4+17t^2+841) ≤ 29 + 5t^2/16`
  is bounded below by `1/4` on `[0,1]`, by a six-piece dyadic Bernstein
  certificate.  This is the certificate behind the band `|A| ≤ |B|`, with
  uniform chord margin `1/256`.

`chordGap` is stated at first-mode modulus equal to second-mode modulus, so it
strictly contains the supplied `|A| ≤ (3/4)|B|` branch.
-/

namespace ErdosProblems.Erdos1041.SexticChordCoveringCriterion

noncomputable section

open Complex

lemma sqrt_three_sq : Real.sqrt 3 ^ 2 = 3 := Real.sq_sqrt (by norm_num)

/-- Half-chord coordinate: the adjacent chord between two consecutive sixth
roots of unity, before rotation.  The endpoints `x = ±1` are unit vectors. -/
def chordBase (x : ℝ) : ℂ := ⟨Real.sqrt 3 / 2, x / 2⟩

@[simp] lemma chordBase_re (x : ℝ) : (chordBase x).re = Real.sqrt 3 / 2 := rfl
@[simp] lemma chordBase_im (x : ℝ) : (chordBase x).im = x / 2 := rfl

lemma chordBase_pow_two (x : ℝ) :
    chordBase x ^ 2 = ⟨(3 - x ^ 2) / 4, Real.sqrt 3 * x / 2⟩ := by
  have h := sqrt_three_sq
  refine Complex.ext ?_ ?_
  · simp only [pow_two, Complex.mul_re, chordBase_re, chordBase_im]
    linear_combination h / 4
  · simp only [pow_two, Complex.mul_im, chordBase_re, chordBase_im]
    ring

lemma chordBase_pow_three (x : ℝ) :
    chordBase x ^ 3 = ⟨3 * Real.sqrt 3 * (1 - x ^ 2) / 8, x * (9 - x ^ 2) / 8⟩ := by
  have h := sqrt_three_sq
  have h2 := chordBase_pow_two x
  refine Complex.ext ?_ ?_
  · rw [pow_succ, h2]
    simp only [Complex.mul_re, chordBase_re, chordBase_im]
    ring
  · rw [pow_succ, h2]
    simp only [Complex.mul_im, chordBase_re, chordBase_im]
    linear_combination x / 4 * h

lemma chordBase_pow_four (x : ℝ) :
    chordBase x ^ 4 = ⟨(x ^ 4 - 18 * x ^ 2 + 9) / 16, Real.sqrt 3 * x * (3 - x ^ 2) / 4⟩ := by
  have h := sqrt_three_sq
  have h2 := chordBase_pow_two x
  refine Complex.ext ?_ ?_
  · rw [show (4 : ℕ) = 2 + 2 from rfl, pow_add, h2]
    simp only [Complex.mul_re]
    linear_combination (-(x ^ 2 / 4)) * h
  · rw [show (4 : ℕ) = 2 + 2 from rfl, pow_add, h2]
    simp only [Complex.mul_im]
    ring

lemma chordBase_pow_five (x : ℝ) :
    chordBase x ^ 5 =
      ⟨Real.sqrt 3 * (5 * x ^ 4 - 30 * x ^ 2 + 9) / 32, x * (x ^ 4 - 30 * x ^ 2 + 45) / 32⟩ := by
  have h := sqrt_three_sq
  have h4 := chordBase_pow_four x
  refine Complex.ext ?_ ?_
  · rw [pow_succ, h4]
    simp only [Complex.mul_re, chordBase_re, chordBase_im]
    ring
  · rw [pow_succ, h4]
    simp only [Complex.mul_im, chordBase_re, chordBase_im]
    linear_combination (x * (3 - x ^ 2) / 8) * h

lemma chordBase_pow_six (x : ℝ) :
    chordBase x ^ 6 =
      ⟨(27 - 135 * x ^ 2 + 45 * x ^ 4 - x ^ 6) / 64,
       3 * Real.sqrt 3 * x * (x ^ 4 - 10 * x ^ 2 + 9) / 32⟩ := by
  have h := sqrt_three_sq
  have h3 := chordBase_pow_three x
  refine Complex.ext ?_ ?_
  · rw [show (6 : ℕ) = 3 + 3 from rfl, pow_add, h3]
    simp only [Complex.mul_re]
    linear_combination (9 * (1 - x ^ 2) ^ 2 / 64) * h
  · rw [show (6 : ℕ) = 3 + 3 from rfl, pow_add, h3]
    simp only [Complex.mul_im]
    ring

/-- The rotated profile on an adjacent chord.  `α = A w`, `β = B w ^ 2` and
`c = ± C` are the rotated coefficients, where `w ^ 6 = -1` is the rotation. -/
def chordProfile (α β : ℂ) (c x : ℝ) : ℝ :=
  (α * (chordBase x + (starRingEnd ℂ (chordBase x)) ^ 5)).re
    + (β * ((chordBase x) ^ 2 + (starRingEnd ℂ (chordBase x)) ^ 4)).re
    + ((chordBase x) ^ 6).re
    - c * ((chordBase x) ^ 3).re

/-- The explicit quartic of the chord normal form. -/
def chordN (u v p r c x : ℝ) : ℝ :=
  x ^ 4 - 44 * x ^ 2 + 91 + 4 * p * (21 - x ^ 2) + 16 * Real.sqrt 3 * r * x
    + 10 * Real.sqrt 3 * u * (5 - x ^ 2) + 2 * v * x * (29 - x ^ 2)
    - 24 * Real.sqrt 3 * c

@[simp] lemma cmk_re (a b : ℝ) : (⟨a, b⟩ : ℂ).re = a := rfl
@[simp] lemma cmk_im (a b : ℝ) : (⟨a, b⟩ : ℂ).im = b := rfl

lemma conj_chordBase_pow_five (x : ℝ) :
    (starRingEnd ℂ (chordBase x)) ^ 5 =
      ⟨Real.sqrt 3 * (5 * x ^ 4 - 30 * x ^ 2 + 9) / 32,
       -(x * (x ^ 4 - 30 * x ^ 2 + 45) / 32)⟩ := by
  rw [← map_pow, chordBase_pow_five]
  refine Complex.ext ?_ ?_ <;> simp

lemma conj_chordBase_pow_four (x : ℝ) :
    (starRingEnd ℂ (chordBase x)) ^ 4 =
      ⟨(x ^ 4 - 18 * x ^ 2 + 9) / 16, -(Real.sqrt 3 * x * (3 - x ^ 2) / 4)⟩ := by
  rw [← map_pow, chordBase_pow_four]
  refine Complex.ext ?_ ?_ <;> simp

/-- **Chord normal form.**  On an adjacent unit chord the paired sextic model is
an explicit quartic damped by the endpoint factor `1 - x ^ 2`. -/
theorem chord_normal_form (α β : ℂ) (c x : ℝ) :
    64 * chordProfile α β c x = -64 + (1 - x ^ 2) * chordN α.re α.im β.re β.im c x := by
  simp only [chordProfile, chordN, conj_chordBase_pow_five, conj_chordBase_pow_four,
    chordBase_pow_two, chordBase_pow_three, chordBase_pow_six,
    Complex.mul_re, Complex.add_re, Complex.add_im, cmk_re,
    chordBase_re, chordBase_im]
  ring

/-- **Uniform root depth.**  Both endpoints of every adjacent chord sit at
depth exactly one, for every `A`, `B`, `C`. -/
theorem chordProfile_endpoint (α β : ℂ) (c : ℝ) :
    chordProfile α β c 1 = -1 ∧ chordProfile α β c (-1) = -1 := by
  refine ⟨?_, ?_⟩
  · have h := chord_normal_form α β c 1
    norm_num at h
    linarith
  · have h := chord_normal_form α β c (-1)
    norm_num at h
    linarith

/-- The scalar gap polynomial at `|A| = |B|`. -/
def chordGap (t : ℝ) : ℝ :=
  t ^ 6 + (5 / 8) * t ^ 5 - 43 * t ^ 4 + (651 / 8) * t ^ 3 + 91 * t ^ 2 - 82 * t + 15

/-- The rational majorant used to remove the square root from the
Cauchy--Schwarz bound on the pivot residual. -/
theorem rational_majorant (t : ℝ) :
    (29 + (5 / 16) * t ^ 2) ^ 2 - (t ^ 4 + 17 * t ^ 2 + 841)
      = 3 * t ^ 2 * (96 - 77 * t ^ 2) / 256 := by ring

theorem rational_majorant_nonneg {t : ℝ} (h0 : 0 ≤ t) (h1 : t ≤ 1) :
    t ^ 4 + 17 * t ^ 2 + 841 ≤ (29 + (5 / 16) * t ^ 2) ^ 2 := by
  have ht2 : t ^ 2 ≤ 1 := by nlinarith
  have hsq : (0 : ℝ) ≤ t ^ 2 := sq_nonneg t
  have hpos : (0 : ℝ) ≤ 3 * t ^ 2 * (96 - 77 * t ^ 2) / 256 := by nlinarith
  linarith [rational_majorant t]

/-- **Antipodal midpoint obstruction.**  Antipodal chords share the second mode
and reverse the first mode, so their midpoint values sum to a quantity free of
`A` and of the cubic.  Hence `Re β ≤ -9/28` is necessary for any antipodal
pair, whatever the first mode, the cubic, and the pivot. -/
theorem antipodal_midpoint_sum (u v p r c : ℝ) :
    (chordN u v p r c 0 + 24 * Real.sqrt 3 * c)
      + (chordN (-u) (-v) p r (-c) 0 - 24 * Real.sqrt 3 * c)
      = 2 * (91 + 84 * p) := by
  simp only [chordN]; ring

/-- Inner-cone bound: within `π/6` of the reversed first-mode direction the
whole first-mode chord profile is at most `-32`. -/
theorem inner_cone_bound {t : ℝ} (h0 : 0 ≤ t) (h1 : t ≤ 1) :
    -75 + 15 * t ^ 2 + 29 * t - t ^ 3 ≤ -32 := by
  nlinarith [sq_nonneg t, sq_nonneg (1 - t), mul_nonneg h0 h0]

/-- Outer-cone bound: within `π/3` the same profile is at most `8` in the
normalised scale. -/
theorem outer_cone_bound {t : ℝ} (h0 : 0 ≤ t) (h1 : t ≤ 1) :
    -25 + 5 * t ^ 2 + 29 * t - t ^ 3 ≤ 8 := by
  nlinarith [sq_nonneg t, sq_nonneg (1 - t), mul_nonneg h0 h0]

lemma bernstein_0 (x : ℝ) :
    chordGap x - (1 / 4 : ℝ) =
      (59 / 4 : ℝ) * ((4 : ℝ) * x) ^ 0 * ((1 : ℝ) - (4 : ℝ) * x) ^ 6
        + (68 : ℝ) * ((4 : ℝ) * x) ^ 1 * ((1 : ℝ) - (4 : ℝ) * x) ^ 5
        + (1991 / 16 : ℝ) * ((4 : ℝ) * x) ^ 2 * ((1 : ℝ) - (4 : ℝ) * x) ^ 4
        + (58379 / 512 : ℝ) * ((4 : ℝ) * x) ^ 3 * ((1 : ℝ) - (4 : ℝ) * x) ^ 3
        + (27659 / 512 : ℝ) * ((4 : ℝ) * x) ^ 4 * ((1 : ℝ) - (4 : ℝ) * x) ^ 2
        + (100181 / 8192 : ℝ) * ((4 : ℝ) * x) ^ 5 * ((1 : ℝ) - (4 : ℝ) * x) ^ 1
        + (8535 / 8192 : ℝ) * ((4 : ℝ) * x) ^ 6 * ((1 : ℝ) - (4 : ℝ) * x) ^ 0 := by
  unfold chordGap
  ring

lemma chordGap_ge_piece0 {x : ℝ} (h0 : (0 : ℝ) ≤ x) (h1 : x ≤ (1 / 4 : ℝ)) :
    (1 / 4 : ℝ) ≤ chordGap x := by
  have hs : (0 : ℝ) ≤ ((4 : ℝ) * x) := by linarith
  have hu : (0 : ℝ) ≤ ((1 : ℝ) - (4 : ℝ) * x) := by linarith
  have h0 : (0 : ℝ) ≤ (59 / 4 : ℝ) * ((4 : ℝ) * x) ^ 0 * ((1 : ℝ) - (4 : ℝ) * x) ^ 6 :=
    mul_nonneg (mul_nonneg (by norm_num) (pow_nonneg hs 0)) (pow_nonneg hu 6)
  have h1 : (0 : ℝ) ≤ (68 : ℝ) * ((4 : ℝ) * x) ^ 1 * ((1 : ℝ) - (4 : ℝ) * x) ^ 5 :=
    mul_nonneg (mul_nonneg (by norm_num) (pow_nonneg hs 1)) (pow_nonneg hu 5)
  have h2 : (0 : ℝ) ≤ (1991 / 16 : ℝ) * ((4 : ℝ) * x) ^ 2 * ((1 : ℝ) - (4 : ℝ) * x) ^ 4 :=
    mul_nonneg (mul_nonneg (by norm_num) (pow_nonneg hs 2)) (pow_nonneg hu 4)
  have h3 : (0 : ℝ) ≤ (58379 / 512 : ℝ) * ((4 : ℝ) * x) ^ 3 * ((1 : ℝ) - (4 : ℝ) * x) ^ 3 :=
    mul_nonneg (mul_nonneg (by norm_num) (pow_nonneg hs 3)) (pow_nonneg hu 3)
  have h4 : (0 : ℝ) ≤ (27659 / 512 : ℝ) * ((4 : ℝ) * x) ^ 4 * ((1 : ℝ) - (4 : ℝ) * x) ^ 2 :=
    mul_nonneg (mul_nonneg (by norm_num) (pow_nonneg hs 4)) (pow_nonneg hu 2)
  have h5 : (0 : ℝ) ≤ (100181 / 8192 : ℝ) * ((4 : ℝ) * x) ^ 5 * ((1 : ℝ) - (4 : ℝ) * x) ^ 1 :=
    mul_nonneg (mul_nonneg (by norm_num) (pow_nonneg hs 5)) (pow_nonneg hu 1)
  have h6 : (0 : ℝ) ≤ (8535 / 8192 : ℝ) * ((4 : ℝ) * x) ^ 6 * ((1 : ℝ) - (4 : ℝ) * x) ^ 0 :=
    mul_nonneg (mul_nonneg (by norm_num) (pow_nonneg hs 6)) (pow_nonneg hu 0)
  have hid := bernstein_0 x
  linarith [h0, h1, h2, h3, h4, h5, h6]

lemma bernstein_1 (x : ℝ) :
    chordGap x - (1 / 4 : ℝ) =
      (8535 / 8192 : ℝ) * ((16 : ℝ) * x + (-4 : ℝ)) ^ 0 * ((5 : ℝ) - (16 : ℝ) * x) ^ 6
        + (155869 / 32768 : ℝ) * ((16 : ℝ) * x + (-4 : ℝ)) ^ 1 * ((5 : ℝ) - (16 : ℝ) * x) ^ 5
        + (284661 / 32768 : ℝ) * ((16 : ℝ) * x + (-4 : ℝ)) ^ 2 * ((5 : ℝ) - (16 : ℝ) * x) ^ 4
        + (2104533 / 262144 : ℝ) * ((16 : ℝ) * x + (-4 : ℝ)) ^ 3 * ((5 : ℝ) - (16 : ℝ) * x) ^ 3
        + (8179407 / 2097152 : ℝ) * ((16 : ℝ) * x + (-4 : ℝ)) ^ 4 * ((5 : ℝ) - (16 : ℝ) * x) ^ 2
        + (7819689 / 8388608 : ℝ) * ((16 : ℝ) * x + (-4 : ℝ)) ^ 5 * ((5 : ℝ) - (16 : ℝ) * x) ^ 1
        + (1473051 / 16777216 : ℝ) * ((16 : ℝ) * x + (-4 : ℝ)) ^ 6 * ((5 : ℝ) - (16 : ℝ) * x) ^ 0 := by
  unfold chordGap
  ring

lemma chordGap_ge_piece1 {x : ℝ} (h0 : (1 / 4 : ℝ) ≤ x) (h1 : x ≤ (5 / 16 : ℝ)) :
    (1 / 4 : ℝ) ≤ chordGap x := by
  have hs : (0 : ℝ) ≤ ((16 : ℝ) * x + (-4 : ℝ)) := by linarith
  have hu : (0 : ℝ) ≤ ((5 : ℝ) - (16 : ℝ) * x) := by linarith
  have h0 : (0 : ℝ) ≤ (8535 / 8192 : ℝ) * ((16 : ℝ) * x + (-4 : ℝ)) ^ 0 * ((5 : ℝ) - (16 : ℝ) * x) ^ 6 :=
    mul_nonneg (mul_nonneg (by norm_num) (pow_nonneg hs 0)) (pow_nonneg hu 6)
  have h1 : (0 : ℝ) ≤ (155869 / 32768 : ℝ) * ((16 : ℝ) * x + (-4 : ℝ)) ^ 1 * ((5 : ℝ) - (16 : ℝ) * x) ^ 5 :=
    mul_nonneg (mul_nonneg (by norm_num) (pow_nonneg hs 1)) (pow_nonneg hu 5)
  have h2 : (0 : ℝ) ≤ (284661 / 32768 : ℝ) * ((16 : ℝ) * x + (-4 : ℝ)) ^ 2 * ((5 : ℝ) - (16 : ℝ) * x) ^ 4 :=
    mul_nonneg (mul_nonneg (by norm_num) (pow_nonneg hs 2)) (pow_nonneg hu 4)
  have h3 : (0 : ℝ) ≤ (2104533 / 262144 : ℝ) * ((16 : ℝ) * x + (-4 : ℝ)) ^ 3 * ((5 : ℝ) - (16 : ℝ) * x) ^ 3 :=
    mul_nonneg (mul_nonneg (by norm_num) (pow_nonneg hs 3)) (pow_nonneg hu 3)
  have h4 : (0 : ℝ) ≤ (8179407 / 2097152 : ℝ) * ((16 : ℝ) * x + (-4 : ℝ)) ^ 4 * ((5 : ℝ) - (16 : ℝ) * x) ^ 2 :=
    mul_nonneg (mul_nonneg (by norm_num) (pow_nonneg hs 4)) (pow_nonneg hu 2)
  have h5 : (0 : ℝ) ≤ (7819689 / 8388608 : ℝ) * ((16 : ℝ) * x + (-4 : ℝ)) ^ 5 * ((5 : ℝ) - (16 : ℝ) * x) ^ 1 :=
    mul_nonneg (mul_nonneg (by norm_num) (pow_nonneg hs 5)) (pow_nonneg hu 1)
  have h6 : (0 : ℝ) ≤ (1473051 / 16777216 : ℝ) * ((16 : ℝ) * x + (-4 : ℝ)) ^ 6 * ((5 : ℝ) - (16 : ℝ) * x) ^ 0 :=
    mul_nonneg (mul_nonneg (by norm_num) (pow_nonneg hs 6)) (pow_nonneg hu 0)
  have hid := bernstein_1 x
  linarith [h0, h1, h2, h3, h4, h5, h6]

lemma bernstein_2 (x : ℝ) :
    chordGap x - (1 / 4 : ℝ) =
      (1473051 / 16777216 : ℝ) * ((32 : ℝ) * x + (-10 : ℝ)) ^ 0 * ((11 : ℝ) - (32 : ℝ) * x) ^ 6
        + (2718885 / 8388608 : ℝ) * ((32 : ℝ) * x + (-10 : ℝ)) ^ 1 * ((11 : ℝ) - (32 : ℝ) * x) ^ 5
        + (29706471 / 67108864 : ℝ) * ((32 : ℝ) * x + (-10 : ℝ)) ^ 2 * ((11 : ℝ) - (32 : ℝ) * x) ^ 4
        + (300285 / 1048576 : ℝ) * ((32 : ℝ) * x + (-10 : ℝ)) ^ 3 * ((11 : ℝ) - (32 : ℝ) * x) ^ 3
        + (34164153 / 268435456 : ℝ) * ((32 : ℝ) * x + (-10 : ℝ)) ^ 4 * ((11 : ℝ) - (32 : ℝ) * x) ^ 2
        + (9702139 / 134217728 : ℝ) * ((32 : ℝ) * x + (-10 : ℝ)) ^ 5 * ((11 : ℝ) - (32 : ℝ) * x) ^ 1
        + (26890821 / 1073741824 : ℝ) * ((32 : ℝ) * x + (-10 : ℝ)) ^ 6 * ((11 : ℝ) - (32 : ℝ) * x) ^ 0 := by
  unfold chordGap
  ring

lemma chordGap_ge_piece2 {x : ℝ} (h0 : (5 / 16 : ℝ) ≤ x) (h1 : x ≤ (11 / 32 : ℝ)) :
    (1 / 4 : ℝ) ≤ chordGap x := by
  have hs : (0 : ℝ) ≤ ((32 : ℝ) * x + (-10 : ℝ)) := by linarith
  have hu : (0 : ℝ) ≤ ((11 : ℝ) - (32 : ℝ) * x) := by linarith
  have h0 : (0 : ℝ) ≤ (1473051 / 16777216 : ℝ) * ((32 : ℝ) * x + (-10 : ℝ)) ^ 0 * ((11 : ℝ) - (32 : ℝ) * x) ^ 6 :=
    mul_nonneg (mul_nonneg (by norm_num) (pow_nonneg hs 0)) (pow_nonneg hu 6)
  have h1 : (0 : ℝ) ≤ (2718885 / 8388608 : ℝ) * ((32 : ℝ) * x + (-10 : ℝ)) ^ 1 * ((11 : ℝ) - (32 : ℝ) * x) ^ 5 :=
    mul_nonneg (mul_nonneg (by norm_num) (pow_nonneg hs 1)) (pow_nonneg hu 5)
  have h2 : (0 : ℝ) ≤ (29706471 / 67108864 : ℝ) * ((32 : ℝ) * x + (-10 : ℝ)) ^ 2 * ((11 : ℝ) - (32 : ℝ) * x) ^ 4 :=
    mul_nonneg (mul_nonneg (by norm_num) (pow_nonneg hs 2)) (pow_nonneg hu 4)
  have h3 : (0 : ℝ) ≤ (300285 / 1048576 : ℝ) * ((32 : ℝ) * x + (-10 : ℝ)) ^ 3 * ((11 : ℝ) - (32 : ℝ) * x) ^ 3 :=
    mul_nonneg (mul_nonneg (by norm_num) (pow_nonneg hs 3)) (pow_nonneg hu 3)
  have h4 : (0 : ℝ) ≤ (34164153 / 268435456 : ℝ) * ((32 : ℝ) * x + (-10 : ℝ)) ^ 4 * ((11 : ℝ) - (32 : ℝ) * x) ^ 2 :=
    mul_nonneg (mul_nonneg (by norm_num) (pow_nonneg hs 4)) (pow_nonneg hu 2)
  have h5 : (0 : ℝ) ≤ (9702139 / 134217728 : ℝ) * ((32 : ℝ) * x + (-10 : ℝ)) ^ 5 * ((11 : ℝ) - (32 : ℝ) * x) ^ 1 :=
    mul_nonneg (mul_nonneg (by norm_num) (pow_nonneg hs 5)) (pow_nonneg hu 1)
  have h6 : (0 : ℝ) ≤ (26890821 / 1073741824 : ℝ) * ((32 : ℝ) * x + (-10 : ℝ)) ^ 6 * ((11 : ℝ) - (32 : ℝ) * x) ^ 0 :=
    mul_nonneg (mul_nonneg (by norm_num) (pow_nonneg hs 6)) (pow_nonneg hu 0)
  have hid := bernstein_2 x
  linarith [h0, h1, h2, h3, h4, h5, h6]

lemma bernstein_3 (x : ℝ) :
    chordGap x - (1 / 4 : ℝ) =
      (26890821 / 1073741824 : ℝ) * ((32 : ℝ) * x + (-11 : ℝ)) ^ 0 * ((12 : ℝ) - (32 : ℝ) * x) ^ 6
        + (61268185 / 268435456 : ℝ) * ((32 : ℝ) * x + (-11 : ℝ)) ^ 1 * ((12 : ℝ) - (32 : ℝ) * x) ^ 5
        + (30435461 / 33554432 : ℝ) * ((32 : ℝ) * x + (-11 : ℝ)) ^ 2 * ((12 : ℝ) - (32 : ℝ) * x) ^ 4
        + (15496937 / 8388608 : ℝ) * ((32 : ℝ) * x + (-11 : ℝ)) ^ 3 * ((12 : ℝ) - (32 : ℝ) * x) ^ 3
        + (8416169 / 4194304 : ℝ) * ((32 : ℝ) * x + (-11 : ℝ)) ^ 4 * ((12 : ℝ) - (32 : ℝ) * x) ^ 2
        + (1162085 / 1048576 : ℝ) * ((32 : ℝ) * x + (-11 : ℝ)) ^ 5 * ((12 : ℝ) - (32 : ℝ) * x) ^ 1
        + (8035 / 32768 : ℝ) * ((32 : ℝ) * x + (-11 : ℝ)) ^ 6 * ((12 : ℝ) - (32 : ℝ) * x) ^ 0 := by
  unfold chordGap
  ring

lemma chordGap_ge_piece3 {x : ℝ} (h0 : (11 / 32 : ℝ) ≤ x) (h1 : x ≤ (3 / 8 : ℝ)) :
    (1 / 4 : ℝ) ≤ chordGap x := by
  have hs : (0 : ℝ) ≤ ((32 : ℝ) * x + (-11 : ℝ)) := by linarith
  have hu : (0 : ℝ) ≤ ((12 : ℝ) - (32 : ℝ) * x) := by linarith
  have h0 : (0 : ℝ) ≤ (26890821 / 1073741824 : ℝ) * ((32 : ℝ) * x + (-11 : ℝ)) ^ 0 * ((12 : ℝ) - (32 : ℝ) * x) ^ 6 :=
    mul_nonneg (mul_nonneg (by norm_num) (pow_nonneg hs 0)) (pow_nonneg hu 6)
  have h1 : (0 : ℝ) ≤ (61268185 / 268435456 : ℝ) * ((32 : ℝ) * x + (-11 : ℝ)) ^ 1 * ((12 : ℝ) - (32 : ℝ) * x) ^ 5 :=
    mul_nonneg (mul_nonneg (by norm_num) (pow_nonneg hs 1)) (pow_nonneg hu 5)
  have h2 : (0 : ℝ) ≤ (30435461 / 33554432 : ℝ) * ((32 : ℝ) * x + (-11 : ℝ)) ^ 2 * ((12 : ℝ) - (32 : ℝ) * x) ^ 4 :=
    mul_nonneg (mul_nonneg (by norm_num) (pow_nonneg hs 2)) (pow_nonneg hu 4)
  have h3 : (0 : ℝ) ≤ (15496937 / 8388608 : ℝ) * ((32 : ℝ) * x + (-11 : ℝ)) ^ 3 * ((12 : ℝ) - (32 : ℝ) * x) ^ 3 :=
    mul_nonneg (mul_nonneg (by norm_num) (pow_nonneg hs 3)) (pow_nonneg hu 3)
  have h4 : (0 : ℝ) ≤ (8416169 / 4194304 : ℝ) * ((32 : ℝ) * x + (-11 : ℝ)) ^ 4 * ((12 : ℝ) - (32 : ℝ) * x) ^ 2 :=
    mul_nonneg (mul_nonneg (by norm_num) (pow_nonneg hs 4)) (pow_nonneg hu 2)
  have h5 : (0 : ℝ) ≤ (1162085 / 1048576 : ℝ) * ((32 : ℝ) * x + (-11 : ℝ)) ^ 5 * ((12 : ℝ) - (32 : ℝ) * x) ^ 1 :=
    mul_nonneg (mul_nonneg (by norm_num) (pow_nonneg hs 5)) (pow_nonneg hu 1)
  have h6 : (0 : ℝ) ≤ (8035 / 32768 : ℝ) * ((32 : ℝ) * x + (-11 : ℝ)) ^ 6 * ((12 : ℝ) - (32 : ℝ) * x) ^ 0 :=
    mul_nonneg (mul_nonneg (by norm_num) (pow_nonneg hs 6)) (pow_nonneg hu 0)
  have hid := bernstein_3 x
  linarith [h0, h1, h2, h3, h4, h5, h6]

lemma bernstein_4 (x : ℝ) :
    chordGap x - (1 / 4 : ℝ) =
      (8035 / 32768 : ℝ) * ((8 : ℝ) * x + (-3 : ℝ)) ^ 0 * ((4 : ℝ) - (8 : ℝ) * x) ^ 6
        + (766315 / 262144 : ℝ) * ((8 : ℝ) * x + (-3 : ℝ)) ^ 1 * ((4 : ℝ) - (8 : ℝ) * x) ^ 5
        + (867261 / 65536 : ℝ) * ((8 : ℝ) * x + (-3 : ℝ)) ^ 2 * ((4 : ℝ) - (8 : ℝ) * x) ^ 4
        + (234633 / 8192 : ℝ) * ((8 : ℝ) * x + (-3 : ℝ)) ^ 3 * ((4 : ℝ) - (8 : ℝ) * x) ^ 3
        + (65679 / 2048 : ℝ) * ((8 : ℝ) * x + (-3 : ℝ)) ^ 4 * ((4 : ℝ) - (8 : ℝ) * x) ^ 2
        + (18435 / 1024 : ℝ) * ((8 : ℝ) * x + (-3 : ℝ)) ^ 5 * ((4 : ℝ) - (8 : ℝ) * x) ^ 1
        + (1029 / 256 : ℝ) * ((8 : ℝ) * x + (-3 : ℝ)) ^ 6 * ((4 : ℝ) - (8 : ℝ) * x) ^ 0 := by
  unfold chordGap
  ring

lemma chordGap_ge_piece4 {x : ℝ} (h0 : (3 / 8 : ℝ) ≤ x) (h1 : x ≤ (1 / 2 : ℝ)) :
    (1 / 4 : ℝ) ≤ chordGap x := by
  have hs : (0 : ℝ) ≤ ((8 : ℝ) * x + (-3 : ℝ)) := by linarith
  have hu : (0 : ℝ) ≤ ((4 : ℝ) - (8 : ℝ) * x) := by linarith
  have h0 : (0 : ℝ) ≤ (8035 / 32768 : ℝ) * ((8 : ℝ) * x + (-3 : ℝ)) ^ 0 * ((4 : ℝ) - (8 : ℝ) * x) ^ 6 :=
    mul_nonneg (mul_nonneg (by norm_num) (pow_nonneg hs 0)) (pow_nonneg hu 6)
  have h1 : (0 : ℝ) ≤ (766315 / 262144 : ℝ) * ((8 : ℝ) * x + (-3 : ℝ)) ^ 1 * ((4 : ℝ) - (8 : ℝ) * x) ^ 5 :=
    mul_nonneg (mul_nonneg (by norm_num) (pow_nonneg hs 1)) (pow_nonneg hu 5)
  have h2 : (0 : ℝ) ≤ (867261 / 65536 : ℝ) * ((8 : ℝ) * x + (-3 : ℝ)) ^ 2 * ((4 : ℝ) - (8 : ℝ) * x) ^ 4 :=
    mul_nonneg (mul_nonneg (by norm_num) (pow_nonneg hs 2)) (pow_nonneg hu 4)
  have h3 : (0 : ℝ) ≤ (234633 / 8192 : ℝ) * ((8 : ℝ) * x + (-3 : ℝ)) ^ 3 * ((4 : ℝ) - (8 : ℝ) * x) ^ 3 :=
    mul_nonneg (mul_nonneg (by norm_num) (pow_nonneg hs 3)) (pow_nonneg hu 3)
  have h4 : (0 : ℝ) ≤ (65679 / 2048 : ℝ) * ((8 : ℝ) * x + (-3 : ℝ)) ^ 4 * ((4 : ℝ) - (8 : ℝ) * x) ^ 2 :=
    mul_nonneg (mul_nonneg (by norm_num) (pow_nonneg hs 4)) (pow_nonneg hu 2)
  have h5 : (0 : ℝ) ≤ (18435 / 1024 : ℝ) * ((8 : ℝ) * x + (-3 : ℝ)) ^ 5 * ((4 : ℝ) - (8 : ℝ) * x) ^ 1 :=
    mul_nonneg (mul_nonneg (by norm_num) (pow_nonneg hs 5)) (pow_nonneg hu 1)
  have h6 : (0 : ℝ) ≤ (1029 / 256 : ℝ) * ((8 : ℝ) * x + (-3 : ℝ)) ^ 6 * ((4 : ℝ) - (8 : ℝ) * x) ^ 0 :=
    mul_nonneg (mul_nonneg (by norm_num) (pow_nonneg hs 6)) (pow_nonneg hu 0)
  have hid := bernstein_4 x
  linarith [h0, h1, h2, h3, h4, h5, h6]

lemma bernstein_5 (x : ℝ) :
    chordGap x - (1 / 4 : ℝ) =
      (1029 / 256 : ℝ) * ((2 : ℝ) * x + (-1 : ℝ)) ^ 0 * ((2 : ℝ) - (2 : ℝ) * x) ^ 6
        + (12435 / 256 : ℝ) * ((2 : ℝ) * x + (-1 : ℝ)) ^ 1 * ((2 : ℝ) - (2 : ℝ) * x) ^ 5
        + (28179 / 128 : ℝ) * ((2 : ℝ) * x + (-1 : ℝ)) ^ 2 * ((2 : ℝ) - (2 : ℝ) * x) ^ 4
        + (30411 / 64 : ℝ) * ((2 : ℝ) * x + (-1 : ℝ)) ^ 3 * ((2 : ℝ) - (2 : ℝ) * x) ^ 3
        + (16887 / 32 : ℝ) * ((2 : ℝ) * x + (-1 : ℝ)) ^ 4 * ((2 : ℝ) - (2 : ℝ) * x) ^ 2
        + (2335 / 8 : ℝ) * ((2 : ℝ) * x + (-1 : ℝ)) ^ 5 * ((2 : ℝ) - (2 : ℝ) * x) ^ 1
        + (255 / 4 : ℝ) * ((2 : ℝ) * x + (-1 : ℝ)) ^ 6 * ((2 : ℝ) - (2 : ℝ) * x) ^ 0 := by
  unfold chordGap
  ring

lemma chordGap_ge_piece5 {x : ℝ} (h0 : (1 / 2 : ℝ) ≤ x) (h1 : x ≤ (1 : ℝ)) :
    (1 / 4 : ℝ) ≤ chordGap x := by
  have hs : (0 : ℝ) ≤ ((2 : ℝ) * x + (-1 : ℝ)) := by linarith
  have hu : (0 : ℝ) ≤ ((2 : ℝ) - (2 : ℝ) * x) := by linarith
  have h0 : (0 : ℝ) ≤ (1029 / 256 : ℝ) * ((2 : ℝ) * x + (-1 : ℝ)) ^ 0 * ((2 : ℝ) - (2 : ℝ) * x) ^ 6 :=
    mul_nonneg (mul_nonneg (by norm_num) (pow_nonneg hs 0)) (pow_nonneg hu 6)
  have h1 : (0 : ℝ) ≤ (12435 / 256 : ℝ) * ((2 : ℝ) * x + (-1 : ℝ)) ^ 1 * ((2 : ℝ) - (2 : ℝ) * x) ^ 5 :=
    mul_nonneg (mul_nonneg (by norm_num) (pow_nonneg hs 1)) (pow_nonneg hu 5)
  have h2 : (0 : ℝ) ≤ (28179 / 128 : ℝ) * ((2 : ℝ) * x + (-1 : ℝ)) ^ 2 * ((2 : ℝ) - (2 : ℝ) * x) ^ 4 :=
    mul_nonneg (mul_nonneg (by norm_num) (pow_nonneg hs 2)) (pow_nonneg hu 4)
  have h3 : (0 : ℝ) ≤ (30411 / 64 : ℝ) * ((2 : ℝ) * x + (-1 : ℝ)) ^ 3 * ((2 : ℝ) - (2 : ℝ) * x) ^ 3 :=
    mul_nonneg (mul_nonneg (by norm_num) (pow_nonneg hs 3)) (pow_nonneg hu 3)
  have h4 : (0 : ℝ) ≤ (16887 / 32 : ℝ) * ((2 : ℝ) * x + (-1 : ℝ)) ^ 4 * ((2 : ℝ) - (2 : ℝ) * x) ^ 2 :=
    mul_nonneg (mul_nonneg (by norm_num) (pow_nonneg hs 4)) (pow_nonneg hu 2)
  have h5 : (0 : ℝ) ≤ (2335 / 8 : ℝ) * ((2 : ℝ) * x + (-1 : ℝ)) ^ 5 * ((2 : ℝ) - (2 : ℝ) * x) ^ 1 :=
    mul_nonneg (mul_nonneg (by norm_num) (pow_nonneg hs 5)) (pow_nonneg hu 1)
  have h6 : (0 : ℝ) ≤ (255 / 4 : ℝ) * ((2 : ℝ) * x + (-1 : ℝ)) ^ 6 * ((2 : ℝ) - (2 : ℝ) * x) ^ 0 :=
    mul_nonneg (mul_nonneg (by norm_num) (pow_nonneg hs 6)) (pow_nonneg hu 0)
  have hid := bernstein_5 x
  linarith [h0, h1, h2, h3, h4, h5, h6]

/-- **Six-piece Bernstein certificate.**  The gap polynomial at `|A| = |B|`
never drops below `1/4` on the unit interval. -/
theorem chordGap_ge {x : ℝ} (h0 : 0 ≤ x) (h1 : x ≤ 1) : (1 / 4 : ℝ) ≤ chordGap x := by
  rcases le_total x (1 / 4 : ℝ) with h | h
  · exact chordGap_ge_piece0 h0 h
  rcases le_total x (5 / 16 : ℝ) with h' | h'
  · exact chordGap_ge_piece1 (by linarith) h'
  rcases le_total x (11 / 32 : ℝ) with h'' | h''
  · exact chordGap_ge_piece2 (by linarith) h''
  rcases le_total x (3 / 8 : ℝ) with h₃ | h₃
  · exact chordGap_ge_piece3 (by linarith) h₃
  rcases le_total x (1 / 2 : ℝ) with h₄ | h₄
  · exact chordGap_ge_piece4 (by linarith) h₄
  · exact chordGap_ge_piece5 (by linarith) h1

/-- **Uniform chord margin.**  Whenever the certified chain bounds `64` times
the larger of the two antipodal chord profiles by `-chordGap`, that profile is
at most `-1/256`. -/
theorem chord_margin {h t : ℝ} (h0 : 0 ≤ t) (h1 : t ≤ 1)
    (hchain : 64 * h ≤ -chordGap t) : h ≤ -(1 / 256 : ℝ) := by
  have := chordGap_ge h0 h1
  linarith

end

end ErdosProblems.Erdos1041.SexticChordCoveringCriterion
