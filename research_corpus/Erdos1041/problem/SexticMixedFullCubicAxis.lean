import ErdosProblems.Erdos1041.SexticMixedCubicLiftWindow
import Mathlib.Tactic

/-!
# Erdős #1041: two tiles cover the full cubic axis of a mixed cell

The adjacent pair `(0,1)` covers the upper cubic half-line.  Its reflection
`(5,0)` covers the lower half-line.  Both use radius `2/3`, and their ranges
overlap.  This closes the complete real tangent-cubic axis above the first
open mixed `(A,B)` coefficient cell.
-/

namespace ErdosProblems.Erdos1041.SexticMixedFullCubicAxis

open ErdosProblems.Erdos1041.SexticCanonicalMixedSlice
open ErdosProblems.Erdos1041.SexticMixedOriginSpokeNoGo
open ErdosProblems.Erdos1041.SexticMixedTruncatedNeighborhood
open ErdosProblems.Erdos1041.SexticMixedCubicLiftWindow
open ErdosProblems.Erdos1041.SexticSecondModeCubicLift
open ErdosProblems.Erdos1041.SexticFirstModeDominantTangentCone

noncomputable section

def reflectedChordPoint (u : ℝ) : ℂ :=
  ⟨(2 / 3) * (1 / 2 + u / 2), -(1 - u) * sqrtThree / 3⟩

def rayFivePoint (t : ℝ) : ℂ :=
  ⟨t / 2, -t * sqrtThree / 2⟩

def reflectedC0 : ℝ := -(-45 * (sqrtTwo * sqrtThree) + 45 * sqrtTwo + 64) / 729
def reflectedC1 : ℝ :=
  -(-144 * (sqrtTwo * sqrtThree) + 256 + 161 * sqrtThree + 960 * sqrtTwo) / 5832
def reflectedC2 : ℝ :=
  -(-640 - 108 * (sqrtTwo * sqrtThree) + 645 * sqrtThree + 3396 * sqrtTwo) / 14580
def reflectedC3 : ℝ :=
  -(-2560 + 1455 * sqrtThree + 7488 * sqrtTwo) / 29160
def reflectedC4 : ℝ :=
  -(-320 + 54 * (sqrtTwo * sqrtThree) + 365 * sqrtThree + 1698 * sqrtTwo) / 7290
def reflectedC5 : ℝ :=
  -(256 + 144 * (sqrtTwo * sqrtThree) + 309 * sqrtThree + 960 * sqrtTwo) / 5832
def reflectedC6 : ℝ :=
  -(180 * sqrtTwo + 256 + 195 * sqrtThree + 180 * (sqrtTwo * sqrtThree)) / 2916

def reflectedChordBernstein (u : ℝ) : ℝ :=
    reflectedC0 * (1 - u) ^ 6
  + reflectedC1 * (6 * u * (1 - u) ^ 5)
  + reflectedC2 * (15 * u ^ 2 * (1 - u) ^ 4)
  + reflectedC3 * (20 * u ^ 3 * (1 - u) ^ 3)
  + reflectedC4 * (15 * u ^ 4 * (1 - u) ^ 2)
  + reflectedC5 * (6 * u ^ 5 * (1 - u))
  + reflectedC6 * u ^ 6

theorem endpoint_reflected_chord_identity (u : ℝ) :
    pairedTangentComplex endpointA endpointB (reflectedChordPoint u) =
      reflectedChordBernstein u := by
  have hs2 : sqrtThree ^ 2 = 3 := sqrtThree_sq
  have hs3 : sqrtThree ^ 3 = 3 * sqrtThree := by
    calc sqrtThree ^ 3 = sqrtThree ^ 2 * sqrtThree := by ring
         _ = 3 * sqrtThree := by rw [hs2]
  have hs4 : sqrtThree ^ 4 = 9 := by
    calc sqrtThree ^ 4 = (sqrtThree ^ 2) ^ 2 := by ring
         _ = 3 ^ 2 := by rw [hs2]
         _ = 9 := by norm_num
  have hs5 : sqrtThree ^ 5 = 9 * sqrtThree := by
    calc sqrtThree ^ 5 = sqrtThree ^ 4 * sqrtThree := by ring
         _ = 9 * sqrtThree := by rw [hs4]
  have hs6 : sqrtThree ^ 6 = 27 := by
    calc sqrtThree ^ 6 = (sqrtThree ^ 2) ^ 3 := by ring
         _ = 3 ^ 3 := by rw [hs2]
         _ = 27 := by norm_num
  simp [pairedTangentComplex, endpointA, endpointB, reflectedChordPoint,
    reflectedChordBernstein, reflectedC0, reflectedC1, reflectedC2,
    reflectedC3, reflectedC4, reflectedC5, reflectedC6,
    Complex.mul_re, Complex.mul_im, Complex.conj_re, Complex.conj_im, pow_succ]
  ring_nf
  rw [hs6, hs5, hs4, hs3, hs2]
  ring

theorem reflected_coefficients_uniformly_negative :
    reflectedC0 ≤ -(1 : ℝ) / 1000 ∧ reflectedC1 ≤ -(1 : ℝ) / 1000 ∧
    reflectedC2 ≤ -(1 : ℝ) / 1000 ∧ reflectedC3 ≤ -(1 : ℝ) / 1000 ∧
    reflectedC4 ≤ -(1 : ℝ) / 1000 ∧ reflectedC5 ≤ -(1 : ℝ) / 1000 ∧
    reflectedC6 ≤ -(1 : ℝ) / 1000 := by
  have hs2l := sqrtTwo_gt_sevenFifths
  have hs2u := sqrtTwo_lt_threeHalves
  have hs3l := sqrtThree_gt_fiveThirds
  have hs3u := sqrtThree_lt_sevenFourths
  have hs6u : sqrtTwo * sqrtThree < 21 / 8 := by
    calc
      sqrtTwo * sqrtThree < (3 / 2 : ℝ) * sqrtThree :=
        mul_lt_mul_of_pos_right hs2u sqrtThree_pos
      _ < (3 / 2 : ℝ) * (7 / 4 : ℝ) :=
        mul_lt_mul_of_pos_left hs3u (by norm_num)
      _ = 21 / 8 := by ring
  have hs6l : 7 / 3 < sqrtTwo * sqrtThree := by
    have h1 : (7 / 5 : ℝ) * sqrtThree < sqrtTwo * sqrtThree :=
      mul_lt_mul_of_pos_right hs2l sqrtThree_pos
    have h2 : (7 / 3 : ℝ) < (7 / 5 : ℝ) * sqrtThree := by nlinarith
    linarith
  unfold reflectedC0 reflectedC1 reflectedC2 reflectedC3 reflectedC4
    reflectedC5 reflectedC6
  constructor
  · nlinarith
  constructor
  · nlinarith
  constructor
  · nlinarith
  constructor
  · nlinarith
  constructor
  · nlinarith
  constructor <;> nlinarith

theorem endpoint_reflected_chord_le {u : ℝ} (hu0 : 0 ≤ u) (hu1 : u ≤ 1) :
    pairedTangentComplex endpointA endpointB (reflectedChordPoint u) ≤
      -(1 : ℝ) / 1000 := by
  have homu : 0 ≤ 1 - u := sub_nonneg.mpr hu1
  rcases reflected_coefficients_uniformly_negative with
    ⟨hc0, hc1, hc2, hc3, hc4, hc5, hc6⟩
  have h0 := mul_le_mul_of_nonneg_right hc0 (by positivity : 0 ≤ (1 - u) ^ 6)
  have h1 := mul_le_mul_of_nonneg_right hc1 (by positivity : 0 ≤ 6 * u * (1 - u) ^ 5)
  have h2 := mul_le_mul_of_nonneg_right hc2 (by positivity : 0 ≤ 15 * u ^ 2 * (1 - u) ^ 4)
  have h3 := mul_le_mul_of_nonneg_right hc3 (by positivity : 0 ≤ 20 * u ^ 3 * (1 - u) ^ 3)
  have h4 := mul_le_mul_of_nonneg_right hc4 (by positivity : 0 ≤ 15 * u ^ 4 * (1 - u) ^ 2)
  have h5 := mul_le_mul_of_nonneg_right hc5 (by positivity : 0 ≤ 6 * u ^ 5 * (1 - u))
  have h6 := mul_le_mul_of_nonneg_right hc6 (by positivity : 0 ≤ u ^ 6)
  have hsum := bernsteinSix_partition u
  rw [endpoint_reflected_chord_identity]
  unfold reflectedChordBernstein
  nlinarith

theorem reflectedChordPoint_norm_le_one {u : ℝ} (hu0 : 0 ≤ u) (hu1 : u ≤ 1) :
    ‖reflectedChordPoint u‖ ≤ 1 := by
  have hsq : Complex.normSq (reflectedChordPoint u) = (4 / 9) * (1 - u + u ^ 2) := by
    simp [reflectedChordPoint, Complex.normSq_apply]
    ring_nf
    linear_combination ((1 - u) ^ 2 / 9) * sqrtThree_sq
  rw [Complex.normSq_eq_norm_sq] at hsq
  have hprod : 0 ≤ u * (1 - u) := mul_nonneg hu0 (sub_nonneg.mpr hu1)
  have hpoly : 1 - u + u ^ 2 ≤ 1 := by nlinarith
  have hnormsq : ‖reflectedChordPoint u‖ ^ 2 ≤ 4 / 9 := by nlinarith
  nlinarith [norm_nonneg (reflectedChordPoint u), sq_nonneg (‖reflectedChordPoint u‖ - 1)]

theorem rayFivePoint_norm_le_one {t : ℝ} (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    ‖rayFivePoint t‖ ≤ 1 := by
  have hsq : Complex.normSq (rayFivePoint t) = t ^ 2 := by
    simp [rayFivePoint, Complex.normSq_apply]
    ring_nf
    linear_combination (t ^ 2 / 4) * sqrtThree_sq
  rw [Complex.normSq_eq_norm_sq] at hsq
  have heq : ‖rayFivePoint t‖ = t := by
    nlinarith [norm_nonneg (rayFivePoint t), sq_nonneg (‖rayFivePoint t‖ - t)]
  linarith

theorem endpoint_rayFive_identity (t : ℝ) :
    pairedTangentComplex endpointA endpointB (rayFivePoint t) =
      pairedTangentRay aZero bLow t := by
  have hs2 := sqrtThree_sq
  have hs3 : sqrtThree ^ 3 = 3 * sqrtThree := by
    calc sqrtThree ^ 3 = sqrtThree ^ 2 * sqrtThree := by ring
         _ = 3 * sqrtThree := by rw [hs2]
  have hs4 : sqrtThree ^ 4 = 9 := by
    calc sqrtThree ^ 4 = (sqrtThree ^ 2) ^ 2 := by ring
         _ = 3 ^ 2 := by rw [hs2]
         _ = 9 := by norm_num
  have hs5 : sqrtThree ^ 5 = 9 * sqrtThree := by
    calc sqrtThree ^ 5 = sqrtThree ^ 4 * sqrtThree := by ring
         _ = 9 * sqrtThree := by rw [hs4]
  have hs6 : sqrtThree ^ 6 = 27 := by
    calc sqrtThree ^ 6 = (sqrtThree ^ 2) ^ 3 := by ring
         _ = 3 ^ 3 := by rw [hs2]
         _ = 27 := by norm_num
  simp [pairedTangentComplex, endpointA, endpointB, rayFivePoint,
    pairedTangentRay, aZero, bLow, Complex.mul_re, Complex.mul_im,
    Complex.conj_re, Complex.conj_im, pow_succ]
  ring_nf
  rw [hs6, hs5, hs4, hs3, hs2]
  ring

theorem endpoint_rayFive_le {t : ℝ} (ht : 2 / 3 ≤ t) (ht1 : t ≤ 1) :
    pairedTangentComplex endpointA endpointB (rayFivePoint t) ≤
      -(107 : ℝ) / 5832 := by
  have ht0 : 0 ≤ t := by nlinarith
  have ht2lo : 4 / 9 ≤ t ^ 2 := by nlinarith [sq_nonneg (t - 2 / 3)]
  have ht2hi : t ^ 2 ≤ 1 := pow_le_one₀ ht0 ht1
  have ht4lo : 16 / 81 ≤ t ^ 4 := by
    have hp := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 2 / 3) ht 4
    norm_num at hp ⊢
    exact hp
  have hb : bLow ≤ (9 : ℝ) / 32 := by
    unfold bLow
    have htail : 0 ≤ sqrtThree - 1 := by nlinarith [sqrtThree_gt_fiveThirds]
    have hs2u := le_of_lt sqrtTwo_lt_threeHalves
    have htailu : sqrtThree - 1 ≤ (3 : ℝ) / 4 := by
      nlinarith [sqrtThree_lt_sevenFourths]
    have hmul := mul_le_mul hs2u htailu htail (by norm_num : (0 : ℝ) ≤ 3 / 2)
    nlinarith
  have hq : 0 ≤ t ^ 2 - t ^ 4 := by
    have heq : t ^ 2 - t ^ 4 = t ^ 2 * (1 - t ^ 2) := by ring
    rw [heq]
    exact mul_nonneg (sq_nonneg t) (sub_nonneg.mpr ht2hi)
  rw [endpoint_rayFive_identity]
  unfold pairedTangentRay aZero
  have hmul := mul_le_mul_of_nonneg_left hb hq
  have hbracket : (9 : ℝ) / 32 * (1 - t ^ 2) - t ^ 4 ≤ -107 / 2592 := by
    nlinarith
  have hfactor : (9 : ℝ) / 32 * (t ^ 2 - t ^ 4) - t ^ 6 =
      t ^ 2 * ((9 : ℝ) / 32 * (1 - t ^ 2) - t ^ 4) := by ring
  have hneg : t ^ 2 * ((9 : ℝ) / 32 * (1 - t ^ 2) - t ^ 4) ≤
      (4 / 9 : ℝ) * (-107 / 2592) := by
    have hm := mul_le_mul_of_nonpos_right ht2lo (by linarith :
      (9 : ℝ) / 32 * (1 - t ^ 2) - t ^ 4 ≤ 0)
    nlinarith
  have hscaled : (9 : ℝ) / 32 * (t ^ 2 - t ^ 4) - t ^ 6 ≤ -107 / 5832 := by
    rw [hfactor]
    norm_num at hneg ⊢
    exact hneg
  nlinarith

theorem reflected_chord_cube_im_mem_neg_unit {u : ℝ} (hu0 : 0 ≤ u) (hu1 : u ≤ 1) :
    -1 ≤ (reflectedChordPoint u ^ 3).im ∧ (reflectedChordPoint u ^ 3).im ≤ 0 := by
  have heq : (reflectedChordPoint u ^ 3).im =
      -(4 * sqrtThree / 9) * u * (1 - u) := by
    have hs3 : sqrtThree ^ 3 = 3 * sqrtThree := by
      calc sqrtThree ^ 3 = sqrtThree ^ 2 * sqrtThree := by ring
           _ = 3 * sqrtThree := by rw [sqrtThree_sq]
    simp [reflectedChordPoint, pow_succ, Complex.mul_re, Complex.mul_im]
    ring_nf
    rw [hs3]
    ring
  rw [heq]
  have hs0 : 0 ≤ sqrtThree := le_of_lt sqrtThree_pos
  have hp0 : 0 ≤ u * (1 - u) := mul_nonneg hu0 (sub_nonneg.mpr hu1)
  have hp4 : u * (1 - u) ≤ 1 / 4 := by nlinarith [sq_nonneg (u - 1 / 2)]
  have hsUpper := sqrtThree_lt_sevenFourths
  constructor
  · have hmul := mul_le_mul hp4 (le_of_lt hsUpper) hs0 (by norm_num : (0 : ℝ) ≤ 1 / 4)
    nlinarith
  · have hcoef : 0 ≤ (4 * sqrtThree / 9 : ℝ) := by positivity
    have hmul := mul_nonneg hcoef hp0
    linarith

theorem reflected_tangentCubic_le {c u : ℝ} (hc : c ≤ (1 : ℝ) / 10000)
    (hu0 : 0 ≤ u) (hu1 : u ≤ 1) :
    tangentCubic c (reflectedChordPoint u) ≤ 1 / 10000 := by
  rcases reflected_chord_cube_im_mem_neg_unit hu0 hu1 with ⟨himLo, himHi⟩
  rw [tangentCubic_eq_neg_mul_im]
  by_cases hc0 : 0 ≤ c
  · have himNeg : 0 ≤ -(reflectedChordPoint u ^ 3).im := by nlinarith
    have hm := mul_le_mul_of_nonneg_right hc himNeg
    nlinarith
  · have hcneg : c < 0 := lt_of_not_ge hc0
    have : -c * (reflectedChordPoint u ^ 3).im ≤ 0 :=
      mul_nonpos_of_nonneg_of_nonpos (by nlinarith) himHi
    linarith

theorem reflected_rayFive_cube_im_zero (t : ℝ) : (rayFivePoint t ^ 3).im = 0 := by
  have hs2 := sqrtThree_sq
  simp [rayFivePoint, pow_succ, Complex.mul_re, Complex.mul_im]
  ring_nf at hs2 ⊢
  linear_combination (t ^ 3 * sqrtThree / 8) * hs2

theorem reflected_coefficient_ball_connector {A B : ℂ} {c : ℝ}
    (hA : ‖A - endpointA‖ ≤ 1 / 10000)
    (hB : ‖B - endpointB‖ ≤ 1 / 10000)
    (hc : c ≤ (1 : ℝ) / 10000) :
    (∀ u : ℝ, 0 ≤ u → u ≤ 1 → mixedCubicModel A B c (reflectedChordPoint u) < 0) ∧
    (∀ t : ℝ, 2 / 3 ≤ t → t ≤ 1 → mixedCubicModel A B c (rayFivePoint t) < 0) ∧
    (∀ t : ℝ, 2 / 3 ≤ t → t ≤ 1 → mixedCubicModel A B c (rayZeroPoint t) ≤ 0) := by
  let dA := A - endpointA
  let dB := B - endpointB
  have hAid : endpointA + dA = A := by dsimp [dA]; ring
  have hBid : endpointB + dB = B := by dsimp [dB]; ring
  refine ⟨?_, ?_, ?_⟩
  · intro u hu0 hu1
    have herr := tangentError_re_abs_le (by norm_num : (0 : ℝ) ≤ 1 / 10000)
      hA hB (reflectedChordPoint_norm_le_one hu0 hu1)
    have herrUp : (tangentError dA dB (reflectedChordPoint u)).re ≤ 4 / 10000 := by
      nlinarith [le_abs_self (tangentError dA dB (reflectedChordPoint u)).re]
    have hbase := endpoint_reflected_chord_le hu0 hu1
    have hcubic := reflected_tangentCubic_le hc hu0 hu1
    rw [mixedCubicModel, ← hAid, ← hBid, pairedTangentComplex_add]
    nlinarith
  · intro t ht ht1
    have ht0 : 0 ≤ t := by nlinarith
    have herr := tangentError_re_abs_le (by norm_num : (0 : ℝ) ≤ 1 / 10000)
      hA hB (rayFivePoint_norm_le_one ht0 ht1)
    have herrUp : (tangentError dA dB (rayFivePoint t)).re ≤ 4 / 10000 := by
      nlinarith [le_abs_self (tangentError dA dB (rayFivePoint t)).re]
    have hbase := endpoint_rayFive_le ht ht1
    have hcubic : tangentCubic c (rayFivePoint t) = 0 :=
      tangentCubic_eq_zero_of_cube_im_zero (reflected_rayFive_cube_im_zero t)
    rw [mixedCubicModel, ← hAid, ← hBid, pairedTangentComplex_add, hcubic, add_zero]
    nlinarith
  · intro t ht ht1
    have hzero : tangentCubic c (rayZeroPoint t) = 0 := tangentCubic_rayZero_zero c t
    rw [mixedCubicModel, hzero, add_zero, ← hAid, ← hBid]
    exact perturbed_rayZero_nonpos hA hB (by nlinarith) ht1

/-- Every real cubic coefficient is covered by one of two adjacent radius-
`2/3` connector tiles over the full open `(A,B)` coefficient cell. -/
theorem coefficient_ball_full_cubic_axis {A B : ℂ} (c : ℝ)
    (hA : ‖A - endpointA‖ ≤ 1 / 10000)
    (hB : ‖B - endpointB‖ ≤ 1 / 10000) :
    ((∀ u : ℝ, 0 ≤ u → u ≤ 1 → mixedCubicModel A B c (chordPoint u) < 0) ∧
      (∀ t : ℝ, 2 / 3 ≤ t → t ≤ 1 → mixedCubicModel A B c (rayZeroPoint t) ≤ 0) ∧
      (∀ t : ℝ, 2 / 3 ≤ t → t ≤ 1 → mixedCubicModel A B c (rayOnePoint t) < 0)) ∨
    ((∀ u : ℝ, 0 ≤ u → u ≤ 1 → mixedCubicModel A B c (reflectedChordPoint u) < 0) ∧
      (∀ t : ℝ, 2 / 3 ≤ t → t ≤ 1 → mixedCubicModel A B c (rayFivePoint t) < 0) ∧
      (∀ t : ℝ, 2 / 3 ≤ t → t ≤ 1 → mixedCubicModel A B c (rayZeroPoint t) ≤ 0)) := by
  by_cases hc : -(1 : ℝ) / 10000 ≤ c
  · left
    exact coefficient_ball_cubic_halfline_connector hA hB hc
  · right
    exact reflected_coefficient_ball_connector hA hB (by nlinarith)

end

end ErdosProblems.Erdos1041.SexticMixedFullCubicAxis
