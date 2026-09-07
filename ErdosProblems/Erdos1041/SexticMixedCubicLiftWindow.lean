import ErdosProblems.Erdos1041.SexticMixedTruncatedNeighborhood
import ErdosProblems.Erdos1041.SexticSecondModeCubicLift
import Mathlib.Tactic

/-!
# Erdős #1041: the one-sided cubic lift of a mixed connector cell

The mixed coefficient ball does not lift through an arbitrary tangent cubic:
the first mode breaks the even antipodal symmetry.  It does, however, lift
through an explicit half-line of cubic coefficients because the cubic has one
fixed sign on the selected chord and vanishes on both sixth-root rays.
-/

namespace ErdosProblems.Erdos1041.SexticMixedCubicLiftWindow

open ErdosProblems.Erdos1041.SexticCanonicalMixedSlice
open ErdosProblems.Erdos1041.SexticMixedOriginSpokeNoGo
open ErdosProblems.Erdos1041.SexticMixedTruncatedNeighborhood
open ErdosProblems.Erdos1041.SexticSecondModeCubicLift

noncomputable section

def mixedCubicModel (A B : ℂ) (c : ℝ) (z : ℂ) : ℝ :=
  pairedTangentComplex A B z + tangentCubic c z

theorem chordPoint_eq_adjacentPoint (u : ℝ) :
    chordPoint u = adjacentPoint (2 / 3) u := by
  apply Complex.ext
  · simp [chordPoint, adjacentPoint]
  · simp [chordPoint, adjacentPoint]
    ring

/-- The cubic shape on the selected chord is nonnegative before multiplication
by `-c`, and is bounded by one. -/
theorem chord_cube_im_mem_unit {u : ℝ} (hu0 : 0 ≤ u) (hu1 : u ≤ 1) :
    0 ≤ (chordPoint u ^ 3).im ∧ (chordPoint u ^ 3).im ≤ 1 := by
  rw [chordPoint_eq_adjacentPoint, adjacentPoint_cube_im]
  have hs0 : 0 ≤ sqrtThree := le_of_lt sqrtThree_pos
  have hsUpper := sqrtThree_lt_sevenFourths
  have htail : 0 ≤ 1 - u := sub_nonneg.mpr hu1
  have hprod0 : 0 ≤ u * (1 - u) := mul_nonneg hu0 htail
  have hprod4 : u * (1 - u) ≤ 1 / 4 := by
    nlinarith [sq_nonneg (u - 1 / 2)]
  constructor
  · positivity
  · have hcoef : 0 ≤ (4 * sqrtThree / 9 : ℝ) := by positivity
    have hmul := mul_le_mul hprod4 (le_of_lt hsUpper) hs0 (by norm_num : (0 : ℝ) ≤ 1 / 4)
    nlinarith

theorem tangentCubic_chord_le {c u : ℝ} (hc : -(1 : ℝ) / 10000 ≤ c)
    (hu0 : 0 ≤ u) (hu1 : u ≤ 1) :
    tangentCubic c (chordPoint u) ≤ 1 / 10000 := by
  rcases chord_cube_im_mem_unit hu0 hu1 with ⟨him0, him1⟩
  rw [tangentCubic_eq_neg_mul_im]
  have hcneg : -c ≤ (1 : ℝ) / 10000 := by nlinarith
  have hfirst := mul_le_mul_of_nonneg_right hcneg him0
  have hsecond : (1 : ℝ) / 10000 * (chordPoint u ^ 3).im ≤ 1 / 10000 := by
    nlinarith
  linarith

/-- Quantitative version of the coefficient-ball chord theorem. -/
theorem coefficient_ball_chord_le {A B : ℂ}
    (hA : ‖A - endpointA‖ ≤ 1 / 10000)
    (hB : ‖B - endpointB‖ ≤ 1 / 10000)
    {u : ℝ} (hu0 : 0 ≤ u) (hu1 : u ≤ 1) :
    pairedTangentComplex A B (chordPoint u) ≤ -(3 : ℝ) / 5000 := by
  let dA := A - endpointA
  let dB := B - endpointB
  have hAid : endpointA + dA = A := by dsimp [dA]; ring
  have hBid : endpointB + dB = B := by dsimp [dB]; ring
  have herr := tangentError_re_abs_le (by norm_num : (0 : ℝ) ≤ 1 / 10000)
    hA hB (chordPoint_norm_le_one hu0 hu1)
  have herrUp : (tangentError dA dB (chordPoint u)).re ≤ 4 / 10000 := by
    nlinarith [le_abs_self (tangentError dA dB (chordPoint u)).re]
  rw [← hAid, ← hBid, pairedTangentComplex_add, endpoint_chord_identity]
  have hbase := endpointChordPower_le hu0 hu1
  nlinarith

theorem rayZero_cube_im_zero (t : ℝ) : (rayZeroPoint t ^ 3).im = 0 := by
  simp [rayZeroPoint, pow_succ, Complex.mul_re, Complex.mul_im]

theorem rayOne_cube_im_zero (t : ℝ) : (rayOnePoint t ^ 3).im = 0 := by
  have hs2 := sqrtThree_sq
  have hs3 : sqrtThree ^ 3 = 3 * sqrtThree := by
    calc sqrtThree ^ 3 = sqrtThree ^ 2 * sqrtThree := by ring
         _ = 3 * sqrtThree := by rw [hs2]
  simp [rayOnePoint, omega, pow_succ, Complex.mul_re, Complex.mul_im]
  ring_nf
  rw [hs3]
  ring

theorem tangentCubic_rayZero_zero (c t : ℝ) :
    tangentCubic c (rayZeroPoint t) = 0 :=
  tangentCubic_eq_zero_of_cube_im_zero (rayZero_cube_im_zero t)

theorem tangentCubic_rayOne_zero (c t : ℝ) :
    tangentCubic c (rayOnePoint t) = 0 :=
  tangentCubic_eq_zero_of_cube_im_zero (rayOne_cube_im_zero t)

/-- The first open mixed cell lifts through the complete cubic half-line
`c ≥ -10^-4`, with the same pair and radius. -/
theorem coefficient_ball_cubic_halfline_connector {A B : ℂ} {c : ℝ}
    (hA : ‖A - endpointA‖ ≤ 1 / 10000)
    (hB : ‖B - endpointB‖ ≤ 1 / 10000)
    (hc : -(1 : ℝ) / 10000 ≤ c) :
    (∀ u : ℝ, 0 ≤ u → u ≤ 1 →
      mixedCubicModel A B c (chordPoint u) < 0) ∧
    (∀ t : ℝ, 2 / 3 ≤ t → t ≤ 1 →
      mixedCubicModel A B c (rayZeroPoint t) ≤ 0) ∧
    (∀ t : ℝ, 2 / 3 ≤ t → t ≤ 1 →
      mixedCubicModel A B c (rayOnePoint t) < 0) := by
  rcases coefficient_ball_connector hA hB with ⟨_hchord, hr0, hr1⟩
  refine ⟨?_, ?_, ?_⟩
  · intro u hu0 hu1
    have hbase := coefficient_ball_chord_le hA hB hu0 hu1
    have hcubic := tangentCubic_chord_le hc hu0 hu1
    unfold mixedCubicModel
    nlinarith
  · intro t ht ht1
    rw [mixedCubicModel, tangentCubic_rayZero_zero, add_zero]
    exact hr0 t ht ht1
  · intro t ht ht1
    rw [mixedCubicModel, tangentCubic_rayOne_zero, add_zero]
    exact hr1 t ht ht1

/-! ## Why the cubic half-line cannot be replaced by all cubic coefficients -/

theorem negativeTwo_midpoint_value :
    mixedCubicModel endpointA endpointB (-2) (chordPoint (1 / 2)) =
      (-6 * (sqrtTwo * sqrtThree) + 2 + 6 * sqrtTwo + 7 * sqrtThree) / 54 := by
  unfold mixedCubicModel
  rw [endpoint_chord_identity, tangentCubic_eq_neg_mul_im,
    chordPoint_eq_adjacentPoint, adjacentPoint_cube_im]
  unfold endpointChordPower
  norm_num
  ring

theorem negativeTwo_midpoint_pos :
    0 < mixedCubicModel endpointA endpointB (-2) (chordPoint (1 / 2)) := by
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
  rw [negativeTwo_midpoint_value]
  nlinarith

theorem negativeTwo_antipodal_endpoint_value :
    mixedCubicModel endpointA endpointB (-2) (-chordPoint 1) =
      (-256 + 195 * sqrtThree + 360 * sqrtTwo) / 2916 := by
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
  simp [mixedCubicModel, pairedTangentComplex, tangentCubic, endpointA,
    endpointB, chordPoint, Complex.mul_re, Complex.mul_im,
    Complex.conj_re, Complex.conj_im, pow_succ]
  ring_nf
  rw [hs6, hs5, hs4, hs3, hs2]
  ring

theorem negativeTwo_antipodal_endpoint_pos :
    0 < mixedCubicModel endpointA endpointB (-2) (-chordPoint 1) := by
  have hs2 := sqrtTwo_gt_sevenFifths
  have hs3 := sqrtThree_gt_fiveThirds
  rw [negativeTwo_antipodal_endpoint_value]
  nlinarith

/-- At `c=-2` the selected chord fails at its midpoint, while its antipodal
copy fails at an endpoint where the cubic vanishes.  Hence arbitrary cubic
lifting by antipodal choice is impossible for this genuinely mixed cell. -/
theorem arbitrary_antipodal_cubic_lift_no_go :
    0 < mixedCubicModel endpointA endpointB (-2) (chordPoint (1 / 2)) ∧
    0 < mixedCubicModel endpointA endpointB (-2) (-chordPoint 1) :=
  ⟨negativeTwo_midpoint_pos, negativeTwo_antipodal_endpoint_pos⟩

end

end ErdosProblems.Erdos1041.SexticMixedCubicLiftWindow
