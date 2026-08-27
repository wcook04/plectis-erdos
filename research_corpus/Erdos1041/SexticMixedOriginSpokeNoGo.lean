import ErdosProblems.Erdos1041.SexticFirstModeDominantTangentCone
import ErdosProblems.Erdos1041.SexticCanonicalMixedSlice
import Mathlib.Tactic

/-!
# Erdős #1041: a genuinely mixed obstruction to complete origin spokes

For one explicit first/second-mode phase pair and every ratio
`0 ≤ λ ≤ 1/4`, four of the six complete sixth-root rays escape the
nonpositive paired tangent model.  The only two rays not certified to escape
are antipodal.  Hence no adjacent or gap-two pair of complete origin spokes
can provide the strict short connector; truncated spokes are necessary.

At the endpoint `λ = 1/4` the obstruction is also resolved constructively:
directions zero and one are safe from radius `2/3` outwards, and their joining
chord has a strict degree-six Bernstein certificate.  Thus truncation is both
necessary and sufficient for this explicit genuinely mixed configuration.
-/

namespace ErdosProblems.Erdos1041.SexticMixedOriginSpokeNoGo

open ErdosProblems.Erdos1041.SexticFirstModeDominantTangentCone
open ErdosProblems.Erdos1041.SexticCanonicalMixedSlice

noncomputable section

abbrev sqrtTwo : ℝ := Real.sqrt 2

theorem sqrtTwo_nonneg : 0 ≤ sqrtTwo := Real.sqrt_nonneg 2

theorem sqrtTwo_sq : sqrtTwo ^ 2 = 2 := by
  norm_num [sqrtTwo]

theorem sqrtTwo_gt_one : 1 < sqrtTwo := by
  have hs := sqrtTwo_sq
  have hn := sqrtTwo_nonneg
  nlinarith

theorem sqrtTwo_gt_sevenFifths : 7 / 5 < sqrtTwo := by
  have hs := sqrtTwo_sq
  have hn := sqrtTwo_nonneg
  nlinarith

theorem sqrtThree_lt_sevenFourths : sqrtThree < 7 / 4 := by
  have hs := sqrtThree_sq
  have hn : 0 ≤ sqrtThree := le_of_lt sqrtThree_pos
  nlinarith

theorem sqrtThree_gt_threeHalves : 3 / 2 < sqrtThree := by
  have hs := sqrtThree_sq
  have hn : 0 ≤ sqrtThree := le_of_lt sqrtThree_pos
  nlinarith

theorem sqrtTwo_lt_threeHalves : sqrtTwo < 3 / 2 := by
  have hs := sqrtTwo_sq
  have hn := sqrtTwo_nonneg
  nlinarith

theorem sqrtThree_gt_fiveThirds : 5 / 3 < sqrtThree := by
  have hs := sqrtThree_sq
  have hn : 0 ≤ sqrtThree := le_of_lt sqrtThree_pos
  nlinarith

def RaySafe (a b : ℝ) : Prop :=
  ∀ t : ℝ, 0 ≤ t → t ≤ 1 → pairedTangentRay a b t ≤ 0

def aNeg (lam : ℝ) : ℝ := -sqrtThree * lam / 2
def aZero : ℝ := 0
def aPos (lam : ℝ) : ℝ := sqrtThree * lam / 2

def bNeg : ℝ := -sqrtTwo * (sqrtThree + 1) / 4
def bHigh : ℝ := sqrtTwo / 2
def bLow : ℝ := sqrtTwo * (sqrtThree - 1) / 4

/-- Direction one escapes at the chord-search calibration point `t=1/2`. -/
theorem rayOne_half_pos {lam : ℝ} (hlam4 : lam ≤ 1 / 4) :
    0 < pairedTangentRay (aNeg lam) bHigh (1 / 2) := by
  have hs3 : 0 < sqrtThree := sqrtThree_pos
  have hmul := mul_le_mul_of_nonneg_left hlam4 (le_of_lt hs3)
  have hconst : 0 < 24 * sqrtTwo - 15 * sqrtThree - 4 := by
    have hs2 := sqrtTwo_gt_sevenFifths
    have hs3u := sqrtThree_lt_sevenFourths
    nlinarith
  unfold pairedTangentRay aNeg bHigh
  norm_num
  nlinarith

/-- A zero first-mode projection with the small positive second-mode
projection escapes already at `t=1/4`. -/
theorem zeroLow_quarter_pos :
    0 < pairedTangentRay aZero bLow (1 / 4) := by
  have hs2 : 1 < sqrtTwo := sqrtTwo_gt_one
  have hs3 : 1 / 2 < sqrtThree - 1 := by
    nlinarith [sqrtThree_gt_threeHalves]
  have htail : 0 ≤ sqrtThree - 1 := le_of_lt (by linarith)
  have hprod : 1 / 2 < sqrtTwo * (sqrtThree - 1) := by
    calc
      1 / 2 < 1 * (sqrtThree - 1) := by simpa using hs3
      _ ≤ sqrtTwo * (sqrtThree - 1) :=
        mul_le_mul_of_nonneg_right (le_of_lt hs2) htail
  unfold pairedTangentRay aZero bLow
  norm_num
  nlinarith

/-- Direction four escapes at `t=1/2`; its first-mode contribution is
nonnegative, so the positive second mode alone suffices. -/
theorem rayFour_half_pos {lam : ℝ} (hlam0 : 0 ≤ lam) :
    0 < pairedTangentRay (aPos lam) bHigh (1 / 2) := by
  have hs2 : 1 < sqrtTwo := sqrtTwo_gt_one
  have hs3 : 0 < sqrtThree := sqrtThree_pos
  have hmul : 0 ≤ sqrtThree * lam := mul_nonneg (le_of_lt hs3) hlam0
  unfold pairedTangentRay aPos bHigh
  norm_num
  nlinarith

theorem not_rayOne_safe {lam : ℝ} (hlam4 : lam ≤ 1 / 4) :
    ¬ RaySafe (aNeg lam) bHigh := by
  intro h
  have := h (1 / 2) (by norm_num) (by norm_num)
  linarith [rayOne_half_pos hlam4]

theorem not_zeroLow_safe : ¬ RaySafe aZero bLow := by
  intro h
  have := h (1 / 4) (by norm_num) (by norm_num)
  linarith [zeroLow_quarter_pos]

theorem not_rayFour_safe {lam : ℝ} (hlam0 : 0 ≤ lam) :
    ¬ RaySafe (aPos lam) bHigh := by
  intro h
  have := h (1 / 2) (by norm_num) (by norm_num)
  linarith [rayFour_half_pos hlam0]

/-- In the explicit phase table

`a = (-,-,0,+,+,0)` and `b = (bNeg,bHigh,bLow,bNeg,bHigh,bLow)`.

Every adjacent or gap-two pair contains one of directions `1,2,4,5`, each
of which escapes. -/
theorem no_adjacent_or_gapTwo_safe_pair
    {lam : ℝ} (hlam0 : 0 ≤ lam) (hlam4 : lam ≤ 1 / 4) :
    ¬ (
      (RaySafe (aNeg lam) bNeg ∧ RaySafe (aNeg lam) bHigh) ∨
      (RaySafe (aNeg lam) bHigh ∧ RaySafe aZero bLow) ∨
      (RaySafe aZero bLow ∧ RaySafe (aPos lam) bNeg) ∨
      (RaySafe (aPos lam) bNeg ∧ RaySafe (aPos lam) bHigh) ∨
      (RaySafe (aPos lam) bHigh ∧ RaySafe aZero bLow) ∨
      (RaySafe aZero bLow ∧ RaySafe (aNeg lam) bNeg) ∨
      (RaySafe (aNeg lam) bNeg ∧ RaySafe aZero bLow) ∨
      (RaySafe (aNeg lam) bHigh ∧ RaySafe (aPos lam) bNeg) ∨
      (RaySafe aZero bLow ∧ RaySafe (aPos lam) bHigh) ∨
      (RaySafe (aPos lam) bNeg ∧ RaySafe aZero bLow) ∨
      (RaySafe (aPos lam) bHigh ∧ RaySafe (aNeg lam) bNeg) ∨
      (RaySafe aZero bLow ∧ RaySafe (aNeg lam) bHigh)) := by
  have h1 := not_rayOne_safe hlam4
  have h2 := not_zeroLow_safe
  have h4 := not_rayFour_safe hlam0
  tauto

/-! ## The positive-radius repair at the endpoint ratio -/

/-- The power-basis value of the paired tangent model on the radius `2/3`
chord from direction zero to direction one.  The expression is the exact real
part after substituting the two phases displayed in the module docstring. -/
def endpointChordPower (u : ℝ) : ℝ :=
  -(256 * u ^ 6 - 768 * u ^ 5 - 1920 * u ^ 4 - 144 * sqrtTwo * u ^ 4 +
      144 * (sqrtTwo * sqrtThree) * u ^ 4 + 240 * sqrtThree * u ^ 4 -
      576 * (sqrtTwo * sqrtThree) * u ^ 3 - 480 * sqrtThree * u ^ 3 -
      576 * sqrtTwo * u ^ 3 + 5120 * u ^ 3 - 1920 * u ^ 2 -
      324 * (sqrtTwo * sqrtThree) * u ^ 2 + 2052 * sqrtTwo * u ^ 2 -
      1872 * sqrtTwo * u - 768 * u + 240 * sqrtThree * u +
      576 * (sqrtTwo * sqrtThree) * u + 180 * sqrtTwo + 256 +
      195 * sqrtThree + 180 * (sqrtTwo * sqrtThree)) / 2916

def chordC0 : ℝ :=
  -(180 * sqrtTwo + 256 + 195 * sqrtThree +
      180 * (sqrtTwo * sqrtThree)) / 2916
def chordC1 : ℝ :=
  (-276 * (sqrtTwo * sqrtThree) - 235 * sqrtThree - 128 +
      132 * sqrtTwo) / 2916
def chordC2 : ℝ :=
  (-1752 * (sqrtTwo * sqrtThree) - 1375 * sqrtThree + 640 +
      1536 * sqrtTwo) / 14580
def chordC3 : ℝ :=
  (-1872 * (sqrtTwo * sqrtThree) - 1455 * sqrtThree + 1280 +
      1872 * sqrtTwo) / 14580
def chordC4 : ℝ :=
  (-1644 * (sqrtTwo * sqrtThree) - 1375 * sqrtThree + 640 +
      1860 * sqrtTwo) / 14580
def chordC5 : ℝ :=
  (-204 * (sqrtTwo * sqrtThree) - 235 * sqrtThree - 128 +
      348 * sqrtTwo) / 2916
def chordC6 : ℝ :=
  (-195 * sqrtThree - 256 + 360 * sqrtTwo) / 2916

def endpointChordBernstein (u : ℝ) : ℝ :=
    chordC0 * (1 - u) ^ 6
  + chordC1 * (6 * u * (1 - u) ^ 5)
  + chordC2 * (15 * u ^ 2 * (1 - u) ^ 4)
  + chordC3 * (20 * u ^ 3 * (1 - u) ^ 3)
  + chordC4 * (15 * u ^ 4 * (1 - u) ^ 2)
  + chordC5 * (6 * u ^ 5 * (1 - u))
  + chordC6 * u ^ 6

theorem endpointChordPower_eq_bernstein (u : ℝ) :
    endpointChordPower u = endpointChordBernstein u := by
  unfold endpointChordPower endpointChordBernstein chordC0 chordC1 chordC2
    chordC3 chordC4 chordC5 chordC6
  ring

theorem bernsteinSix_partition (u : ℝ) :
    (1 - u) ^ 6 + 6 * u * (1 - u) ^ 5 +
      15 * u ^ 2 * (1 - u) ^ 4 + 20 * u ^ 3 * (1 - u) ^ 3 +
      15 * u ^ 4 * (1 - u) ^ 2 + 6 * u ^ 5 * (1 - u) + u ^ 6 = 1 := by
  ring

/-- Every exact Bernstein control is bounded above by `-1/1000`. -/
theorem chord_coefficients_uniformly_negative :
    chordC0 ≤ -(1 : ℝ) / 1000 ∧ chordC1 ≤ -(1 : ℝ) / 1000 ∧
    chordC2 ≤ -(1 : ℝ) / 1000 ∧ chordC3 ≤ -(1 : ℝ) / 1000 ∧
    chordC4 ≤ -(1 : ℝ) / 1000 ∧ chordC5 ≤ -(1 : ℝ) / 1000 ∧
    chordC6 ≤ -(1 : ℝ) / 1000 := by
  have hs2l := sqrtTwo_gt_sevenFifths
  have hs2u := sqrtTwo_lt_threeHalves
  have hs3l := sqrtThree_gt_fiveThirds
  have hs6l : 7 / 3 < sqrtTwo * sqrtThree := by
    have h1 : (7 / 5 : ℝ) * sqrtThree < sqrtTwo * sqrtThree :=
      mul_lt_mul_of_pos_right hs2l sqrtThree_pos
    have h2 : (7 / 3 : ℝ) < (7 / 5 : ℝ) * sqrtThree := by
      nlinarith
    linarith
  unfold chordC0 chordC1 chordC2 chordC3 chordC4 chordC5 chordC6
  constructor
  · nlinarith [sqrtTwo_nonneg, le_of_lt sqrtThree_pos]
  constructor
  · nlinarith
  constructor
  · nlinarith
  constructor
  · nlinarith
  constructor
  · nlinarith
  constructor <;> nlinarith

/-- The radius `2/3` joining chord is uniformly, strictly negative. -/
theorem endpointChordPower_le {u : ℝ} (hu0 : 0 ≤ u) (hu1 : u ≤ 1) :
    endpointChordPower u ≤ -(1 : ℝ) / 1000 := by
  have homu : 0 ≤ 1 - u := sub_nonneg.mpr hu1
  rcases chord_coefficients_uniformly_negative with
    ⟨hc0, hc1, hc2, hc3, hc4, hc5, hc6⟩
  have h0 := mul_le_mul_of_nonneg_right hc0 (by positivity : 0 ≤ (1 - u) ^ 6)
  have h1 := mul_le_mul_of_nonneg_right hc1
    (by positivity : 0 ≤ 6 * u * (1 - u) ^ 5)
  have h2 := mul_le_mul_of_nonneg_right hc2
    (by positivity : 0 ≤ 15 * u ^ 2 * (1 - u) ^ 4)
  have h3 := mul_le_mul_of_nonneg_right hc3
    (by positivity : 0 ≤ 20 * u ^ 3 * (1 - u) ^ 3)
  have h4 := mul_le_mul_of_nonneg_right hc4
    (by positivity : 0 ≤ 15 * u ^ 4 * (1 - u) ^ 2)
  have h5 := mul_le_mul_of_nonneg_right hc5
    (by positivity : 0 ≤ 6 * u ^ 5 * (1 - u))
  have h6 := mul_le_mul_of_nonneg_right hc6 (by positivity : 0 ≤ u ^ 6)
  have hsum := bernsteinSix_partition u
  rw [endpointChordPower_eq_bernstein]
  unfold endpointChordBernstein
  nlinarith

def rayOneBarrier (t : ℝ) : ℝ :=
  24 * t ^ 5 - 5 * t ^ 4 + 18 * t ^ 3 - 18 * t + 5

theorem rayOneBarrier_identity (t : ℝ) :
    81 * rayOneBarrier t =
      8 * (3 * t - 2) ^ 5 + 75 * (3 * t - 2) ^ 4 +
      334 * (3 * t - 2) ^ 3 + 844 * (3 * t - 2) ^ 2 +
      642 * (3 * t - 2) + 41 := by
  unfold rayOneBarrier
  ring

theorem rayOneBarrier_pos {t : ℝ} (ht : 2 / 3 ≤ t) :
    0 < rayOneBarrier t := by
  have hu : 0 ≤ 3 * t - 2 := by nlinarith
  have hp : 0 < 8 * (3 * t - 2) ^ 5 + 75 * (3 * t - 2) ^ 4 +
      334 * (3 * t - 2) ^ 3 + 844 * (3 * t - 2) ^ 2 +
      642 * (3 * t - 2) + 41 := by positivity
  rw [← rayOneBarrier_identity] at hp
  nlinarith

/-- Direction zero is safe on the complete unit ray, hence on the truncated
tail beginning at `2/3`. -/
theorem rayZero_nonpos {t : ℝ} (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    pairedTangentRay (aNeg (1 / 4)) bNeg t ≤ 0 := by
  have ht2 : t ^ 2 ≤ 1 := pow_le_one₀ ht0 ht1
  have ht4 : t ^ 4 ≤ 1 := pow_le_one₀ ht0 ht1
  have hp : 0 ≤ t - t ^ 5 := by
    have : t - t ^ 5 = t * (1 - t ^ 4) := by ring
    rw [this]
    exact mul_nonneg ht0 (sub_nonneg.mpr ht4)
  have hq : 0 ≤ t ^ 2 - t ^ 4 := by
    have : t ^ 2 - t ^ 4 = t ^ 2 * (1 - t ^ 2) := by ring
    rw [this]
    exact mul_nonneg (sq_nonneg t) (sub_nonneg.mpr ht2)
  have ha : aNeg (1 / 4) ≤ 0 := by
    unfold aNeg
    nlinarith [sqrtThree_pos]
  have hb : bNeg ≤ 0 := by
    unfold bNeg
    have hs2 : 0 ≤ sqrtTwo := sqrtTwo_nonneg
    have hs3 : 0 ≤ sqrtThree + 1 := by nlinarith [sqrtThree_pos]
    have hprod : 0 ≤ sqrtTwo * (sqrtThree + 1) := mul_nonneg hs2 hs3
    nlinarith
  have hpa : (t - t ^ 5) * aNeg (1 / 4) ≤ 0 :=
    mul_nonpos_of_nonneg_of_nonpos hp ha
  have hqb : (t ^ 2 - t ^ 4) * bNeg ≤ 0 :=
    mul_nonpos_of_nonneg_of_nonpos hq hb
  have ht6 : 0 ≤ t ^ 6 := by positivity
  unfold pairedTangentRay
  linarith

/-- Direction one becomes safe exactly after the rational cutoff used by the
joining chord. -/
theorem rayOne_tail_nonpos {t : ℝ} (ht : 2 / 3 ≤ t) (ht1 : t ≤ 1) :
    pairedTangentRay (aNeg (1 / 4)) bHigh t < 0 := by
  have ht0 : 0 ≤ t := by nlinarith
  have ht2 : t ^ 2 ≤ 1 := pow_le_one₀ ht0 ht1
  have ht4 : t ^ 4 ≤ 1 := pow_le_one₀ ht0 ht1
  have hp : 0 ≤ t - t ^ 5 := by
    have : t - t ^ 5 = t * (1 - t ^ 4) := by ring
    rw [this]
    exact mul_nonneg ht0 (sub_nonneg.mpr ht4)
  have hq : 0 ≤ t ^ 2 - t ^ 4 := by
    have : t ^ 2 - t ^ 4 = t ^ 2 * (1 - t ^ 2) := by ring
    rw [this]
    exact mul_nonneg (sq_nonneg t) (sub_nonneg.mpr ht2)
  have ha : aNeg (1 / 4) ≤ -(5 : ℝ) / 24 := by
    unfold aNeg
    nlinarith [sqrtThree_gt_fiveThirds]
  have hb : bHigh ≤ (3 : ℝ) / 4 := by
    unfold bHigh
    nlinarith [sqrtTwo_lt_threeHalves]
  have hpa := mul_le_mul_of_nonneg_left ha hp
  have hqb := mul_le_mul_of_nonneg_left hb hq
  have hbound : pairedTangentRay (aNeg (1 / 4)) bHigh t ≤
      -(5 : ℝ) / 24 * (t - t ^ 5) +
        (3 : ℝ) / 4 * (t ^ 2 - t ^ 4) - t ^ 6 := by
    unfold pairedTangentRay
    nlinarith
  have hid : -(5 : ℝ) / 24 * (t - t ^ 5) +
        (3 : ℝ) / 4 * (t ^ 2 - t ^ 4) - t ^ 6 =
      -t * rayOneBarrier t / 24 := by
    unfold rayOneBarrier
    ring
  have hbar := rayOneBarrier_pos ht
  have htpos : 0 < t := by nlinarith
  rw [hid] at hbound
  have hprod : 0 < t * rayOneBarrier t := mul_pos htpos hbar
  have hneg : -t * rayOneBarrier t / 24 < 0 := by nlinarith
  exact hbound.trans_lt hneg

/-- Exact scalar connector for the mixed endpoint: the chord is strictly
negative and both radial tails are nonpositive from radius `2/3`. -/
theorem endpoint_truncated_connector :
    (∀ u : ℝ, 0 ≤ u → u ≤ 1 → endpointChordPower u < 0) ∧
    (∀ t : ℝ, 2 / 3 ≤ t → t ≤ 1 →
      pairedTangentRay (aNeg (1 / 4)) bNeg t ≤ 0) ∧
    (∀ t : ℝ, 2 / 3 ≤ t → t ≤ 1 →
      pairedTangentRay (aNeg (1 / 4)) bHigh t ≤ 0) := by
  refine ⟨?_, ?_, ?_⟩
  · intro u hu0 hu1
    exact (endpointChordPower_le hu0 hu1).trans_lt (by norm_num)
  · intro t ht ht1
    exact rayZero_nonpos (by nlinarith) ht1
  · intro t ht ht1
    exact le_of_lt (rayOne_tail_nonpos ht ht1)

end

end ErdosProblems.Erdos1041.SexticMixedOriginSpokeNoGo
