import ErdosProblems.Erdos1041.SexticMixedOriginSpokeNoGo
import Mathlib.Tactic

/-!
# Erdős #1041: a quantitative neighborhood of a mixed sextic connector

This module thickens the explicit radius-`2/3` mixed connector.  The tangent
model is written with its two complex low-mode coefficients, so the final
theorem is an actual coefficient ball rather than an abstract error lemma.
-/

namespace ErdosProblems.Erdos1041.SexticMixedTruncatedNeighborhood

open ErdosProblems.Erdos1041.SexticCanonicalMixedSlice
open ErdosProblems.Erdos1041.SexticMixedOriginSpokeNoGo
open ErdosProblems.Erdos1041.SexticFirstModeDominantTangentCone

noncomputable section

def pairedTangentComplex (A B z : ℂ) : ℝ :=
  (A * z + B * z ^ 2 - (starRingEnd ℂ) B * z ^ 4 -
    (starRingEnd ℂ) A * z ^ 5 - z ^ 6).re

def endpointA : ℂ :=
  ⟨-sqrtThree / 8, 1 / 8⟩

def endpointB : ℂ :=
  ⟨-(sqrtTwo * sqrtThree + sqrtTwo) / 4,
    (sqrtTwo - sqrtTwo * sqrtThree) / 4⟩

def omega : ℂ := ⟨1 / 2, sqrtThree / 2⟩

def chordPoint (u : ℝ) : ℂ :=
  ⟨(2 / 3) * (1 - u / 2), u * sqrtThree / 3⟩

/-- Direct substitution connects the complex coefficient model to the exact
Bernstein-certified real chord polynomial. -/
theorem endpoint_chord_identity (u : ℝ) :
    pairedTangentComplex endpointA endpointB (chordPoint u) =
      endpointChordPower u := by
  have hs3 := sqrtThree_sq
  simp [pairedTangentComplex, endpointA, endpointB, chordPoint,
    Complex.mul_re, Complex.mul_im, Complex.conj_re, Complex.conj_im,
    pow_succ, endpointChordPower]
  ring_nf at hs3 ⊢
  linear_combination
    (u / 2916 *
      (4 * u ^ 5 * sqrtThree ^ 4 - 48 * u ^ 5 * sqrtThree ^ 2 -
       84 * u ^ 5 - 9 * u ^ 4 * sqrtThree ^ 3 +
       240 * u ^ 4 * sqrtThree ^ 2 + 3 * u ^ 4 * sqrtThree +
       240 * u ^ 4 + 9 * u ^ 3 * sqrtTwo * sqrtThree ^ 3 +
       45 * u ^ 3 * sqrtTwo * sqrtThree ^ 2 -
       63 * u ^ 3 * sqrtTwo * sqrtThree + 45 * u ^ 3 * sqrtTwo +
       15 * u ^ 3 * sqrtThree ^ 3 - 240 * u ^ 3 * sqrtThree ^ 2 -
       105 * u ^ 3 * sqrtThree + 720 * u ^ 3 -
       72 * u ^ 2 * sqrtTwo * sqrtThree ^ 2 +
       288 * u ^ 2 * sqrtTwo * sqrtThree + 216 * u ^ 2 * sqrtTwo +
       240 * u ^ 2 * sqrtThree - 1920 * u ^ 2 -
       135 * u * sqrtTwo * sqrtThree - 729 * u * sqrtTwo -
       120 * u * sqrtThree + 960 * u + 612 * sqrtTwo)) * hs3

def tangentError (dA dB z : ℂ) : ℂ :=
  dA * z + dB * z ^ 2 - (starRingEnd ℂ) dB * z ^ 4 -
    (starRingEnd ℂ) dA * z ^ 5

theorem pairedTangentComplex_add (A B dA dB z : ℂ) :
    pairedTangentComplex (A + dA) (B + dB) z =
      pairedTangentComplex A B z + (tangentError dA dB z).re := by
  unfold pairedTangentComplex tangentError
  simp only [map_add]
  rw [← Complex.add_re]
  congr 1
  ring

/-- On the closed unit disk, changing each low-mode coefficient by at most
`eps` changes the paired tangent value by at most `4 eps`. -/
theorem tangentError_norm_le {eps : ℝ} (heps : 0 ≤ eps)
    {dA dB z : ℂ} (hA : ‖dA‖ ≤ eps) (hB : ‖dB‖ ≤ eps)
    (hz : ‖z‖ ≤ 1) :
    ‖tangentError dA dB z‖ ≤ 4 * eps := by
  have hz0 : 0 ≤ ‖z‖ := norm_nonneg z
  have hz2 : ‖z‖ ^ 2 ≤ 1 := pow_le_one₀ hz0 hz
  have hz4 : ‖z‖ ^ 4 ≤ 1 := pow_le_one₀ hz0 hz
  have hz5 : ‖z‖ ^ 5 ≤ 1 := pow_le_one₀ hz0 hz
  calc
    ‖tangentError dA dB z‖
        ≤ ‖dA * z + dB * z ^ 2 - (starRingEnd ℂ) dB * z ^ 4‖ +
            ‖(starRingEnd ℂ) dA * z ^ 5‖ := by
          unfold tangentError
          exact norm_sub_le _ _
    _ ≤ (‖dA * z + dB * z ^ 2‖ + ‖(starRingEnd ℂ) dB * z ^ 4‖) +
            ‖(starRingEnd ℂ) dA * z ^ 5‖ := by
          exact add_le_add (norm_sub_le _ _) (le_refl _)
    _ ≤ ((‖dA * z‖ + ‖dB * z ^ 2‖) +
            ‖(starRingEnd ℂ) dB * z ^ 4‖) +
            ‖(starRingEnd ℂ) dA * z ^ 5‖ := by
          gcongr
          exact norm_add_le _ _
    _ = ((‖dA‖ * ‖z‖ + ‖dB‖ * ‖z‖ ^ 2) +
            ‖dB‖ * ‖z‖ ^ 4) + ‖dA‖ * ‖z‖ ^ 5 := by
          simp [norm_pow]
    _ ≤ 4 * eps := by
          have hAz : ‖dA‖ * ‖z‖ ≤ eps := by
            calc ‖dA‖ * ‖z‖ ≤ eps * 1 :=
                  mul_le_mul hA hz (norm_nonneg _) heps
                 _ = eps := by ring
          have hBz2 : ‖dB‖ * ‖z‖ ^ 2 ≤ eps := by
            calc ‖dB‖ * ‖z‖ ^ 2 ≤ eps * 1 :=
                  mul_le_mul hB hz2 (by positivity) heps
                 _ = eps := by ring
          have hBz4 : ‖dB‖ * ‖z‖ ^ 4 ≤ eps := by
            calc ‖dB‖ * ‖z‖ ^ 4 ≤ eps * 1 :=
                  mul_le_mul hB hz4 (by positivity) heps
                 _ = eps := by ring
          have hAz5 : ‖dA‖ * ‖z‖ ^ 5 ≤ eps := by
            calc ‖dA‖ * ‖z‖ ^ 5 ≤ eps * 1 :=
                  mul_le_mul hA hz5 (by positivity) heps
                 _ = eps := by ring
          linarith

theorem tangentError_re_abs_le {eps : ℝ} (heps : 0 ≤ eps)
    {dA dB z : ℂ} (hA : ‖dA‖ ≤ eps) (hB : ‖dB‖ ≤ eps)
    (hz : ‖z‖ ≤ 1) :
    |(tangentError dA dB z).re| ≤ 4 * eps :=
  (Complex.abs_re_le_norm _).trans (tangentError_norm_le heps hA hB hz)

theorem chordPoint_normSq (u : ℝ) :
    Complex.normSq (chordPoint u) = (4 / 9) * (1 - u + u ^ 2) := by
  simp [chordPoint, Complex.normSq_apply]
  ring_nf
  linear_combination (u ^ 2 / 9) * sqrtThree_sq

theorem chordPoint_norm_le_one {u : ℝ} (hu0 : 0 ≤ u) (hu1 : u ≤ 1) :
    ‖chordPoint u‖ ≤ 1 := by
  have hprod : 0 ≤ u * (1 - u) :=
    mul_nonneg hu0 (sub_nonneg.mpr hu1)
  have hsq := chordPoint_normSq u
  rw [Complex.normSq_eq_norm_sq] at hsq
  have hn := norm_nonneg (chordPoint u)
  have hpoly : 1 - u + u ^ 2 ≤ 1 := by nlinarith
  have hnormsq : ‖chordPoint u‖ ^ 2 ≤ 4 / 9 := by nlinarith
  nlinarith [sq_nonneg (‖chordPoint u‖ - 1)]

def rayZeroPoint (t : ℝ) : ℂ := ⟨t, 0⟩
def rayOnePoint (t : ℝ) : ℂ := (t : ℂ) * omega

theorem omega_normSq : Complex.normSq omega = 1 := by
  simp [omega, Complex.normSq_apply]
  nlinarith [sqrtThree_sq]

theorem omega_norm : ‖omega‖ = 1 := by
  have h := omega_normSq
  rw [Complex.normSq_eq_norm_sq] at h
  nlinarith [norm_nonneg omega]

theorem rayZeroPoint_norm_le_one {t : ℝ} (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    ‖rayZeroPoint t‖ ≤ 1 := by
  have hsq : ‖rayZeroPoint t‖ ^ 2 = t ^ 2 := by
    rw [← Complex.normSq_eq_norm_sq]
    simp [rayZeroPoint, Complex.normSq_apply]
    ring
  have hn := norm_nonneg (rayZeroPoint t)
  have heq : ‖rayZeroPoint t‖ = t := by
    nlinarith [sq_nonneg (‖rayZeroPoint t‖ - t)]
  linarith

theorem rayOnePoint_norm_le_one {t : ℝ} (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    ‖rayOnePoint t‖ ≤ 1 := by
  rw [rayOnePoint, norm_mul, omega_norm]
  simpa [Real.norm_eq_abs, abs_of_nonneg ht0] using ht1

theorem endpoint_rayZero_identity (t : ℝ) :
    pairedTangentComplex endpointA endpointB (rayZeroPoint t) =
      pairedTangentRay (aNeg (1 / 4)) bNeg t := by
  simp [pairedTangentComplex, endpointA, endpointB, rayZeroPoint,
    pairedTangentRay, aNeg, bNeg, Complex.mul_re, Complex.mul_im,
    Complex.conj_re, Complex.conj_im, pow_succ]
  ring

theorem endpoint_rayOne_identity (t : ℝ) :
    pairedTangentComplex endpointA endpointB (rayOnePoint t) =
      pairedTangentRay (aNeg (1 / 4)) bHigh t := by
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
  simp [pairedTangentComplex, endpointA, endpointB, rayOnePoint, omega,
    pairedTangentRay, aNeg, bHigh, Complex.mul_re, Complex.mul_im,
    Complex.conj_re, Complex.conj_im, pow_succ]
  ring_nf
  rw [hs6, hs5, hs4, hs3, hs2]
  ring

theorem rayOneBarrier_lower {t : ℝ} (ht : 2 / 3 ≤ t) :
    41 / 81 ≤ rayOneBarrier t := by
  have hu : 0 ≤ 3 * t - 2 := by nlinarith
  have hrest : 0 ≤
      8 * (3 * t - 2) ^ 5 + 75 * (3 * t - 2) ^ 4 +
      334 * (3 * t - 2) ^ 3 + 844 * (3 * t - 2) ^ 2 +
      642 * (3 * t - 2) := by positivity
  have hid := rayOneBarrier_identity t
  nlinarith

/-- The endpoint direction-one tail has a uniform margin much larger than the
coefficient perturbation budget. -/
theorem endpoint_rayOne_le {t : ℝ} (ht : 2 / 3 ≤ t) (ht1 : t ≤ 1) :
    pairedTangentComplex endpointA endpointB (rayOnePoint t) ≤
      -(41 : ℝ) / 2916 := by
  have ht0 : 0 ≤ t := by nlinarith
  have ht2 : t ^ 2 ≤ 1 := pow_le_one₀ ht0 ht1
  have ht4 : t ^ 4 ≤ 1 := pow_le_one₀ ht0 ht1
  have hp : 0 ≤ t - t ^ 5 := by
    have heq : t - t ^ 5 = t * (1 - t ^ 4) := by ring
    rw [heq]
    exact mul_nonneg ht0 (sub_nonneg.mpr ht4)
  have hq : 0 ≤ t ^ 2 - t ^ 4 := by
    have heq : t ^ 2 - t ^ 4 = t ^ 2 * (1 - t ^ 2) := by ring
    rw [heq]
    exact mul_nonneg (sq_nonneg t) (sub_nonneg.mpr ht2)
  have ha : aNeg (1 / 4) ≤ -(5 : ℝ) / 24 := by
    unfold aNeg
    nlinarith [sqrtThree_gt_fiveThirds]
  have hb : bHigh ≤ (3 : ℝ) / 4 := by
    unfold bHigh
    nlinarith [sqrtTwo_lt_threeHalves]
  have hpa := mul_le_mul_of_nonneg_left ha hp
  have hqb := mul_le_mul_of_nonneg_left hb hq
  have hmodel : pairedTangentRay (aNeg (1 / 4)) bHigh t ≤
      -(5 : ℝ) / 24 * (t - t ^ 5) +
        (3 : ℝ) / 4 * (t ^ 2 - t ^ 4) - t ^ 6 := by
    unfold pairedTangentRay
    nlinarith
  have hid : -(5 : ℝ) / 24 * (t - t ^ 5) +
        (3 : ℝ) / 4 * (t ^ 2 - t ^ 4) - t ^ 6 =
      -t * rayOneBarrier t / 24 := by
    unfold rayOneBarrier
    ring
  have hbar := rayOneBarrier_lower ht
  have hbar0 : (0 : ℝ) ≤ (41 : ℝ) / 81 := by norm_num
  have hmul : (2 / 3 : ℝ) * (41 / 81) ≤ t * rayOneBarrier t :=
    mul_le_mul ht hbar hbar0 ht0
  rw [endpoint_rayOne_identity]
  rw [hid] at hmodel
  nlinarith

theorem perturbed_rayZero_identity (dA dB : ℂ) (t : ℝ) :
    pairedTangentComplex (endpointA + dA) (endpointB + dB) (rayZeroPoint t) =
      (t - t ^ 5) * (endpointA + dA).re +
        (t ^ 2 - t ^ 4) * (endpointB + dB).re - t ^ 6 := by
  simp [pairedTangentComplex, endpointA, endpointB, rayZeroPoint,
    Complex.mul_re, Complex.mul_im, Complex.conj_re, Complex.conj_im,
    pow_succ]
  ring

theorem perturbed_rayZero_nonpos {dA dB : ℂ}
    (hA : ‖dA‖ ≤ 1 / 10000) (hB : ‖dB‖ ≤ 1 / 10000)
    {t : ℝ} (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    pairedTangentComplex (endpointA + dA) (endpointB + dB)
      (rayZeroPoint t) ≤ 0 := by
  have hAreAbs := Complex.abs_re_le_norm dA
  have hBreAbs := Complex.abs_re_le_norm dB
  have hAre : dA.re ≤ 1 / 10000 :=
    (le_abs_self dA.re).trans (hAreAbs.trans hA)
  have hBre : dB.re ≤ 1 / 10000 :=
    (le_abs_self dB.re).trans (hBreAbs.trans hB)
  have hAneg : (endpointA + dA).re ≤ 0 := by
    simp [endpointA]
    nlinarith [sqrtThree_gt_fiveThirds]
  have hBneg : (endpointB + dB).re ≤ 0 := by
    have hs2 := sqrtTwo_gt_one
    have hs3 : 1 < sqrtThree := by nlinarith [sqrtThree_gt_fiveThirds]
    have hprod : 1 < sqrtTwo * sqrtThree :=
      lt_of_lt_of_le hs2 (by
        simpa using mul_le_mul_of_nonneg_left (le_of_lt hs3) sqrtTwo_nonneg)
    simp [endpointB]
    nlinarith
  have ht2 : t ^ 2 ≤ 1 := pow_le_one₀ ht0 ht1
  have ht4 : t ^ 4 ≤ 1 := pow_le_one₀ ht0 ht1
  have hp : 0 ≤ t - t ^ 5 := by
    have heq : t - t ^ 5 = t * (1 - t ^ 4) := by ring
    rw [heq]
    exact mul_nonneg ht0 (sub_nonneg.mpr ht4)
  have hq : 0 ≤ t ^ 2 - t ^ 4 := by
    have heq : t ^ 2 - t ^ 4 = t ^ 2 * (1 - t ^ 2) := by ring
    rw [heq]
    exact mul_nonneg (sq_nonneg t) (sub_nonneg.mpr ht2)
  rw [perturbed_rayZero_identity]
  have hpa := mul_nonpos_of_nonneg_of_nonpos hp hAneg
  have hqb := mul_nonpos_of_nonneg_of_nonpos hq hBneg
  have ht6 : 0 ≤ t ^ 6 := by positivity
  linarith

theorem perturbed_chord_strict {dA dB : ℂ}
    (hA : ‖dA‖ ≤ 1 / 10000) (hB : ‖dB‖ ≤ 1 / 10000)
    {u : ℝ} (hu0 : 0 ≤ u) (hu1 : u ≤ 1) :
    pairedTangentComplex (endpointA + dA) (endpointB + dB)
      (chordPoint u) < 0 := by
  have herr := tangentError_re_abs_le (by norm_num : (0 : ℝ) ≤ 1 / 10000)
    hA hB (chordPoint_norm_le_one hu0 hu1)
  have herrUp : (tangentError dA dB (chordPoint u)).re ≤ 4 / 10000 :=
    by nlinarith [le_abs_self (tangentError dA dB (chordPoint u)).re]
  rw [pairedTangentComplex_add, endpoint_chord_identity]
  have hbase := endpointChordPower_le hu0 hu1
  nlinarith

theorem perturbed_rayOne_strict {dA dB : ℂ}
    (hA : ‖dA‖ ≤ 1 / 10000) (hB : ‖dB‖ ≤ 1 / 10000)
    {t : ℝ} (ht : 2 / 3 ≤ t) (ht1 : t ≤ 1) :
    pairedTangentComplex (endpointA + dA) (endpointB + dB)
      (rayOnePoint t) < 0 := by
  have ht0 : 0 ≤ t := by nlinarith
  have herr := tangentError_re_abs_le (by norm_num : (0 : ℝ) ≤ 1 / 10000)
    hA hB (rayOnePoint_norm_le_one ht0 ht1)
  have herrUp : (tangentError dA dB (rayOnePoint t)).re ≤ 4 / 10000 :=
    by nlinarith [le_abs_self (tangentError dA dB (rayOnePoint t)).re]
  rw [pairedTangentComplex_add]
  have hbase := endpoint_rayOne_le ht ht1
  nlinarith

/-- A genuine open ball in the two complex low-mode coefficients has the same
adjacent radius-`2/3` connector. -/
theorem coefficient_ball_connector {A B : ℂ}
    (hA : ‖A - endpointA‖ ≤ 1 / 10000)
    (hB : ‖B - endpointB‖ ≤ 1 / 10000) :
    (∀ u : ℝ, 0 ≤ u → u ≤ 1 →
      pairedTangentComplex A B (chordPoint u) < 0) ∧
    (∀ t : ℝ, 2 / 3 ≤ t → t ≤ 1 →
      pairedTangentComplex A B (rayZeroPoint t) ≤ 0) ∧
    (∀ t : ℝ, 2 / 3 ≤ t → t ≤ 1 →
      pairedTangentComplex A B (rayOnePoint t) < 0) := by
  have hAid : endpointA + (A - endpointA) = A := by ring
  have hBid : endpointB + (B - endpointB) = B := by ring
  refine ⟨?_, ?_, ?_⟩
  · intro u hu0 hu1
    rw [← hAid, ← hBid]
    exact perturbed_chord_strict hA hB hu0 hu1
  · intro t ht ht1
    rw [← hAid, ← hBid]
    exact perturbed_rayZero_nonpos hA hB (by nlinarith) ht1
  · intro t ht ht1
    rw [← hAid, ← hBid]
    exact perturbed_rayOne_strict hA hB ht ht1

end

end ErdosProblems.Erdos1041.SexticMixedTruncatedNeighborhood
