import Erdos249257.SuffixCylinderTwoSheet
import Erdos249257.SuffixCylinderBelow

/-!
# Exact feedback fan-in: advance or one certified in-strip hole
-/

namespace Erdos249257.SuffixCylinderFeedbackFanIn

open Erdos249257
open Erdos249257.HalfCarryReachability
open Erdos249257.HalfCarrySelectedWindow
open Erdos249257.SelectedSuffixCylinder
open Erdos249257.SuffixCylinderPromotion
open Erdos249257.SuffixCylinderThreshold
open Erdos249257.SuffixCylinderGlobalProducer
open Erdos249257.RewindSeamOperationalBridge

/-- A specified crossing coefficient profile realizes its specified seam
coordinate.  Unlike the existential wrapper in `SuffixCylinderGlobalProducer`,
this form retains `c`, which is needed to decide whether the hole escapes. -/
theorem protectedEvenSeamRealizedAt_succ_of_crossingProfile
    {K N E c : ℕ}
    (W : SelectedHalfWindow N (halfStripBound N))
    (hN : 1 ≤ N)
    (hcrossLow : 2 ^ (N - (K + 1)) < E)
    (hprofile : ∀ k (hk : 1 ≤ k) (hkR : k ≤ halfStripBound N),
      supportCoeff (wordSupport (W.word k hk hkR)) (N + 1) =
        if k ≤ E - 2 ^ (N - (K + 1)) then c + 1 else c)
    (h27 : 27 ≤ halfStripBound (N + 1)) :
    ProtectedEvenSeamRealizedAt (N + 1)
      (E - 2 ^ (N - (K + 1)) : ℕ) (c : ℤ) := by
  let δ := E - 2 ^ (N - (K + 1))
  have hδpos : 1 ≤ δ := by
    dsimp [δ]
    omega
  have hR : 1 ≤ halfStripBound N := by
    unfold halfStripBound
    omega
  have hcoeffOne := hprofile 1 (by omega) hR
  have hcoeffOne' :
      supportCoeff (wordSupport (W.word 1 (by omega) hR)) (N + 1) = c + 1 := by
    simpa [δ, if_pos hδpos] using hcoeffOne
  let a₁ := W.word 1 (by omega) hR
  have hc : c + 1 ≤ 2 * Nat.sqrt (N + 1) := by
    rw [← hcoeffOne']
    exact supportCoeff_le_two_mul_sqrt (wordSupport a₁) (N + 1)
  have hbuffer :
      halfStripBound (N + 1) + (c + 1) ≤ 2 * halfStripBound N := by
    simpa using halfStripBound_add_coeff_le_two_mul_pred
      (n := N + 1) (c := c + 1) (by omega) hc
  apply protectedEvenSeamRealizedAt_succ_of_profile
    hN W le_rfl h27 hbuffer
  intro k hk hkR
  simpa [δ] using hprofile k hk hkR

/-- **Complete feedback fan-in.** At an exact half-divisor horizon, low and
high common-bit cases advance ordinarily. A crossing whose one-hole seam
escapes below or above the next strip is recylindrified by the corresponding
sheet constructor. Therefore the only non-advancing result is a realized
seam whose exact integer hole lies inside the next full strip. -/
theorem CylinderStage.feedbackAdvance_or_protectedSeam_inStrip
    {K N : ℕ} (S : CylinderStage K N)
    (hN : 1 ≤ N) (hK1N : K + 1 ≤ N)
    (hrow : N + 1 = 2 * (K + 1))
    (h27 : 27 ≤ halfStripBound (N + 1)) :
    Nonempty (CylinderStage (K + 1) (N + 1)) ∨
      ∃ δ c : ℕ,
        ProtectedEvenSeamRealizedAt (N + 1) (δ : ℤ) (c : ℤ) ∧
        (1 : ℤ) ≤ 2 * (δ : ℤ) - (c : ℤ) ∧
        2 * (δ : ℤ) - (c : ℤ) ≤
          (halfStripBound (N + 1) : ℤ) := by
  have hfeedback : (N + 1) / 2 ≤ K + 1 := by
    rw [hrow]
    omega
  by_cases hbelow : S.endpoint ≤ 2 ^ (N - (K + 1))
  · left
    exact ⟨(Erdos249257.SuffixCylinderGlobalProducer.CylinderStage.promoteLow
      S hK1N hbelow |>.advance hN hfeedback)⟩
  · by_cases habove :
        2 ^ (N - (K + 1)) + halfStripBound N ≤ S.endpoint
    · left
      exact ⟨(S.promoteHigh hK1N habove).advance hN hfeedback⟩
    · have hcrossLow : 2 ^ (N - (K + 1)) < S.endpoint := by omega
      have hcrossHigh :
          S.endpoint < 2 ^ (N - (K + 1)) + halfStripBound N := by omega
      obtain ⟨c, hprofile⟩ :=
        supportCoeff_profile_of_crossingSuffixCylinder
          S.window hK1N hrow S.cylinder hcrossLow
      let δ := S.endpoint - 2 ^ (N - (K + 1))
      have hseam : ProtectedEvenSeamRealizedAt (N + 1) (δ : ℤ) (c : ℤ) := by
        simpa [δ] using
          protectedEvenSeamRealizedAt_succ_of_crossingProfile
            S.window hN hcrossLow hprofile h27
      by_cases hholeBelow : 2 * δ - c < 1
      · left
        exact ⟨
          Erdos249257.SuffixCylinderBelow.CylinderStage.feedbackAdvanceCrossingBelow
            S hN hK1N hcrossLow hcrossHigh c
            (by simpa [δ] using hprofile) hholeBelow⟩
      · by_cases hholeAbove : halfStripBound (N + 1) < 2 * δ - c
        · left
          exact ⟨
            Erdos249257.SuffixCylinderTwoSheet.CylinderStage.feedbackAdvanceCrossingAbove
              S hN hK1N hcrossLow hcrossHigh c
              (by simpa [δ] using hprofile) hholeAbove⟩
        · right
          refine ⟨δ, c, hseam, ?_, ?_⟩
          · omega
          · omega

#print axioms protectedEvenSeamRealizedAt_succ_of_crossingProfile
#print axioms CylinderStage.feedbackAdvance_or_protectedSeam_inStrip

end Erdos249257.SuffixCylinderFeedbackFanIn
