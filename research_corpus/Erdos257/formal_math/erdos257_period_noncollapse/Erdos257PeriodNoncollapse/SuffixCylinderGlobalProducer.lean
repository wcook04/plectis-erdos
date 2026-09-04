import Erdos257PeriodNoncollapse.SuffixCylinderThreshold

/-!
# Total feedback step for endpoint-indexed suffix cylinders

At an exact half-divisor horizon, an endpoint cylinder has only three
possibilities.  Its suffix interval lies below the new head bit, lies above
it, or crosses it.  The first two cases promote the cylinder and continue;
the crossing case has an exact unit-drop coefficient profile and realizes
the already-landed localized one-hole seam.
-/

namespace Erdos257PeriodNoncollapse.SuffixCylinderGlobalProducer

open Erdos257PeriodNoncollapse
open Erdos257PeriodNoncollapse.HalfCarryReachability
open Erdos257PeriodNoncollapse.HalfCarrySelectedWindow
open Erdos257PeriodNoncollapse.SelectedSuffixCylinder
open Erdos257PeriodNoncollapse.SuffixCylinderPromotion
open Erdos257PeriodNoncollapse.SuffixCylinderThreshold
open Erdos257PeriodNoncollapse.RewindHalfDivisorAdapter
open Erdos257PeriodNoncollapse.RewindSeamOperationalBridge
open Erdos257PeriodNoncollapse.HalfDivisorUnitDrop

/-- Inside a suffix cylinder whose endpoint is above the new head power,
the new bit is true exactly on the initial carry segment ending at
`E - 2^(N-(K+1))`. -/
theorem headBit_true_iff_le_crossingCut
    {K N R E : ℕ} (W : SelectedHalfWindow N R)
    (hK1N : K + 1 ≤ N)
    (hcyl : HasSuffixCylinderAt W
      ((Nat.le_succ K).trans hK1N) E)
    (hhead : 2 ^ (N - (K + 1)) < E)
    {k : ℕ} (hk : 1 ≤ k) (hkR : k ≤ R) :
    W.word k hk hkR ⟨K + 1, by omega⟩ = true ↔
      k ≤ E - 2 ^ (N - (K + 1)) := by
  rcases hcyl with ⟨_pfx, hcyl⟩
  have hendpoint := (hcyl k hk hkR).2
  constructor
  · intro htrue
    have hle := headPower_le_wordSuffixNumeral_of_true hK1N
      (W.word k hk hkR) htrue
    change wordSuffixNumeral (W.word k hk hkR) K (N - K) + k = E
      at hendpoint
    omega
  · intro hkcut
    cases hbit : W.word k hk hkR ⟨K + 1, by omega⟩ with
    | false =>
        have hlt := wordSuffixNumeral_lt_headPower_of_false hK1N
          (W.word k hk hkR) hbit
        change wordSuffixNumeral (W.word k hk hkR) K (N - K) + k = E
          at hendpoint
        omega
    | true => rfl

/-- At the exact doubled row, a crossing endpoint cylinder has the literal
unit-drop coefficient profile.  This is the object-level fact needed by the
operational one-hole seam consumer, obtained directly from the cylinder
rather than from a separately retained rewind history. -/
theorem supportCoeff_profile_of_crossingSuffixCylinder
    {K N R E : ℕ} (W : SelectedHalfWindow N R)
    (hK1N : K + 1 ≤ N) (hrow : N + 1 = 2 * (K + 1))
    (hcyl : HasSuffixCylinderAt W
      ((Nat.le_succ K).trans hK1N) E)
    (hhead : 2 ^ (N - (K + 1)) < E) :
    ∃ c : ℕ, ∀ k (hk : 1 ≤ k) (hkR : k ≤ R),
      supportCoeff (wordSupport (W.word k hk hkR)) (N + 1) =
        if k ≤ E - 2 ^ (N - (K + 1)) then c + 1 else c := by
  classical
  rcases hcyl with ⟨pfx, hcyl⟩
  let c := supportCoeff (wordSupport (extendHalfWord pfx false)) (N + 1)
  refine ⟨c, ?_⟩
  intro k hk hkR
  have hprefix := (hcyl k hk hkR).1
  have hbitIff := headBit_true_iff_le_crossingCut W hK1N
    ⟨pfx, hcyl⟩ hhead hk hkR
  by_cases hkcut : k ≤ E - 2 ^ (N - (K + 1))
  · rw [if_pos hkcut]
    have hbit : W.word k hk hkR ⟨K + 1, by omega⟩ = true :=
      hbitIff.2 hkcut
    have hrestrict :
        restrictWord hK1N (W.word k hk hkR) =
          extendHalfWord pfx true :=
      restrictWord_succ_eq_extendHalfWord hK1N (W.word k hk hkR)
        pfx true hprefix hbit
    calc
      supportCoeff (wordSupport (W.word k hk hkR)) (N + 1) =
          supportCoeff (wordSupport (extendHalfWord pfx true)) (N + 1) := by
        rw [hrow]
        exact supportCoeff_eq_of_restriction_at_halfDivisor hK1N
          (by omega) (W.word k hk hkR) (extendHalfWord pfx true) hrestrict
      _ = supportCoeff (wordSupport (extendHalfWord pfx false))
            (N + 1) + 1 := by
        rw [hrow]
        exact supportCoeff_extend_true_eq_false_add_one_at_double pfx
      _ = c + 1 := by rfl
  · rw [if_neg hkcut]
    have hbit : W.word k hk hkR ⟨K + 1, by omega⟩ = false := by
      cases hb : W.word k hk hkR ⟨K + 1, by omega⟩ with
      | false => rfl
      | true => exact (hkcut (hbitIff.1 hb)).elim
    have hrestrict :
        restrictWord hK1N (W.word k hk hkR) =
          extendHalfWord pfx false :=
      restrictWord_succ_eq_extendHalfWord hK1N (W.word k hk hkR)
        pfx false hprefix hbit
    calc
      supportCoeff (wordSupport (W.word k hk hkR)) (N + 1) =
          supportCoeff (wordSupport (extendHalfWord pfx false)) (N + 1) := by
        rw [hrow]
        exact supportCoeff_eq_of_restriction_at_halfDivisor hK1N
          (by omega) (W.word k hk hkR) (extendHalfWord pfx false) hrestrict
      _ = c := by rfl

/-- A genuine crossing of the head threshold realizes the localized
one-hole seam at the produced even row. -/
theorem protectedEvenSeamRealizedAt_succ_of_crossingSuffixCylinder
    {K N E : ℕ}
    (W : SelectedHalfWindow N (halfStripBound N))
    (hK1N : K + 1 ≤ N) (hrow : N + 1 = 2 * (K + 1))
    (hN : 1 ≤ N)
    (hcyl : HasSuffixCylinderAt W
      ((Nat.le_succ K).trans hK1N) E)
    (hcrossLow : 2 ^ (N - (K + 1)) < E)
    (hcrossHigh : E < 2 ^ (N - (K + 1)) + halfStripBound N)
    (h27 : 27 ≤ halfStripBound (N + 1)) :
    ∃ δ c : ℤ, ProtectedEvenSeamRealizedAt (N + 1) δ c := by
  obtain ⟨c, hprofile⟩ :=
    supportCoeff_profile_of_crossingSuffixCylinder W hK1N hrow hcyl hcrossLow
  let δ := E - 2 ^ (N - (K + 1))
  have hR : 1 ≤ halfStripBound N := by
    unfold halfStripBound
    omega
  have hδpos : 1 ≤ δ := by
    dsimp [δ]
    omega
  have hδR : δ < halfStripBound N := by
    dsimp [δ]
    omega
  have hcoeffOne := hprofile 1 (by omega) hR
  rw [if_pos (by omega : 1 ≤ δ)] at hcoeffOne
  let a₁ := W.word 1 (by omega) hR
  have hc : c + 1 ≤ 2 * Nat.sqrt (N + 1) := by
    rw [← hcoeffOne]
    exact supportCoeff_le_two_mul_sqrt (wordSupport a₁) (N + 1)
  have hbuffer :
      halfStripBound (N + 1) + (c + 1) ≤ 2 * halfStripBound N := by
    simpa using halfStripBound_add_coeff_le_two_mul_pred
      (n := N + 1) (c := c + 1) (by omega) hc
  refine ⟨(δ : ℤ), (c : ℤ), ?_⟩
  apply protectedEvenSeamRealizedAt_succ_of_profile
    hN W le_rfl h27 hbuffer
  intro k hk hkR
  simpa [δ] using hprofile k hk hkR

/-- Low-side cutoff promotion, complementary to `CylinderStage.promoteHigh`.
The endpoint is unchanged because the newly exposed bit is uniformly false. -/
noncomputable def CylinderStage.promoteLow
    {K N : ℕ} (S : CylinderStage K N) (hK1N : K + 1 ≤ N)
    (hbelow : S.endpoint ≤ 2 ^ (N - (K + 1))) :
    CylinderStage (K + 1) N := by
  have hR : 1 ≤ halfStripBound N := by
    unfold halfStripBound
    omega
  have hpromote :=
    promoteSuffixCylinderAt_succ_of_endpoint_le_headThreshold
      S.window hK1N hR S.cylinder hbelow
  exact ⟨hK1N, S.window, S.endpoint, hpromote.1, hpromote.2⟩

/-- Center the odd-row endpoint at the newly exposed head weight. -/
def centeredThresholdDelta (k endpoint oddCoeff : ℕ) : ℤ :=
  2 * (endpoint : ℤ) - (oddCoeff : ℤ) - (2 : ℤ) ^ k

/-- Exact two-row centered recurrence.  The Boolean is the boundary decision:
`true` subtracts the newly exposed head weight, while `false` retains it. -/
theorem centeredThresholdDelta_step
    (k endpoint nextEndpoint oddCoeff evenCoeff nextOddCoeff : ℕ)
    (bit : Bool)
    (hstep :
      (nextEndpoint : ℤ) =
        4 * (endpoint : ℤ) - 2 * (oddCoeff : ℤ) -
          (if bit then (2 : ℤ) ^ (k + 1) else 0) -
          (evenCoeff : ℤ)) :
    centeredThresholdDelta (k + 1) nextEndpoint nextOddCoeff =
      4 * centeredThresholdDelta k endpoint oddCoeff +
        (if bit then -(2 : ℤ) ^ (k + 1) else (2 : ℤ) ^ (k + 1)) -
        2 * (evenCoeff : ℤ) - (nextOddCoeff : ℤ) := by
  unfold centeredThresholdDelta
  rw [hstep]
  split <;> ring

/-- From cutoff two onward, any next centered value lies in one residue class
modulo eight determined by the three adjacent support coefficients.  This is
a necessary filter for a future crossing, not a no-crossing theorem. -/
theorem eight_dvd_centeredThresholdDelta_step_pulse
    (k endpoint nextEndpoint oddCoeff evenCoeff nextOddCoeff : ℕ)
    (bit : Bool)
    (hk : 2 ≤ k)
    (hstep :
      (nextEndpoint : ℤ) =
        4 * (endpoint : ℤ) - 2 * (oddCoeff : ℤ) -
          (if bit then (2 : ℤ) ^ (k + 1) else 0) -
          (evenCoeff : ℤ)) :
    (8 : ℤ) ∣
      centeredThresholdDelta (k + 1) nextEndpoint nextOddCoeff +
        2 * (evenCoeff : ℤ) + (nextOddCoeff : ℤ) -
        4 * (oddCoeff : ℤ) := by
  obtain ⟨j, rfl⟩ := Nat.exists_eq_add_of_le hk
  rw [centeredThresholdDelta_step
    (k := 2 + j) (endpoint := endpoint) (nextEndpoint := nextEndpoint)
    (oddCoeff := oddCoeff) (evenCoeff := evenCoeff)
    (nextOddCoeff := nextOddCoeff) bit hstep]
  unfold centeredThresholdDelta
  have hpow : (2 : ℤ) ^ (2 + j) = 4 * (2 : ℤ) ^ j := by
    rw [pow_add]
    norm_num
  have hpowSucc : (2 : ℤ) ^ (2 + j + 1) = 8 * (2 : ℤ) ^ j := by
    rw [show 2 + j + 1 = 3 + j by omega, pow_add]
    norm_num
  rw [hpow, hpowSucc]
  by_cases hbit : bit
  · rw [if_pos hbit]
    refine ⟨(endpoint : ℤ) - (oddCoeff : ℤ) - 3 * (2 : ℤ) ^ j, ?_⟩
    ring
  · rw [if_neg hbit]
    refine ⟨(endpoint : ℤ) - (oddCoeff : ℤ) - (2 : ℤ) ^ j, ?_⟩
    ring

/-- **Total feedback step.** At an exact half-divisor horizon, every full
suffix-cylinder stage either promotes through the new bit and advances one
row, or emits a realized localized one-hole seam.  There is no fourth
object-level case. -/
theorem CylinderStage.feedbackStep_or_protectedSeam
    {K N : ℕ} (S : CylinderStage K N)
    (hN : 1 ≤ N) (hK1N : K + 1 ≤ N)
    (hrow : N + 1 = 2 * (K + 1))
    (h27 : 27 ≤ halfStripBound (N + 1)) :
    Nonempty (CylinderStage (K + 1) (N + 1)) ∨
      ∃ δ c : ℤ, ProtectedEvenSeamRealizedAt (N + 1) δ c := by
  have hfeedback : (N + 1) / 2 ≤ K + 1 := by
    rw [hrow]
    omega
  by_cases hbelow : S.endpoint ≤ 2 ^ (N - (K + 1))
  · left
    exact ⟨(CylinderStage.promoteLow S hK1N hbelow).advance hN hfeedback⟩
  · by_cases habove :
        2 ^ (N - (K + 1)) + halfStripBound N ≤ S.endpoint
    · left
      exact ⟨(S.promoteHigh hK1N habove).advance hN hfeedback⟩
    · right
      exact protectedEvenSeamRealizedAt_succ_of_crossingSuffixCylinder
        S.window hK1N hrow hN S.cylinder (by omega) (by omega) h27

#print axioms headBit_true_iff_le_crossingCut
#print axioms supportCoeff_profile_of_crossingSuffixCylinder
#print axioms protectedEvenSeamRealizedAt_succ_of_crossingSuffixCylinder
#print axioms CylinderStage.promoteLow
#print axioms centeredThresholdDelta_step
#print axioms eight_dvd_centeredThresholdDelta_step_pulse
#print axioms CylinderStage.feedbackStep_or_protectedSeam

end Erdos257PeriodNoncollapse.SuffixCylinderGlobalProducer
