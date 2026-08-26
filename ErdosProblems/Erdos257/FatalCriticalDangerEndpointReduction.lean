import ErdosProblems.Erdos257.FatalBorrowMiddleScaleContradiction
import Erdos249257.HalfUpperResetCriticalBand

/-!
# Erdős #257: a critical danger is either early or endpoint-thin

The fatal-borrow lane now emits an actual upper reset whose charge lies in a
linear-width interval below its critical dyadic boundary.  This file pushes
that danger through an actual upper/right cylinder without estimating any
pulse separately.

If the run stops before the critical index, the still-open upper endpoint
packet law has failed.  If it reaches the critical index, exact scaling makes
the whole endpoint packet smaller than the same linear danger width dilated by
`4^k`.  Thus a fatal critical witness has only two precise escape sockets.
-/

namespace ErdosProblems.Erdos257

open Erdos257PeriodNoncollapse
open Erdos257PeriodNoncollapse.HalfCylinderIntegerGreedy
open Erdos257PeriodNoncollapse.HalfUpperResetCriticalBand

noncomputable section

/-- A critical upper-reset danger pushed through an actual right run has a
lossless dichotomy.  Either the run terminates strictly before the critical
index, or its complete endpoint packet is bounded by the linearly thin danger
window, amplified by exactly `4^k`.

The first branch is precisely the failure of the observed
`criticalIndex = rightRunLength` law.  The second branch retains the full
affine pulse charge, so no local-mass or denominator estimate is hidden. -/
theorem upperResetCriticalDanger_run_lt_or_endpointPacket_lt
    {d k j : ℕ} (hd5 : 5 ≤ d) (hk : k ≤ d)
    (hcarry : (seamAdjacentCut d hd5).successorCarries)
    (hrun : ∀ q : ℕ, q < k →
      seamIntegerGreedyRemainder (d + q + 2) +
          2 ^ (d + q + 2) +
          (seamAdjacentCut (d + q + 1) (by omega)).belowPulse + 4 =
        4 * seamIntegerGreedyRemainder (d + q + 1))
    (hcritical :
      CriticalDyadicBandIndex d (seamUpperResetCharge d hd5) j)
    (hdanger :
      2 ^ (d - j + 1) <
        seamUpperResetCharge d hd5 + 2 * (d + j)) :
    k < j ∨
      seamIntegerGreedyRemainder (d + k + 1) +
          affineRightRunCharge
            (fun q ↦
              (seamAdjacentCut (d + q + 1) (by omega)).belowPulse) k <
        4 ^ k * (2 * (d + k)) := by
  have hkj := seamUpperThenRightRun_length_le_criticalIndex
    hd5 hk hcarry hrun hcritical
  by_cases hEq : k = j
  · right
    subst j
    have hpacket :=
      seamUpperThenRightRun_remainder_add_charge_eq_scaledCriticalGap
        hd5 hk hcarry hrun
    have hgap :
        2 ^ (d - k + 1) - seamUpperResetCharge d hd5 <
          2 * (d + k) := by
      omega
    rw [hpacket]
    exact Nat.mul_lt_mul_of_pos_left hgap (pow_pos (by norm_num) k)
  · left
    omega

/-- Producer-facing contrapositive.  An endpoint packet which clears the
linear danger envelope forces the actual right run to stop before the
critical index.  Consequently, proving both the critical-index identity and
this lower envelope rules out every critical danger emitted by a fatal
borrow. -/
theorem upperResetCriticalDanger_run_lt_of_endpointPacket_ge
    {d k j : ℕ} (hd5 : 5 ≤ d) (hk : k ≤ d)
    (hcarry : (seamAdjacentCut d hd5).successorCarries)
    (hrun : ∀ q : ℕ, q < k →
      seamIntegerGreedyRemainder (d + q + 2) +
          2 ^ (d + q + 2) +
          (seamAdjacentCut (d + q + 1) (by omega)).belowPulse + 4 =
        4 * seamIntegerGreedyRemainder (d + q + 1))
    (hcritical :
      CriticalDyadicBandIndex d (seamUpperResetCharge d hd5) j)
    (hdanger :
      2 ^ (d - j + 1) <
        seamUpperResetCharge d hd5 + 2 * (d + j))
    (hpacket :
      4 ^ k * (2 * (d + k)) ≤
        seamIntegerGreedyRemainder (d + k + 1) +
          affineRightRunCharge
            (fun q ↦
              (seamAdjacentCut (d + q + 1) (by omega)).belowPulse) k) :
    k < j := by
  rcases upperResetCriticalDanger_run_lt_or_endpointPacket_lt
      hd5 hk hcarry hrun hcritical hdanger with hlt | hthin
  · exact hlt
  · omega

/-- A row-small seam state emits a last-upper-ancestor block whose complete
endpoint packet lies below the actual-scale linear envelope.  This is the
row-level version of the fatal-borrow theorem below and contains no selected
ancestry hypothesis. -/
theorem exists_lastUpperAncestorThinPacket_of_rowSmall
    {D : ℕ} (hD13 : 13 ≤ D)
    (hsmall : seamIntegerGreedyRemainder D < D) :
    ∃ (d : ℕ) (hd13 : 13 ≤ d) (k : ℕ),
      d < D ∧ k ≤ d ∧ d + k + 1 ≤ D ∧
        (seamAdjacentCut d (by omega)).successorCarries ∧
        (∀ q : ℕ, q < k →
          seamIntegerGreedyRemainder (d + q + 2) +
              2 ^ (d + q + 2) +
              (seamAdjacentCut (d + q + 1) (by omega)).belowPulse + 4 =
            4 * seamIntegerGreedyRemainder (d + q + 1)) ∧
        seamIntegerGreedyRemainder (d + k + 1) < d + k + 1 ∧
        seamIntegerGreedyRemainder (d + k + 1) +
            affineRightRunCharge
              (fun q ↦
                (seamAdjacentCut (d + q + 1) (by omega)).belowPulse) k <
          4 ^ k * (2 * (d + k)) := by
  obtain ⟨d, hd13, k, hdD, hk, hend, hcarry, hrun,
      hendpointSmall, hdanger⟩ :=
    exists_lastUpperAncestorRightRun_danger_of_rowSmall hD13 hsmall
  have hpacket :=
    seamUpperThenRightRun_remainder_add_charge_eq_scaledCriticalGap
      (d := d) (k := k) (by omega) hk hcarry hrun
  have hgap :
      2 ^ (d - k + 1) - seamUpperResetCharge d (by omega) <
        2 * (d + k) := by
    change 2 ^ (d - k + 1) <
      seamUpperResetCharge d (by omega) + 2 * (d + k) at hdanger
    omega
  have hthin :
      seamIntegerGreedyRemainder (d + k + 1) +
            affineRightRunCharge
              (fun q ↦
                (seamAdjacentCut (d + q + 1) (by omega)).belowPulse) k <
          4 ^ k * (2 * (d + k)) := by
    rw [hpacket]
    exact Nat.mul_lt_mul_of_pos_left hgap (pow_pos (by norm_num) k)
  exact ⟨d, hd13, k, hdD, hk, hend, hcarry, hrun,
    hendpointSmall, hthin⟩

/-- The actual-scale packet producer.  Unlike
`SeamUpperResetDyadicBandEscape`, this asks for no hypothetical dyadic index:
it only lower-bounds the complete packet after a literal upper reset and a
literal finite right-run recurrence. -/
def SeamActualUpperRightPacketLinearEscape : Prop :=
  ∀ (d k : ℕ) (hd5 : 5 ≤ d), 13 ≤ d → k ≤ d →
    (seamAdjacentCut d hd5).successorCarries →
    (∀ q : ℕ, q < k →
      seamIntegerGreedyRemainder (d + q + 2) +
          2 ^ (d + q + 2) +
          (seamAdjacentCut (d + q + 1) (by omega)).belowPulse + 4 =
        4 * seamIntegerGreedyRemainder (d + q + 1)) →
    4 ^ k * (2 * (d + k)) ≤
      seamIntegerGreedyRemainder (d + k + 1) +
        affineRightRunCharge
          (fun q ↦
            (seamAdjacentCut (d + q + 1) (by omega)).belowPulse) k

/-- Quotient-coordinate form of the actual upper/right producer.  Instead of
lower-bounding the terminal affine packet, it asks the immediate successor of
the upper reset to clear the translated dyadic boundary associated with the
*realized* right-run length.  This formulation contains no rational remainder
denominator and no accumulated pulse register. -/
def SeamActualUpperSuccessorLinearEscape : Prop :=
  ∀ (d k : ℕ) (hd5 : 5 ≤ d), 13 ≤ d → k ≤ d →
    (seamAdjacentCut d hd5).successorCarries →
    (∀ q : ℕ, q < k →
      seamIntegerGreedyRemainder (d + q + 2) +
          2 ^ (d + q + 2) +
          (seamAdjacentCut (d + q + 1) (by omega)).belowPulse + 4 =
        4 * seamIntegerGreedyRemainder (d + q + 1)) →
    2 ^ (d + 1) - 2 ^ (d - k + 1) + 2 * (d + k) ≤
      seamIntegerGreedyRemainder (d + 1)

/-- The terminal-packet and immediate-successor formulations are exactly
equivalent.  The right-run charge cancels through the exact cylinder, while
the upper-reset charge is complementary to the successor remainder. -/
theorem seamActualUpperRightPacketLinearEscape_iff_successorLinearEscape :
    SeamActualUpperRightPacketLinearEscape ↔
      SeamActualUpperSuccessorLinearEscape := by
  constructor
  · intro hpacket d k hd5 hd13 hk hcarry hrun
    have hlower := hpacket d k hd5 hd13 hk hcarry hrun
    have hpacketEq :=
      seamUpperThenRightRun_remainder_add_charge_eq_scaledCriticalGap
        hd5 hk hcarry hrun
    have hreset := seamUpperBranch_remainder_add_resetCharge_eq hd5 hcarry
    change seamIntegerGreedyRemainder (d + 1) +
        seamUpperResetCharge d hd5 = 2 ^ (d + 1) at hreset
    rw [hpacketEq] at hlower
    have hgap : 2 * (d + k) ≤
        2 ^ (d - k + 1) - seamUpperResetCharge d hd5 := by
      exact Nat.le_of_mul_le_mul_left hlower (pow_pos (by norm_num) k)
    have hsmallPow : 2 ^ (d - k + 1) ≤ 2 ^ (d + 1) :=
      Nat.pow_le_pow_right (by norm_num) (by omega)
    omega
  · intro hsuccessor d k hd5 hd13 hk hcarry hrun
    have hsucc := hsuccessor d k hd5 hd13 hk hcarry hrun
    have hpacketEq :=
      seamUpperThenRightRun_remainder_add_charge_eq_scaledCriticalGap
        hd5 hk hcarry hrun
    have hreset := seamUpperBranch_remainder_add_resetCharge_eq hd5 hcarry
    change seamIntegerGreedyRemainder (d + 1) +
        seamUpperResetCharge d hd5 = 2 ^ (d + 1) at hreset
    have hsmallPow : 2 ^ (d - k + 1) ≤ 2 ^ (d + 1) :=
      Nat.pow_le_pow_right (by norm_num) (by omega)
    have hgap : 2 * (d + k) ≤
        2 ^ (d - k + 1) - seamUpperResetCharge d hd5 := by
      omega
    rw [hpacketEq]
    exact Nat.mul_le_mul_left (4 ^ k) hgap

/-- The former all-index dyadic-band producer implies the actual-scale packet
producer.  This records the hierarchy direction formally: the new interface
discards every hypothetical band index which is not a realized right-run
length. -/
theorem SeamUpperResetDyadicBandEscape.toActualUpperRightPacketLinearEscape
    (hband : SeamUpperResetDyadicBandEscape) :
    SeamActualUpperRightPacketLinearEscape := by
  intro d k hd5 hd13 hk hcarry hrun
  let E := seamUpperResetCharge d hd5
  have hpacket :=
    seamUpperThenRightRun_remainder_add_charge_eq_scaledCriticalGap
      hd5 hk hcarry hrun
  rcases hband d hd5 hd13 hcarry k hk with hhigh | hlow
  · have hcylinder := seamUpperThenRightRun_exactCylinder hd5 hcarry hrun
    change seamIntegerGreedyRemainder (d + k + 1) + 4 ^ k * E +
        affineRightRunCharge
          (fun q ↦
            (seamAdjacentCut (d + q + 1) (by omega)).belowPulse) k =
      2 ^ (d + k + 1) at hcylinder
    have hfactor : 4 ^ k * 2 ^ (d - k + 1) = 2 ^ (d + k + 1) := by
      rw [show 4 ^ k = 2 ^ (2 * k) by
        rw [show 4 = 2 ^ 2 by norm_num, ← pow_mul], ← pow_add]
      congr 1
      omega
    have hweighted : 4 ^ k * E ≤ 4 ^ k * 2 ^ (d - k + 1) := by
      rw [hfactor]
      omega
    have hE : E ≤ 2 ^ (d - k + 1) :=
      Nat.le_of_mul_le_mul_left hweighted (pow_pos (by norm_num) k)
    change 2 ^ (d - k + 1) < E at hhigh
    omega
  · change E + 2 * (d + k) ≤ 2 ^ (d - k + 1) at hlow
    have hgap : 2 * (d + k) ≤ 2 ^ (d - k + 1) - E := by omega
    rw [hpacket]
    exact Nat.mul_le_mul_left (4 ^ k) hgap

/-- The actual-scale packet producer excludes every row-small seam state at
or after row thirteen.  The proof queries only the single last-ancestor block
returned by `exists_lastUpperAncestorThinPacket_of_rowSmall`. -/
theorem SeamActualUpperRightPacketLinearEscape.remainder_ge_row
    (hpacket : SeamActualUpperRightPacketLinearEscape)
    {D : ℕ} (hD13 : 13 ≤ D) :
    D ≤ seamIntegerGreedyRemainder D := by
  by_contra hnot
  have hsmall : seamIntegerGreedyRemainder D < D := Nat.lt_of_not_ge hnot
  obtain ⟨d, hd13, k, _hdD, hk, _hend, hcarry, hrun,
      _hendpointSmall, hthin⟩ :=
    exists_lastUpperAncestorThinPacket_of_rowSmall hD13 hsmall
  have hlower := hpacket d k (by omega) hd13 hk hcarry hrun
  omega

/-- The actual-scale packet producer supplies the canonical row-escape
producer. -/
theorem SeamActualUpperRightPacketLinearEscape.toMiddleProducerRowEscape
    (hpacket : SeamActualUpperRightPacketLinearEscape) :
    SeamMiddleProducerRowEscape := by
  intro s hs hs13 _hncarry _hmiddle
  simpa [seamAdjacentCut_remainder] using hpacket.remainder_ge_row hs13

/-- Direct counterexample endpoint: the actual-scale packet producer places
one-half in the Mersenne achievement set. -/
theorem half_mem_mersenneAchievementSet_of_actualUpperRightPacketLinearEscape
    (hpacket : SeamActualUpperRightPacketLinearEscape) :
    (1 / 2 : ℝ) ∈ mersenneAchievementSet := by
  exact half_mem_mersenneAchievementSet_of_middleProducerRowEscape
    hpacket.toMiddleProducerRowEscape

/-- Direct counterexample endpoint in the pulse-free successor coordinate. -/
theorem half_mem_mersenneAchievementSet_of_actualUpperSuccessorLinearEscape
    (hsuccessor : SeamActualUpperSuccessorLinearEscape) :
    (1 / 2 : ℝ) ∈ mersenneAchievementSet := by
  apply half_mem_mersenneAchievementSet_of_actualUpperRightPacketLinearEscape
  exact seamActualUpperRightPacketLinearEscape_iff_successorLinearEscape.mpr
    hsuccessor

/-- **Fatal borrow emits a last-ancestor thin endpoint packet.**  The
source-current last-upper-ancestor theorem supplies the literal actual run
length `k`, rather than an independently chosen critical index.  Substituting
its danger inequality into the exact run cylinder therefore removes the
dichotomy above completely: every mature fatal borrow yields a row-small
terminal remainder whose *complete* affine packet is below
`4^k * 2 * (s+k)`.

This is the direct consumer interface for a future endpoint lower-envelope
producer.  Proving that actual last-ancestor packets always clear the displayed
linear envelope would contradict a fatal borrow without any raw rational
denominator estimate. -/
theorem exists_lastUpperAncestorThinPacket_of_nonpositiveComplementBudget
    {d : ℕ} (hd : 13 ≤ d)
    (hskip : ¬ mersenneWeight d ≤
      greedyMersenneRemainder (1 / 2 : ℝ) (d - 1))
    (hfatal : halfSelectedAncestryComplementBudget d ≤ 0) :
    ∃ (s : ℕ) (hs13 : 13 ≤ s) (k : ℕ),
      s < d ∧ k ≤ s ∧ s + k + 1 ≤ d ∧
        (seamAdjacentCut s (by omega)).successorCarries ∧
        (∀ q : ℕ, q < k →
          seamIntegerGreedyRemainder (s + q + 2) +
              2 ^ (s + q + 2) +
              (seamAdjacentCut (s + q + 1) (by omega)).belowPulse + 4 =
            4 * seamIntegerGreedyRemainder (s + q + 1)) ∧
        seamIntegerGreedyRemainder (s + k + 1) < s + k + 1 ∧
        seamIntegerGreedyRemainder (s + k + 1) +
            affineRightRunCharge
              (fun q ↦
                (seamAdjacentCut (s + q + 1) (by omega)).belowPulse) k <
          4 ^ k * (2 * (s + k)) := by
  obtain ⟨s, hs13, k, hsd, hk, hend, hcarry, hrun,
      hendpointSmall, hdanger⟩ :=
    exists_lastUpperAncestorRightRunDanger_before_of_nonpositiveComplementBudget
      hd hskip hfatal
  have hpacket :=
    seamUpperThenRightRun_remainder_add_charge_eq_scaledCriticalGap
      (d := s) (k := k) (by omega) hk hcarry hrun
  have hgap :
      2 ^ (s - k + 1) - seamUpperResetCharge s (by omega) <
        2 * (s + k) := by
    omega
  have hthin :
      seamIntegerGreedyRemainder (s + k + 1) +
            affineRightRunCharge
              (fun q ↦
                (seamAdjacentCut (s + q + 1) (by omega)).belowPulse) k <
          4 ^ k * (2 * (s + k)) := by
    rw [hpacket]
    exact Nat.mul_lt_mul_of_pos_left hgap (pow_pos (by norm_num) k)
  exact ⟨s, hs13, k, hsd, hk, hend, hcarry, hrun,
    hendpointSmall, hthin⟩

end

end ErdosProblems.Erdos257

#print axioms ErdosProblems.Erdos257.upperResetCriticalDanger_run_lt_or_endpointPacket_lt
#print axioms ErdosProblems.Erdos257.upperResetCriticalDanger_run_lt_of_endpointPacket_ge
#print axioms ErdosProblems.Erdos257.exists_lastUpperAncestorThinPacket_of_rowSmall
#print axioms ErdosProblems.Erdos257.seamActualUpperRightPacketLinearEscape_iff_successorLinearEscape
#print axioms ErdosProblems.Erdos257.SeamUpperResetDyadicBandEscape.toActualUpperRightPacketLinearEscape
#print axioms ErdosProblems.Erdos257.SeamActualUpperRightPacketLinearEscape.remainder_ge_row
#print axioms ErdosProblems.Erdos257.SeamActualUpperRightPacketLinearEscape.toMiddleProducerRowEscape
#print axioms ErdosProblems.Erdos257.half_mem_mersenneAchievementSet_of_actualUpperRightPacketLinearEscape
#print axioms ErdosProblems.Erdos257.half_mem_mersenneAchievementSet_of_actualUpperSuccessorLinearEscape
#print axioms ErdosProblems.Erdos257.exists_lastUpperAncestorThinPacket_of_nonpositiveComplementBudget
