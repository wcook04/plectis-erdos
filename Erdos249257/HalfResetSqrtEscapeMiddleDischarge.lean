import Erdos249257.HalfResetSqrtEscapeScaleProducers

/-!
# Margin producers behind reset square-root escape

This module reduces the middle-producer half of `SeamResetSqrtEscape` to
branch-local bookkeeping plus one new margin statement, leaving the whole
escape resting on three uniformly-shaped claims: every decision margin of
the integer seam greedy stays above half-row scale.

Splitting on the branch that entered a middle reset row `s`:

* **right predecessor.**  The landed additive right recurrence gives
  `R_s + 2 ^ s + belowPulse + 4 = 4 * R_(s-1)`, i.e. the post-right
  remainder is *exactly* the slack by which the preceding take decision
  cleared its threshold.  A new `SeamTakeMarginScaleProducer` bounds that
  slack.  (A weaker claim `R_s >= 2 ^ s` is refuted by the exact
  arithmetic: the take condition only forces `4 * R_(s-1) >= 2 ^ s +
  belowPulse + 4`, whose substitution yields `R_s >= 0`.)
* **middle predecessor.**  The landed middle recurrence gives
  `R_s + belowPulse = 4 * R_(s-1) + 2 ^ s`, hence
  `R_s >= 2 ^ s - 2 * (s - 2)` by the universal pulse bound — free.
* **upper predecessor.**  The landed reset identity gives exactly
  `R_s = 2 ^ s - E_(s-1)`; discharging the producer here is equivalent
  to a ceiling bound on the upper reset charge.

Consequently `SeamResetSqrtEscape` follows from three statements:

* floor (landed): at every upper reset `d`,
  `3 * 2 ^ ((d + 5) / 2) <= E_d`;
* ceiling (new): at every upper reset `d` with `d >= 9`,
  `4 * E_d + 3 * 2 ^ ((d + 6) / 2) + 2 * (d - 1) <= 2 ^ (d + 3)`;
* take margin (new): at every non-carry row `t` with `t >= 9` whose
  branch takes the terminal bit,
  `2 ^ (t + 1) + belowPulse_t + 4 + 3 * 2 ^ ((t + 6) / 2)
    + 2 * (t - 1) <= 4 * R_t`.

All three say the same thing at the three decision types: the integer
seam greedy never decides with a sub-half-row margin.  No theorem proves
any of them unconditionally; empirically each holds with exponential
slack away from a handful of small rows.
-/

namespace Erdos249257

open HalfCylinderIntegerGreedy

/-- Every positive index is bounded by its own power of two. -/
private theorem le_two_pow_self (k : ℕ) : k ≤ 2 ^ k := by
  induction k with
  | zero => norm_num
  | succ n ih =>
      have hpos : (0 : ℕ) < 2 ^ n := by positivity
      calc
        n + 1 ≤ 2 ^ n + 1 := by linarith [ih]
        _ ≤ 2 ^ n + 2 ^ n := by linarith
        _ = 2 ^ (n + 1) := by rw [pow_succ]; ring

/-- Linear term absorbed by the shifted dyadic power. -/
private theorem ten_mul_le_two_pow_shifted {a : ℕ} (ha6 : 6 ≤ a) :
    (10 : ℕ) * a ≤ 2 ^ (a + 3) := by
  have hbase : 8 * a ≤ 2 ^ a :=
    HalfUpperResetCriticalBand.eight_mul_le_two_pow_of_six_le ha6
  have hpos : (0 : ℕ) < 2 ^ a := by positivity
  have hpowSplit : (2 : ℕ) ^ (a + 3) = 8 * 2 ^ a := by
    rw [pow_add, Nat.mul_comm]
    norm_num
  calc
    (10 : ℕ) * a ≤ 16 * a := by nlinarith
    _ = 2 * (8 * a) := by ring
    _ ≤ 2 * 2 ^ a := by exact Nat.mul_le_mul_left _ hbase
    _ ≤ 8 * 2 ^ a := by linarith
    _ = 2 ^ (a + 3) := hpowSplit.symm

/-- The uniform producer threshold is absorbed by four dyadic scales
from row seven onward. -/
private theorem threshold_le_four_mul_two_pow (s : ℕ) (hs7 : 7 ≤ s) :
    3 * 2 ^ ((s + 5) / 2) + 2 * (s - 2) ≤ 4 * 2 ^ s := by
  have hm : (s + 5) / 2 ≤ s - 1 := by omega
  have hmono : 2 ^ ((s + 5) / 2) ≤ 2 ^ (s - 1) :=
    Nat.pow_le_pow_right (by norm_num) hm
  have hdoubled : 2 * 2 ^ (s - 2) ≤ 2 ^ (s - 1) := by
    have hsq : (2 : ℕ) ^ ((s - 2) + 1) = 2 * 2 ^ (s - 2) :=
      pow_succ' 2 (s - 2)
    have hex : (2 : ℕ) ^ ((s - 2) + 1) ≤ 2 ^ (s - 1) :=
      Nat.pow_le_pow_right (by norm_num) (by omega)
    rw [hsq] at hex
    exact hex
  have h1 : (s - 2 : ℕ) ≤ 2 ^ (s - 2) := le_two_pow_self _
  have hsmall : 2 * (s - 2) ≤ 2 ^ (s - 1) := by linarith [h1, hdoubled]
  have hstep : 3 * 2 ^ ((s + 5) / 2) + 2 * (s - 2) ≤
      3 * 2 ^ (s - 1) + 2 ^ (s - 1) := by linarith
  have hsum : 3 * 2 ^ (s - 1) + 2 ^ (s - 1) = 2 * 2 ^ s := by
    have h1 : (2 : ℕ) ^ (s - 1) * 2 = 2 ^ s := by
      rw [← pow_succ]
      congr 1
      omega
    calc
      3 * 2 ^ (s - 1) + 2 ^ (s - 1) = 2 * (2 ^ (s - 1) * 2) := by ring
      _ = 2 * 2 ^ s := by rw [h1]
  calc
    3 * 2 ^ ((s + 5) / 2) + 2 * (s - 2)
        ≤ 3 * 2 ^ (s - 1) + 2 ^ (s - 1) := hstep
    _ = 2 * 2 ^ s := hsum
    _ ≤ 4 * 2 ^ s := by norm_num

/-- The threshold plus eight times the linear term stays under the
doubled dyadic scale from row ten onward. -/
private theorem threshold_add_eight_le_two_pow_succ_succ (s : ℕ)
    (hs10 : 10 ≤ s) :
    3 * 2 ^ ((s + 5) / 2) + 10 * (s - 2) ≤ 2 ^ (s + 2) := by
  have hmono : 2 ^ ((s + 5) / 2) ≤ 2 ^ (s - 1) :=
    Nat.pow_le_pow_right (by norm_num) (by omega)
  have hten : (10 : ℕ) * (s - 2) ≤ 2 ^ ((s - 2) + 3) :=
    ten_mul_le_two_pow_shifted (by omega)
  have hshift : (2 : ℕ) ^ ((s - 2) + 3) ≤ 2 ^ (s + 1) :=
    Nat.pow_le_pow_right (by norm_num) (by omega)
  have htenS : (10 : ℕ) * (s - 2) ≤ 2 ^ (s + 1) := hten.trans hshift
  have h4 : (2 : ℕ) ^ (s + 1) = 4 * 2 ^ (s - 1) := by
    have h : (2 : ℕ) ^ (s + 1) = 2 ^ (s - 1) * 2 ^ 2 := by
      rw [← pow_add]
      congr 1
      omega
    rw [h, Nat.mul_comm]
    norm_num
  have h8p : (2 : ℕ) ^ (s + 2) = 8 * 2 ^ (s - 1) := by
    have h : (2 : ℕ) ^ (s + 2) = 2 ^ (s - 1) * 2 ^ 3 := by
      rw [← pow_add]
      congr 1
      omega
    rw [h, Nat.mul_comm]
    norm_num
  have hpart : (3 : ℕ) * 2 ^ ((s + 5) / 2) + 10 * (s - 2) ≤
      3 * 2 ^ (s - 1) + 2 ^ (s + 1) := by
    have h3 : (3 : ℕ) * 2 ^ ((s + 5) / 2) ≤ 3 * 2 ^ (s - 1) :=
      Nat.mul_le_mul_left _ hmono
    linarith
  have hjoin : 3 * 2 ^ (s - 1) + 2 ^ (s + 1) ≤ 2 ^ (s + 2) := by
    rw [h4, h8p]
    omega
  calc
    3 * 2 ^ ((s + 5) / 2) + 10 * (s - 2)
        ≤ 3 * 2 ^ (s - 1) + 2 ^ (s + 1) := hpart
    _ ≤ 2 ^ (s + 2) := hjoin

/-- Four dyadic scales equal the doubled-row power. -/
private theorem four_mul_two_pow_eq_pow_add (s : ℕ) :
    (4 : ℕ) * 2 ^ s = 2 ^ (s + 2) :=
  calc
    (4 : ℕ) * 2 ^ s = 2 ^ 2 * 2 ^ s := by norm_num
    _ = 2 ^ (2 + s) := (pow_add 2 2 s).symm
    _ = 2 ^ (s + 2) := by rw [Nat.add_comm]

/-- **Middle-predecessor case.**  A middle reset entered by another
middle branch has source remainder within the linear pulse of the dyadic
scale. -/
theorem seamMiddleReset_sourceRemainder_ge_powShift_of_middlePrev
    {s : ℕ} (hprev5 : 5 ≤ s - 1) (hprev3 : 3 ≤ s - 1)
    (hpcarry :
      ¬ (seamAdjacentCut (s - 1) hprev5).successorCarries)
    (hpmiddle :
      4 * (seamAdjacentCut (s - 1) hprev5).remainder +
            (seamPerturbedFamily (s - 1) hprev3).gap -
            (seamAdjacentCut (s - 1) hprev5).belowPulse <
          (seamAdjacentCut (s - 1) hprev5).terminalWeight) :
    2 ^ s - 2 * (s - 2) ≤ seamIntegerGreedyRemainder s := by
  have hadd := seamMiddleBranch_nextRemainder_add_belowPulse_eq
    (s := s - 1) hprev5 hpcarry hpmiddle
  have hsEq : s - 1 + 1 = s := by omega
  rw [hsEq] at hadd
  have hpulse := seamAdjacentCut_belowPulse_le (s := s - 1) hprev5
  have hsmall : (seamAdjacentCut (s - 1) hprev5).belowPulse ≤
      2 * (s - 2) := by
    have hlt : (s - 1) - 2 ≤ s - 2 := by omega
    exact le_trans hpulse (Nat.mul_le_mul (le_refl 2) hlt)
  have hkey : 2 ^ s ≤ seamIntegerGreedyRemainder s + 2 * (s - 2) := by
    have hz : (0 : ℕ) ≤ 4 * seamIntegerGreedyRemainder (s - 1) :=
      Nat.zero_le _
    omega
  omega

/-- **Right-predecessor exact identity.**  After a right branch the new
remainder equals the take-decision margin of the previous row:
`R_s + 2 ^ s + belowPulse_(s-1) + 4 = 4 * R_(s-1)`. -/
theorem seamMiddleReset_sourceRemainder_eq_takeMargin_of_rightPrev
    {s : ℕ} (hprev5 : 5 ≤ s - 1) (hprev3 : 3 ≤ s - 1)
    (hpcarry :
      ¬ (seamAdjacentCut (s - 1) hprev5).successorCarries)
    (hpright : (seamAdjacentCut (s - 1) hprev5).terminalWeight ≤
      4 * (seamAdjacentCut (s - 1) hprev5).remainder +
        (seamPerturbedFamily (s - 1) hprev3).gap -
        (seamAdjacentCut (s - 1) hprev5).belowPulse) :
    seamIntegerGreedyRemainder s + 2 ^ s +
        (seamAdjacentCut (s - 1) hprev5).belowPulse + 4 =
      4 * seamIntegerGreedyRemainder (s - 1) := by
  have h := seamRightBranch_remainder_add_charge_eq
    (s := s - 1) hprev5 hpcarry hpright
  have hsEq : s - 1 + 1 = s := by omega
  rw [hsEq] at h
  exact h

/-- The named all-depth ceiling producer at upper resets: the quadrupled
reset charge plus the shifted threshold stays under the doubled dyadic
scale. -/
def SeamUpperResetChargeCeilingProducer : Prop :=
  ∀ (d : ℕ) (hd5 : 5 ≤ d), 9 ≤ d →
    (seamAdjacentCut d hd5).successorCarries →
      (4 * (4 * (seamAdjacentCut d hd5).overshoot +
          (seamAdjacentCut d hd5).abovePulse) +
        3 * 2 ^ ((d + 6) / 2) + 2 * (d - 1) : ℕ) ≤ 2 ^ (d + 3)

/-- The named all-depth take-margin producer: whenever the seam greedily
takes its terminal bit at row `t`, the fourfold remainder clears the dyadic
scale, the pulse payment, and the shifted threshold together. -/
def SeamTakeMarginScaleProducer : Prop :=
  ∀ (t : ℕ) (ht5 : 5 ≤ t), 9 ≤ t →
    ¬ (seamAdjacentCut t ht5).successorCarries →
      (seamAdjacentCut t ht5).terminalWeight ≤
        4 * (seamAdjacentCut t ht5).remainder +
          (seamPerturbedFamily t (by omega)).gap -
            (seamAdjacentCut t ht5).belowPulse →
        (2 ^ (t + 1) + (seamAdjacentCut t ht5).belowPulse + 4 +
          3 * 2 ^ ((t + 6) / 2) + 2 * (t - 1) : ℕ) ≤
          4 * (seamAdjacentCut t ht5).remainder

/-- **The middle producer discharges into the ceiling and take-margin
producers.**  Every middle reset enters from a right, middle, or upper
branch: the middle case is unconditional bookkeeping, the right case is
exactly the take-margin producer one row earlier, and the upper case is
exactly the ceiling producer one row earlier. -/
theorem seamMiddleResetRemainderScaleProducer_of_margins
    (hceil : SeamUpperResetChargeCeilingProducer)
    (hmarg : SeamTakeMarginScaleProducer) :
    SeamMiddleResetRemainderScaleProducer := by
  intro s hs5 hr10 hncarry hmiddle
  have hrem := seamAdjacentCut_remainder (s := s) hs5
  have hs3 : 3 ≤ s := by omega
  have hprev5 : 5 ≤ s - 1 := by omega
  have hprev3 : 3 ≤ s - 1 := by omega
  by_cases hpcarry : (seamAdjacentCut (s - 1) hprev5).successorCarries
  · -- upper predecessor: apply the ceiling at row s - 1
    have hr9 : 9 ≤ s - 1 := by omega
    have hceilPrev := hceil (s - 1) hprev5 hr9 hpcarry
    have hresetId := seamUpperBranch_remainder_add_resetCharge_eq
      (d := s - 1) hprev5 hpcarry
    have hsEq : s - 1 + 1 = s := by omega
    rw [hsEq] at hresetId
    have hexp : (s - 1 + 6) / 2 = (s + 5) / 2 := by omega
    have hpowCeil : (2 : ℕ) ^ ((s - 1) + 3) = 2 ^ (s + 2) := by
      congr 1
      omega
    have hlin : (2 : ℕ) * ((s - 1) - 1) = 2 * (s - 2) := by omega
    rw [hexp, hpowCeil, hlin] at hceilPrev
    have h4 := four_mul_two_pow_eq_pow_add s
    rw [hrem]
    omega
  · by_cases hpmid : (4 * (seamAdjacentCut (s - 1) hprev5).remainder +
        (seamPerturbedFamily (s - 1) hprev3).gap -
        (seamAdjacentCut (s - 1) hprev5).belowPulse <
      (seamAdjacentCut (s - 1) hprev5).terminalWeight)
    · -- middle predecessor: bookkeeping off the landed recurrence
      have hlow := seamMiddleReset_sourceRemainder_ge_powShift_of_middlePrev
        hprev5 hprev3 hpcarry hpmid
      have hcore : (3 * 2 ^ ((s + 5) / 2) + 2 * (s - 2) : ℕ) ≤
          4 * (2 ^ s - 2 * (s - 2)) := by
        have hchain := threshold_add_eight_le_two_pow_succ_succ s hr10
        have h4 := four_mul_two_pow_eq_pow_add s
        have hgoal : 3 * 2 ^ ((s + 5) / 2) + 2 * (s - 2) +
            8 * (s - 2) = 3 * 2 ^ ((s + 5) / 2) + 10 * (s - 2) := by
          ring
        omega
      have hfinal : (3 * 2 ^ ((s + 5) / 2) + 2 * (s - 2) : ℕ) ≤
          4 * (seamAdjacentCut s hs5).remainder := by
        have hstep :
            4 * (2 ^ s - 2 * (s - 2)) ≤
              4 * seamIntegerGreedyRemainder s :=
          Nat.mul_le_mul_left _ hlow
        have hrew : 4 * seamIntegerGreedyRemainder s =
            4 * (seamAdjacentCut s hs5).remainder := by rw [hrem]
        calc
          (3 * 2 ^ ((s + 5) / 2) + 2 * (s - 2) : ℕ) ≤
              4 * (2 ^ s - 2 * (s - 2)) := hcore
          _ ≤ 4 * seamIntegerGreedyRemainder s := hstep
          _ = 4 * (seamAdjacentCut s hs5).remainder := hrew
      exact hfinal
    · -- right predecessor: apply the take-margin producer at row s - 1
      have hpright : (seamAdjacentCut (s - 1) hprev5).terminalWeight ≤
          4 * (seamAdjacentCut (s - 1) hprev5).remainder +
            (seamPerturbedFamily (s - 1) hprev3).gap -
            (seamAdjacentCut (s - 1) hprev5).belowPulse :=
        Nat.le_of_not_gt hpmid
      have hr9 : 9 ≤ s - 1 := by omega
      have hmargPrev := hmarg (s - 1) hprev5 hr9 hpcarry hpright
      have hident := seamMiddleReset_sourceRemainder_eq_takeMargin_of_rightPrev
        hprev5 hprev3 hpcarry hpright
      have hremPrev := seamAdjacentCut_remainder (s := s - 1) hprev5
      rw [hremPrev] at hmargPrev
      have hgapPrev := seamAdjacentCut_gap_eq (s := s - 1) hprev3
      have hpowEq : (2 : ℕ) ^ ((s - 1) + 1) = 2 ^ s := by
        congr 1
        omega
      -- rewrite the producer threshold exponents to row-s forms
      have hexpM : (s - 1 + 6) / 2 = (s + 5) / 2 := by omega
      have hlinM : (2 : ℕ) * ((s - 1) - 1) = 2 * (s - 2) := by omega
      rw [hexpM, hlinM] at hmargPrev
      have hpowM : (2 : ℕ) ^ ((s - 1) + 1) = 2 ^ s := hpowEq
      rw [hpowM] at hmargPrev
      have hfinal : (3 * 2 ^ ((s + 5) / 2) + 2 * (s - 2) : ℕ) ≤
          4 * (seamAdjacentCut s hs5).remainder := by
        rw [hrem]
        omega
      exact hfinal

/-- **Full collapse:** the three margin producers imply the complete
reset square-root escape. -/
theorem seamResetSqrtEscape_of_marginProducers
    (hfloor : SeamUpperResetChargeScaleProducer)
    (hceil : SeamUpperResetChargeCeilingProducer)
    (hmarg : SeamTakeMarginScaleProducer) :
    SeamResetSqrtEscape :=
  seamResetSqrtEscape_of_scaleProducers
    (seamMiddleResetRemainderScaleProducer_of_margins hceil hmarg) hfloor

/-- Endpoint: the three margin producers give the desired
half-membership. -/
theorem half_mem_mersenneAchievementSet_of_marginProducers
    (hfloor : SeamUpperResetChargeScaleProducer)
    (hceil : SeamUpperResetChargeCeilingProducer)
    (hmarg : SeamTakeMarginScaleProducer) :
    (1 / 2 : ℝ) ∈ mersenneAchievementSet :=
  half_mem_mersenneAchievementSet_of_resetSqrtEscape
    (seamResetSqrtEscape_of_marginProducers hfloor hceil hmarg)

#print axioms seamMiddleReset_sourceRemainder_ge_powShift_of_middlePrev
#print axioms seamMiddleReset_sourceRemainder_eq_takeMargin_of_rightPrev
#print axioms seamMiddleResetRemainderScaleProducer_of_margins
#print axioms seamResetSqrtEscape_of_marginProducers
#print axioms half_mem_mersenneAchievementSet_of_marginProducers

end Erdos249257
