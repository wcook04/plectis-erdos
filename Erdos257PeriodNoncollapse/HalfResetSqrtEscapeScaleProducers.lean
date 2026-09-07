import Erdos257PeriodNoncollapse.HalfCylinderResetSqrtEscape

/-!
# Scale producers behind reset square-root escape

The reset square-root escape `SeamResetSqrtEscape` asks
`2 ^ (r + 5) < seamResetDeviation r ^ 2` at every actual upper-or-middle
reset row `r >= 10`.  This module splits that single obligation into two
independent branch-local arithmetic producers with one uniform integer
threshold `3 * 2 ^ ((r + 5) / 2)`.

Exact branch identities used (all previously landed):

* middle branch: `seamMiddleBranch_nextRemainder_add_belowPulse_eq` gives
  `seamResetDeviation r = 4 * R_r - belowPulse`, and the universal pulse
  bound `belowPulse <= 2 * (r - 2)` shows escape can fail only when
  `4 * R_r` itself is below the threshold;
* upper branch: `seamUpperBranch_remainder_add_resetCharge_eq` gives
  `seamResetDeviation r = -(4 * overshoot + abovePulse)`, so escape at an
  upper reset is literally a lower bound on the reset charge.

The factor `3` absorbs both parities of `r + 5`: for `k = (r + 5) / 2`
one always has `2 * k >= r + 4`, hence
`(3 * 2 ^ k) ^ 2 = 9 * 4 ^ k >= 9 * 2 ^ (r + 4) > 2 ^ (r + 5)`.

Both producers hold empirically with exponential slack: the audited
return-time band gives `floor(log2 |dev_r|) = r - L` with `L <= 12`
through row 2500 (`check_seam_reset_crossing.py` receipt), far above the
half-row threshold.  No theorem here proves either producer
unconditionally; the module only replaces one diffuse anti-concentration
statement by two concrete monotone lower-bound targets that the existing
backward pullback identities can attack.
-/

namespace Erdos257PeriodNoncollapse

open HalfCylinderIntegerGreedy

/-- Twice the halved row index always covers the row minus three. -/
private theorem four_le_two_mul_half_addfive (s : ℕ) :
    s + 4 ≤ 2 * ((s + 5) / 2) := by
  have h1 := Nat.div_add_mod (s + 5) 2
  have h2 := Nat.mod_lt (s + 5) (by norm_num : (0 : ℕ) < 2)
  omega

/-- Uniform parity-absorbing squaring helper, natural-number form:
three times the half-row power always squares strictly above the full-row
power. -/
private theorem nat_sq_gt_of_three_mul_scale {k s n : ℕ}
    (hsk : s + 4 ≤ 2 * k) (hn : 3 * 2 ^ k ≤ n) :
    2 ^ (s + 5) < n ^ 2 := by
  have hm : 3 * 2 ^ k * (3 * 2 ^ k) ≤ n * n := Nat.mul_le_mul hn hn
  have hk : 2 ^ k * 2 ^ k = 2 ^ (2 * k) := by
    have h : 2 ^ k * 2 ^ k = 2 ^ (k + k) := (pow_add 2 k k).symm
    rw [h, Nat.two_mul]
  have h2 : 3 * 2 ^ k * (3 * 2 ^ k) = 9 * 2 ^ (2 * k) := by
    calc
      3 * 2 ^ k * (3 * 2 ^ k) = 2 ^ k * 2 ^ k * 9 := by ring
      _ = 2 ^ (2 * k) * 9 := by rw [hk]
      _ = 9 * 2 ^ (2 * k) := Nat.mul_comm _ _
  have h3 : 2 ^ (s + 5) ≤ 2 ^ (2 * k + 3) :=
    Nat.pow_le_pow_right (by norm_num) (by omega)
  have h4 : 2 ^ (2 * k + 3) < 9 * 2 ^ (2 * k) := by
    have hsplit : (2 : ℕ) ^ (2 * k + 3) = 8 * 2 ^ (2 * k) := by
      rw [pow_add]
      norm_num
      exact Nat.mul_comm _ _
    rw [hsplit]
    have hzpos : (0 : ℕ) < 2 ^ (2 * k) := by positivity
    exact Nat.mul_lt_mul_of_pos_right (by norm_num : (8 : ℕ) < 9) hzpos
  calc
    2 ^ (s + 5) ≤ 2 ^ (2 * k + 3) := h3
    _ < 9 * 2 ^ (2 * k) := h4
    _ = 3 * 2 ^ k * (3 * 2 ^ k) := h2.symm
    _ ≤ n ^ 2 := by rw [pow_two]; exact hm

/-- Exact signed deviation identity on a middle branch:
`dev_s = 4 * R_s - belowPulse`. -/
theorem middleResetDeviation_eq
    {s : ℕ} (hs5 : 5 ≤ s)
    (hncarry : ¬ (seamAdjacentCut s hs5).successorCarries)
    (hmiddle :
      4 * (seamAdjacentCut s hs5).remainder +
            (seamPerturbedFamily s (by omega)).gap -
            (seamAdjacentCut s hs5).belowPulse <
          (seamAdjacentCut s hs5).terminalWeight) :
    seamResetDeviation s =
      ((4 * (seamAdjacentCut s hs5).remainder : ℕ) : ℤ) -
        ((seamAdjacentCut s hs5).belowPulse : ℤ) := by
  have hadd :=
    seamMiddleBranch_nextRemainder_add_belowPulse_eq hs5 hncarry hmiddle
  have hrem := seamAdjacentCut_remainder hs5
  unfold seamResetDeviation
  have hz := congrArg (fun n : ℕ ↦ (n : ℤ)) hadd
  have hremZ := congrArg (fun n : ℕ ↦ (n : ℤ)) hrem
  push_cast at hz hremZ ⊢
  omega

/-- **Middle scale producer implies square-root escape.**  If the fourfold
remainder clears the uniform threshold plus the maximal pulse, the middle
landing deviation escapes the half-row window. -/
theorem seamResetSqrtEscape_middle_of_scale
    {s : ℕ} (hs5 : 5 ≤ s) (hr10 : 10 ≤ s)
    (hncarry : ¬ (seamAdjacentCut s hs5).successorCarries)
    (hmiddle :
      4 * (seamAdjacentCut s hs5).remainder +
            (seamPerturbedFamily s (by omega)).gap -
            (seamAdjacentCut s hs5).belowPulse <
          (seamAdjacentCut s hs5).terminalWeight)
    (hscale :
      (3 * 2 ^ ((s + 5) / 2) + 2 * (s - 2) : ℕ) ≤
        4 * (seamAdjacentCut s hs5).remainder) :
    ((2 ^ (s + 5) : ℕ) : ℤ) < seamResetDeviation s ^ 2 := by
  have hpulse :=
    (seamPerturbedFamily s (by omega)).pulse_le
      (seamAdjacentCut s hs5).below
  change (seamAdjacentCut s hs5).belowPulse ≤ 2 * (s - 2) at hpulse
  have hrem := seamAdjacentCut_remainder hs5
  rw [hrem] at hscale
  have hdev := middleResetDeviation_eq hs5 hncarry hmiddle
  have hnat : (3 * 2 ^ ((s + 5) / 2) : ℕ) ≤
      (seamResetDeviation s).natAbs := by
    omega
  have hscaled := nat_sq_gt_of_three_mul_scale
    (four_le_two_mul_half_addfive s) hnat
  calc
    ((2 ^ (s + 5) : ℕ) : ℤ) <
        (((seamResetDeviation s).natAbs ^ 2 : ℕ) : ℤ) :=
      by exact_mod_cast hscaled
    _ = seamResetDeviation s ^ 2 := by simp

/-- Exact signed deviation identity on an upper branch:
`dev_d = -(4 * overshoot + abovePulse)`. -/
theorem upperResetDeviation_eq
    {d : ℕ} (hd5 : 5 ≤ d)
    (hcarry : (seamAdjacentCut d hd5).successorCarries) :
    seamResetDeviation d =
      -(((4 * (seamAdjacentCut d hd5).overshoot : ℕ) +
          (seamAdjacentCut d hd5).abovePulse : ℕ) : ℤ) := by
  have hadd := seamUpperBranch_remainder_add_resetCharge_eq hd5 hcarry
  unfold seamResetDeviation
  have hz := congrArg (fun n : ℕ ↦ (n : ℤ)) hadd
  push_cast at hz ⊢
  omega

/-- **Upper scale producer implies square-root escape.**  A reset charge
above the uniform threshold is exactly the escape. -/
theorem seamResetSqrtEscape_upper_of_scale
    {d : ℕ} (hd5 : 5 ≤ d) (hr10 : 10 ≤ d)
    (hcarry : (seamAdjacentCut d hd5).successorCarries)
    (hscale :
      (3 * 2 ^ ((d + 5) / 2) : ℕ) ≤
        4 * (seamAdjacentCut d hd5).overshoot +
          (seamAdjacentCut d hd5).abovePulse) :
    ((2 ^ (d + 5) : ℕ) : ℤ) < seamResetDeviation d ^ 2 := by
  have hdev := upperResetDeviation_eq hd5 hcarry
  have hnat : (3 * 2 ^ ((d + 5) / 2) : ℕ) ≤
      (seamResetDeviation d).natAbs := by
    omega
  have hscaled := nat_sq_gt_of_three_mul_scale
    (four_le_two_mul_half_addfive d) hnat
  calc
    ((2 ^ (d + 5) : ℕ) : ℤ) <
        (((seamResetDeviation d).natAbs ^ 2 : ℕ) : ℤ) :=
      by exact_mod_cast hscaled
    _ = seamResetDeviation d ^ 2 := by simp

/-- The named all-depth producer at middle resets: the fourfold source
remainder clears the uniform threshold plus maximal pulse. -/
def SeamMiddleResetRemainderScaleProducer : Prop :=
  ∀ (s : ℕ) (hs5 : 5 ≤ s), 10 ≤ s →
    ¬ (seamAdjacentCut s hs5).successorCarries →
      4 * (seamAdjacentCut s hs5).remainder +
            (seamPerturbedFamily s (by omega)).gap -
            (seamAdjacentCut s hs5).belowPulse <
          (seamAdjacentCut s hs5).terminalWeight →
        (3 * 2 ^ ((s + 5) / 2) + 2 * (s - 2) : ℕ) ≤
          4 * (seamAdjacentCut s hs5).remainder

/-- The named all-depth producer at upper resets: the reset charge
`4 * overshoot + abovePulse` clears the uniform threshold. -/
def SeamUpperResetChargeScaleProducer : Prop :=
  ∀ (d : ℕ) (hd5 : 5 ≤ d), 10 ≤ d →
    (seamAdjacentCut d hd5).successorCarries →
      (3 * 2 ^ ((d + 5) / 2) : ℕ) ≤
        4 * (seamAdjacentCut d hd5).overshoot +
          (seamAdjacentCut d hd5).abovePulse

/-- The two scale producers jointly imply the full reset square-root
escape. -/
theorem seamResetSqrtEscape_of_scaleProducers
    (hmid : SeamMiddleResetRemainderScaleProducer)
    (hupp : SeamUpperResetChargeScaleProducer) :
    SeamResetSqrtEscape := by
  intro r hr5 hr10 hreset
  rcases hreset with hcarry | ⟨hncarry, hmiddle⟩
  · exact seamResetSqrtEscape_upper_of_scale hr5 hr10 hcarry
      (hupp r hr5 hr10 hcarry)
  · exact seamResetSqrtEscape_middle_of_scale hr5 hr10 hncarry hmiddle
      (hmid r hr5 hr10 hncarry hmiddle)

/-- Endpoint: the two scale producers give the desired half-membership. -/
theorem half_mem_mersenneAchievementSet_of_scaleProducers
    (hmid : SeamMiddleResetRemainderScaleProducer)
    (hupp : SeamUpperResetChargeScaleProducer) :
    (1 / 2 : ℝ) ∈ mersenneAchievementSet :=
  half_mem_mersenneAchievementSet_of_resetSqrtEscape
    (seamResetSqrtEscape_of_scaleProducers hmid hupp)

/-! ## Boundary forms consumed by backward pullback arguments

These restate the thresholds on the post-reset landing remainder, the
quantity the nested pullback identities control directly.  The upper form
is an exact equivalence because the landing remainder and the charge sum
to the dyadic gap exactly.  The middle form is only an implication from
the stronger remainder-scale producer to the landing form: the pulse
slack prevents reversing it. -/

/-- Upper boundary form: charge scale is equivalent to the landing
remainder sitting a full threshold below the dyadic gap. -/
theorem seamUpperReset_landingScale_iff_chargeScale
    {d : ℕ} (hd5 : 5 ≤ d)
    (hcarry : (seamAdjacentCut d hd5).successorCarries) :
    seamIntegerGreedyRemainder (d + 1) + 3 * 2 ^ ((d + 5) / 2) ≤
        2 ^ (d + 1) ↔
      (3 * 2 ^ ((d + 5) / 2) : ℕ) ≤
        4 * (seamAdjacentCut d hd5).overshoot +
          (seamAdjacentCut d hd5).abovePulse := by
  have hadd := seamUpperBranch_remainder_add_resetCharge_eq hd5 hcarry
  constructor
  · intro hland
    omega
  · intro hcharge
    omega

/-- Middle boundary form: the remainder-scale producer implies the landing
remainder sits a full threshold above its own dyadic boundary.  The
converse fails because the pulse may absorb up to `2 * (s - 2)`. -/
theorem seamMiddleReset_landingScale_of_remainderScale
    {s : ℕ} (hs5 : 5 ≤ s)
    (hncarry : ¬ (seamAdjacentCut s hs5).successorCarries)
    (hmiddle :
      4 * (seamAdjacentCut s hs5).remainder +
            (seamPerturbedFamily s (by omega)).gap -
            (seamAdjacentCut s hs5).belowPulse <
          (seamAdjacentCut s hs5).terminalWeight)
    (hscale :
      (3 * 2 ^ ((s + 5) / 2) + 2 * (s - 2) : ℕ) ≤
        4 * (seamAdjacentCut s hs5).remainder) :
    2 ^ (s + 1) + 3 * 2 ^ ((s + 5) / 2) ≤
      seamIntegerGreedyRemainder (s + 1) := by
  have hpulse :=
    (seamPerturbedFamily s (by omega)).pulse_le
      (seamAdjacentCut s hs5).below
  change (seamAdjacentCut s hs5).belowPulse ≤ 2 * (s - 2) at hpulse
  have hadd :=
    seamMiddleBranch_nextRemainder_add_belowPulse_eq hs5 hncarry hmiddle
  rw [seamAdjacentCut_remainder hs5] at hscale
  omega

/-- Exact landing form of a right-branch take margin.  The full threshold
paid at row `t` is neither stronger nor weaker than the resulting remainder
at row `t+1`; the additive right recurrence identifies them term for term.
This is the correct replacement for the false claim that every right landing
is itself dyadic-large. -/
theorem seamRightBranch_landingScale_iff_takeMarginScale
    {t T : ℕ} (ht5 : 5 ≤ t)
    (hncarry : ¬ (seamAdjacentCut t ht5).successorCarries)
    (hright : (seamAdjacentCut t ht5).terminalWeight ≤
      4 * (seamAdjacentCut t ht5).remainder +
        (seamPerturbedFamily t (by omega)).gap -
        (seamAdjacentCut t ht5).belowPulse) :
    T ≤ seamIntegerGreedyRemainder (t + 1) ↔
      2 ^ (t + 1) + (seamAdjacentCut t ht5).belowPulse + 4 + T ≤
        4 * seamIntegerGreedyRemainder t := by
  have hadd :=
    seamRightBranch_remainder_add_charge_eq ht5 hncarry hright
  omega

/-- Exact landing form of the upper-reset charge ceiling.  Since the next
remainder and reset charge partition `2^(d+1)`, a ceiling on four times the
charge is exactly a lower bound on four times the landing remainder. -/
theorem seamUpperReset_landingScale_iff_chargeCeiling
    {d T : ℕ} (hd5 : 5 ≤ d)
    (hcarry : (seamAdjacentCut d hd5).successorCarries) :
    T ≤ 4 * seamIntegerGreedyRemainder (d + 1) ↔
      4 * (4 * (seamAdjacentCut d hd5).overshoot +
          (seamAdjacentCut d hd5).abovePulse) + T ≤
        2 ^ (d + 3) := by
  have hadd := seamUpperBranch_remainder_add_resetCharge_eq hd5 hcarry
  have hpow : (2 : ℕ) ^ (d + 3) = 4 * 2 ^ (d + 1) := by
    rw [show d + 3 = (d + 1) + 2 by omega, pow_add]
    ring
  rw [hpow]
  omega

#print axioms middleResetDeviation_eq
#print axioms seamResetSqrtEscape_middle_of_scale
#print axioms upperResetDeviation_eq
#print axioms seamResetSqrtEscape_upper_of_scale
#print axioms seamResetSqrtEscape_of_scaleProducers
#print axioms half_mem_mersenneAchievementSet_of_scaleProducers
#print axioms seamRightBranch_landingScale_iff_takeMarginScale
#print axioms seamUpperReset_landingScale_iff_chargeCeiling

end Erdos257PeriodNoncollapse
