import Erdos257PeriodNoncollapse.FourNinthsDiagonalMarginProducer

/-!
# Exact accumulated history of the four-ninths diagonal

The local margin countermodel shows that a diagonal remainder cannot be
treated as free state data.  This module records the missing reachability
constraint exactly: the executable remainder is the base-four accumulation
of every earlier pulse, divisor load, and selected dyadic coin.

This identity does not yet prove the selected-landing margin.  It replaces
the falsified local proof search by a history-sensitive arithmetic target.
-/

namespace Erdos257PeriodNoncollapse

open Finset

/-- Base-four accumulation of a zero-indexed increment sequence. -/
def fourNinthsWeightedHistory (q : ℕ → ℤ) : ℕ → ℤ
  | 0 => 0
  | d + 1 => 4 * fourNinthsWeightedHistory q d + q d

/-- The selected dyadic coin charged at the transition from `d` to `d+1`.
The proposition is decidable arithmetically; the explicit classical wrapper
keeps that implementation choice out of all later statements. -/
noncomputable def fourNinthsDiagonalHistoryCoinCharge (d : ℕ) : ℤ := by
  classical
  exact if FourNinthsDiagonalTakesAt d then
    ((2 ^ (d + 1) + 1 : ℕ) : ℤ)
  else 0

/-- The exact signed increment at the transition from depth `d` to `d+1`,
before its multiplication by future powers of four. -/
noncomputable def fourNinthsDiagonalHistoryIncrement (d : ℕ) : ℤ :=
  (fourNinthsPairPulse (d + 1) : ℤ) -
    (fourNinthsDiagonalLoad
      (fourNinthsDiagonalState d) (d + 1) : ℤ) -
    fourNinthsDiagonalHistoryCoinCharge d

/-- Every executable transition is affine with the signed history increment.
This packages the take and skip branches into one recurrence. -/
theorem fourNinthsDiagonalState_rho_succ_eq_historyIncrement (d : ℕ) :
    (fourNinthsDiagonalState (d + 1)).rho =
      4 * (fourNinthsDiagonalState d).rho +
        fourNinthsDiagonalHistoryIncrement d := by
  classical
  by_cases htake : FourNinthsDiagonalTakesAt d
  · rw [fourNinthsDiagonalState_rho_succ_of_takes d htake]
    simp [fourNinthsDiagonalHistoryIncrement,
      fourNinthsDiagonalHistoryCoinCharge, htake]
    ring
  · have hnotTake : ¬
        (((2 ^ (d + 1) + 1 : ℕ) : ℤ) ≤
          4 * (fourNinthsDiagonalState d).rho +
            (fourNinthsPairPulse (d + 1) : ℤ) -
            (fourNinthsDiagonalLoad
              (fourNinthsDiagonalState d) (d + 1) : ℤ)) := by
      simpa [FourNinthsDiagonalTakesAt] using htake
    have hnotTake' : ¬
        ((2 : ℤ) ^ (d + 1) <
          4 * (fourNinthsDiagonalState d).rho +
            (fourNinthsPairPulse (d + 1) : ℤ) -
            (fourNinthsDiagonalLoad
              (fourNinthsDiagonalState d) (d + 1) : ℤ)) := by
      push_cast at hnotTake
      omega
    rw [fourNinthsDiagonalState]
    simp [fourNinthsDiagonalStep, fourNinthsDiagonalHistoryIncrement,
      fourNinthsDiagonalHistoryCoinCharge,
      fourNinthsDiagonalState_bits_length, htake, hnotTake']
    ring

/-- **Exact reachability identity.**  The remainder at every depth is the
base-four accumulated history of the actual signed transition increments. -/
theorem fourNinthsDiagonalState_rho_eq_weightedHistory (d : ℕ) :
    (fourNinthsDiagonalState d).rho =
      fourNinthsWeightedHistory fourNinthsDiagonalHistoryIncrement d := by
  induction d with
  | zero => rfl
  | succ d ih =>
      rw [fourNinthsDiagonalState_rho_succ_eq_historyIncrement,
        fourNinthsWeightedHistory, ih]

/-- Closed-form unrolling of the base-four accumulator. -/
theorem fourNinthsWeightedHistory_eq_sum (q : ℕ → ℤ) (d : ℕ) :
    fourNinthsWeightedHistory q d =
      ∑ j ∈ Finset.range d, (4 : ℤ) ^ (d - 1 - j) * q j := by
  induction d with
  | zero => simp [fourNinthsWeightedHistory]
  | succ d ih =>
      rw [fourNinthsWeightedHistory, ih]
      rw [show ∑ j ∈ Finset.range (d + 1),
            (4 : ℤ) ^ (d + 1 - 1 - j) * q j =
          (∑ j ∈ Finset.range d,
            (4 : ℤ) ^ (d + 1 - 1 - j) * q j) +
              (4 : ℤ) ^ (d + 1 - 1 - d) * q d by
        rw [Finset.sum_range_succ]]
      rw [Finset.mul_sum]
      have htail : d + 1 - 1 - d = 0 := by omega
      rw [htail, pow_zero, one_mul]
      apply congrArg (fun z : ℤ => z + q d)
      apply Finset.sum_congr rfl
      intro j hj
      have hjd : j < d := Finset.mem_range.mp hj
      have hexponent : d + 1 - 1 - j = (d - 1 - j) + 1 := by omega
      rw [hexponent, pow_succ']
      ring

/-- The executable remainder as one literal weighted finite sum over all
earlier actual pulses, loads, and selected coins. -/
theorem fourNinthsDiagonalState_rho_eq_historySum (d : ℕ) :
    (fourNinthsDiagonalState d).rho =
      ∑ j ∈ Finset.range d,
        (4 : ℤ) ^ (d - 1 - j) *
          ((fourNinthsPairPulse (j + 1) : ℤ) -
            (fourNinthsDiagonalLoad
              (fourNinthsDiagonalState j) (j + 1) : ℤ) -
            fourNinthsDiagonalHistoryCoinCharge j) := by
  rw [fourNinthsDiagonalState_rho_eq_weightedHistory,
    fourNinthsWeightedHistory_eq_sum]
  rfl

/-- The selected-rank producer written entirely against the accumulated
history.  This is the source-current form that rules out detached remainder
substitutions such as the local countermodel. -/
theorem fourNinthsSelectedLandingRankProducer_iff_historyEndpoint :
    FourNinthsSelectedLandingRankProducer ↔
      ∀ d : ℕ, FourNinthsDiagonalTakesAt d →
        (((2 ^ (d + 1) + 1 : ℕ) : ℤ) + ((d + 1 : ℕ) : ℤ) ≤
          4 * fourNinthsWeightedHistory
                fourNinthsDiagonalHistoryIncrement d +
            (fourNinthsPairPulse (d + 1) : ℤ) -
            (fourNinthsDiagonalLoad
              (fourNinthsDiagonalState d) (d + 1) : ℤ)) := by
  rw [fourNinthsSelectedLandingRankProducer_iff_endpointInequality]
  constructor
  · intro h d htake
    simpa only [fourNinthsDiagonalState_rho_eq_weightedHistory] using
      h d htake
  · intro h d htake
    simpa only [fourNinthsDiagonalState_rho_eq_weightedHistory] using
      h d htake

/-- Failure of the stronger producer is exactly an actual selected transition
whose accumulated-history endpoint falls in the rank-wide bad window above
the dyadic coin. -/
theorem fourNinths_not_selectedLandingRankProducer_iff_exists_historyBadWindow :
    ¬ FourNinthsSelectedLandingRankProducer ↔
      ∃ d : ℕ, FourNinthsDiagonalTakesAt d ∧
        4 * fourNinthsWeightedHistory
              fourNinthsDiagonalHistoryIncrement d +
            (fourNinthsPairPulse (d + 1) : ℤ) -
            (fourNinthsDiagonalLoad
              (fourNinthsDiagonalState d) (d + 1) : ℤ) <
          (((2 ^ (d + 1) + 1 : ℕ) : ℤ) + ((d + 1 : ℕ) : ℤ)) := by
  rw [fourNinthsSelectedLandingRankProducer_iff_historyEndpoint]
  push Not
  rfl

#print axioms fourNinthsDiagonalState_rho_succ_eq_historyIncrement
#print axioms fourNinthsDiagonalState_rho_eq_weightedHistory
#print axioms fourNinthsWeightedHistory_eq_sum
#print axioms fourNinthsDiagonalState_rho_eq_historySum
#print axioms fourNinthsSelectedLandingRankProducer_iff_historyEndpoint
#print axioms fourNinths_not_selectedLandingRankProducer_iff_exists_historyBadWindow

end Erdos257PeriodNoncollapse
