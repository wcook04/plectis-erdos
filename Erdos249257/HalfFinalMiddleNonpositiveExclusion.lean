import Erdos249257.CampbellShiftSynchronization
import Erdos249257.HalfCylinderLastProducerContradiction
import Erdos249257.HalfResetSqrtEscapeScaleProducers

/-!
# Nonpositive final-middle deviations are impossible

The generic producer-carry socket used the coarse estimate
`mersenneGap d < 8 / 4^(d+1)`.  The sharper already-landed bound
`mersenneGap d < (1/4)^d` lowers the required negative carry from `-8` to
`-4`.  Since a middle reset with nonpositive landing deviation has
terminal-augmented producer carry at most `-4`, it cannot be the final reset
before an all-right seam tail.
-/

namespace Erdos249257

open Set Filter
open HalfCylinderIntegerGreedy

noncomputable section

/-- Four negative carry units already dominate the complete Mersenne gap.
This is the sharp constant needed for nonpositive middle deviations. -/
theorem producerCarry_le_neg_four_forces_gap_margin
    (A : Set ℕ) (d : ℕ)
    (hone : 1 ∉ A)
    (hA : A ⊆ Set.Iic d)
    (hd : 3 ≤ d)
    (hcarry : producerCarry A d ≤ -4) :
    (1 : ℝ) / 2 + mersenneGap d < erdosSupportSeries 2 A := by
  have hid := producerCarry_residual_identity A d hone hA
  have htail := binaryCoeffTail_nonneg (supportCoeff A) (2 * d + 2)
  have hcarryR : (producerCarry A d : ℝ) ≤ -4 := by
    exact_mod_cast hcarry
  have hnum : (4 : ℝ) ≤
      binaryCoeffTail (supportCoeff A) (2 * d + 2) -
        (producerCarry A d : ℝ) := by
    linarith
  have hpowEq :
      (2 : ℝ) ^ (2 * d + 2) = (4 : ℝ) ^ (d + 1) := by
    rw [show 2 * d + 2 = 2 * (d + 1) by omega, pow_mul]
    norm_num
  have hexcess :
      erdosSupportSeries 2 A - (1 : ℝ) / 2 =
        (binaryCoeffTail (supportCoeff A) (2 * d + 2) -
          (producerCarry A d : ℝ)) / (4 : ℝ) ^ (d + 1) := by
    calc
      erdosSupportSeries 2 A - (1 : ℝ) / 2 =
          -((1 : ℝ) / 2 - erdosSupportSeries 2 A) := by ring
      _ = -(((producerCarry A d : ℝ) -
            binaryCoeffTail (supportCoeff A) (2 * d + 2)) /
          (2 : ℝ) ^ (2 * d + 2)) := by rw [hid]
      _ = (binaryCoeffTail (supportCoeff A) (2 * d + 2) -
            (producerCarry A d : ℝ)) / (4 : ℝ) ^ (d + 1) := by
        rw [hpowEq]
        ring
  have hden : (0 : ℝ) < (4 : ℝ) ^ (d + 1) := by positivity
  have hlower : ((1 : ℝ) / 4) ^ d ≤
      erdosSupportSeries 2 A - (1 : ℝ) / 2 := by
    rw [hexcess]
    have hdiv := div_le_div_of_nonneg_right hnum hden.le
    calc
      ((1 : ℝ) / 4) ^ d = 4 / (4 : ℝ) ^ (d + 1) := by
        rw [div_pow, one_pow, pow_succ]
        field_simp
      _ ≤ (binaryCoeffTail (supportCoeff A) (2 * d + 2) -
            (producerCarry A d : ℝ)) / (4 : ℝ) ^ (d + 1) := hdiv
  have hgap := mersenneGap_lt_quarterPow hd
  linarith

/-- Replacing the terminal Mersenne weight by its entire later tail remains
above one half whenever the augmented carry is at most `-4`. -/
theorem producerCarry_le_neg_four_forces_belowTail_gt_half
    (A : Set ℕ) (d : ℕ) (base : ℝ)
    (hone : 1 ∉ A)
    (hA : A ⊆ Set.Iic d)
    (hd : 3 ≤ d)
    (hcarry : producerCarry A d ≤ -4)
    (hdecomp : erdosSupportSeries 2 A = base + mersenneWeight d) :
    (1 : ℝ) / 2 < base + mersenneTail d := by
  have hmargin := producerCarry_le_neg_four_forces_gap_margin
    A d hone hA hd hcarry
  rw [hdecomp] at hmargin
  unfold mersenneGap at hmargin
  linarith

/-- A genuine middle reset followed only by right extensions has strictly
positive signed landing deviation. -/
theorem finalMiddleResetDeviation_pos
    (D : ℕ) (hD13 : 13 ≤ D)
    (hncarry : ¬ (seamAdjacentCut D (by omega)).successorCarries)
    (hmiddle :
      4 * (seamAdjacentCut D (by omega)).remainder +
            (seamPerturbedFamily D (by omega)).gap -
            (seamAdjacentCut D (by omega)).belowPulse <
          (seamAdjacentCut D (by omega)).terminalWeight)
    (hright : ∀ s : ℕ, D + 1 ≤ s →
      seamGreedyWord (s + 1) = (seamGreedyWord s).extend true) :
    0 < seamResetDeviation D := by
  classical
  let hs5 : 5 ≤ D := by omega
  let K := seamAdjacentCut D hs5
  let u : Finset ℕ := seamWordSupport K.below
  let A : Set ℕ := insert D (↑u : Set ℕ)
  have hword : seamGreedyWord (D + 1) = K.below.extend false := by
    exact seamGreedyWord_succ_eq_middleBranch D hs5 hncarry hmiddle
  have hu : ∀ e ∈ u, 2 ≤ e ∧ e < D := by
    intro e he
    exact seamWordSupport_below (by simpa [u] using he)
  have hbase : seamWordSupport (seamGreedyWord (D + 1)) =
      u ∪ Finset.Ico (D + 1) (D + 1) := by
    rw [hword, seamWordSupport_extend_false (by omega)]
    simp [u]
  have hlower := prefix_add_mersenneTail_lt_half_of_eventually_right
    (S := D + 1) (D := D) (u := u)
    (by omega) (by omega) hu hright hbase
  have hone : 1 ∉ A := by
    exact one_not_mem_insert_seamWordSupport hs5 K.below
  have hA : A ⊆ Set.Iic D := by
    exact insert_seamWordSupport_subset_Iic K.below
  have hDnotu : D ∉ u := by
    intro hDu
    exact (Nat.lt_irrefl D) (hu D hDu).2
  have hcarryEq : producerCarry A D = seamResetDeviation D - 4 := by
    have hproducer :=
      producerCarry_insert_seamBelowSupport_eq_middleCoordinate D hs5
    have hdev := middleResetDeviation_eq hs5 hncarry hmiddle
    change producerCarry
      (insert D (↑(seamWordSupport K.below) : Set ℕ)) D = _
    push_cast at hdev
    rw [hproducer, hdev]
  by_contra hnotpos
  have hdevNonpos : seamResetDeviation D ≤ 0 := le_of_not_gt hnotpos
  have hcarryLe : producerCarry A D ≤ -4 := by
    rw [hcarryEq]
    omega
  have hdecomp : erdosSupportSeries 2 A =
      positiveMersenneSupportValue (↑u : Set ℕ) + mersenneWeight D := by
    rw [← positiveMersenneSupportValue_eq_erdosSupportSeries]
    simpa [A, add_comm] using
      (positiveMersenneSupportValue_insert hDnotu)
  have hforced := producerCarry_le_neg_four_forces_belowTail_gt_half
    A D (positiveMersenneSupportValue (↑u : Set ℕ))
    hone hA (by omega) hcarryLe hdecomp
  linarith

/-- Equivalent remainder-side form of the final-middle sign law. -/
theorem finalMiddle_nextRemainder_gt_pow
    (D : ℕ) (hD13 : 13 ≤ D)
    (hncarry : ¬ (seamAdjacentCut D (by omega)).successorCarries)
    (hmiddle :
      4 * (seamAdjacentCut D (by omega)).remainder +
            (seamPerturbedFamily D (by omega)).gap -
            (seamAdjacentCut D (by omega)).belowPulse <
          (seamAdjacentCut D (by omega)).terminalWeight)
    (hright : ∀ s : ℕ, D + 1 ≤ s →
      seamGreedyWord (s + 1) = (seamGreedyWord s).extend true) :
    2 ^ (D + 1) < seamIntegerGreedyRemainder (D + 1) := by
  have hdev := finalMiddleResetDeviation_pos D hD13 hncarry hmiddle hright
  unfold seamResetDeviation at hdev
  have hdev' : ((2 ^ (D + 1) : ℕ) : ℤ) <
      (seamIntegerGreedyRemainder (D + 1) : ℤ) := by omega
  exact_mod_cast hdev'

#print axioms producerCarry_le_neg_four_forces_gap_margin
#print axioms producerCarry_le_neg_four_forces_belowTail_gt_half
#print axioms finalMiddleResetDeviation_pos
#print axioms finalMiddle_nextRemainder_gt_pow

end

end Erdos249257
