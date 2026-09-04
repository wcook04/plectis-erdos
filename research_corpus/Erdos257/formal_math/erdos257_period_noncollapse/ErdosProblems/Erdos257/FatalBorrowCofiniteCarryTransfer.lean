import ErdosProblems.Erdos257.FatalBorrowMidpointTransfer
import Erdos257PeriodNoncollapse.HalfCylinderMiddleCarryLowerBound

/-!
# Erdős #257: fatal midpoint rows in the cofinite carry coordinate

The fatal-borrow transfer produces an exact midpoint quotient row with
residual `R`, and identifies the deterministic seam remainder with `R + 1`.
This module sends that row into the cofinite carry coordinate used by the
last-producer analysis.

Replacing the hypothetically selected terminal rank `d` by the complete
open tail above `d` adds three units to the centred carry.  Consequently the
lazy cofinite endpoint is exactly

`4 * R + 3 - wordPulse`.

In particular, the previously separate midpoint-zero branch is the same
small-cell obstruction as the final-middle route: its centred endpoint is
`3 - wordPulse`.
-/

namespace ErdosProblems.Erdos257

open Set
open Erdos257PeriodNoncollapse
open Erdos257PeriodNoncollapse.HalfCarryReachability
open Erdos257PeriodNoncollapse.HalfCylinderIntegerGreedy

noncomputable section

/-- Exact cross-coordinate transfer from a midpoint quotient residual to the
centred carry of the lower word completed by the full open right tail. -/
theorem midpointRow_lazyCenteredCarry_eq_four_mul_residual_add_three_sub_pulse
    {d R : ℕ} (hd : 5 ≤ d)
    (hskip : ¬ mersenneWeight d ≤
      greedyMersenneRemainder (1 / 2 : ℝ) (d - 1))
    (hrow :
      localPrefixQuotient
          (insert d (halfGreedyPrefixSupport (d - 1))) (2 * d) + R =
        2 ^ (2 * d - 1)) :
    mobiusCenteredHalfCarry
        ((↑(halfGreedyPrefixSupport (d - 1)) : Set ℕ) ∪ Set.Ioi d)
        (2 * d + 1) =
      4 * (R : ℤ) + 3 -
        (wordPulse d (seamGreedyWord d).toNatWord : ℤ) := by
  let P := halfGreedyPrefixSupport (d - 1)
  obtain ⟨halignList, hrem⟩ :=
    midpointRealSkip_forces_seamAlignment_and_remainder
      (d := d) (R := R) (by omega) hskip hrow
  have halignWord : halfActualSeamWord d = seamGreedyWord d := by
    apply SeamRowWord.toList_injective
    rw [halfActualSeamWord_toList d (by omega), seamGreedyWord_toList]
    simpa [P] using halignList
  have hsupport : seamWordSupport (seamGreedyWord d) = P := by
    rw [← halignWord, seamWordSupport_halfActualSeamWord d (by omega)]
  have hP : (↑P : Set ℕ) ⊆ Set.Iio d := by
    intro e he
    exact Set.mem_Iio.mpr
      (halfGreedyPrefixSupport_pred_below d (by omega) e he).2
  have hproducer :=
    producerCarry_insert_seamBelowSupport_eq_middleCoordinate d hd
  have hcarry :=
    mobiusCenteredHalfCarry_union_Ioi_eq_producerCarry_add_three
      (↑P : Set ℕ) d (by omega) hP
  have hproducer' :
      producerCarry (insert d (↑P : Set ℕ)) d =
        4 * (R : ℤ) -
          (wordPulse d (seamGreedyWord d).toNatWord : ℤ) := by
    rw [← hsupport]
    rw [seamAdjacentCut_remainder] at hproducer
    change
      producerCarry
          (insert d (↑(seamWordSupport (seamGreedyWord d)) : Set ℕ)) d =
        4 * (seamIntegerGreedyRemainder d : ℤ) -
          (wordPulse d (seamGreedyWord d).toNatWord : ℤ) - 4 at hproducer
    rw [hproducer]
    rw [hrem]
    push_cast
    ring
  change mobiusCenteredHalfCarry ((↑P : Set ℕ) ∪ Set.Ioi d)
    (2 * d + 1) = _
  calc
    mobiusCenteredHalfCarry ((↑P : Set ℕ) ∪ Set.Ioi d) (2 * d + 1) =
        producerCarry (insert d (↑P : Set ℕ)) d + 3 := hcarry
    _ = 4 * (R : ℤ) + 3 -
        (wordPulse d (seamGreedyWord d).toNatWord : ℤ) := by
      rw [hproducer']
      ring

/-- The same midpoint row gives the exact producer carry before the open
right tail contributes its three-unit shift. -/
theorem midpointRow_seamProducerCarry_eq_four_mul_residual_sub_pulse
    {d R : ℕ} (hd : 5 ≤ d)
    (hskip : ¬ mersenneWeight d ≤
      greedyMersenneRemainder (1 / 2 : ℝ) (d - 1))
    (hrow :
      localPrefixQuotient
          (insert d (halfGreedyPrefixSupport (d - 1))) (2 * d) + R =
        2 ^ (2 * d - 1)) :
    producerCarry
        (insert d
          (↑(seamWordSupport (seamGreedyWord d)) : Set ℕ)) d =
      4 * (R : ℤ) -
        (wordPulse d (seamGreedyWord d).toNatWord : ℤ) := by
  obtain ⟨_, hrem⟩ :=
    midpointRealSkip_forces_seamAlignment_and_remainder
      (d := d) (R := R) (by omega) hskip hrow
  have hproducer :=
    producerCarry_insert_seamBelowSupport_eq_middleCoordinate d hd
  rw [seamAdjacentCut_remainder] at hproducer
  change
    producerCarry
        (insert d
          (↑(seamWordSupport (seamGreedyWord d)) : Set ℕ)) d =
      4 * (seamIntegerGreedyRemainder d : ℤ) -
        (wordPulse d (seamGreedyWord d).toNatWord : ℤ) - 4 at hproducer
  rw [hproducer, hrem]
  push_cast
  ring

/-- The zero-residual midpoint row lands at the exact lazy endpoint
`3 - wordPulse`; it is not a separate kind of obstruction. -/
theorem midpointZeroRow_lazyCenteredCarry_eq_three_sub_pulse
    {d : ℕ} (hd : 5 ≤ d)
    (hskip : ¬ mersenneWeight d ≤
      greedyMersenneRemainder (1 / 2 : ℝ) (d - 1))
    (hrow :
      localPrefixQuotient
          (insert d (halfGreedyPrefixSupport (d - 1))) (2 * d) =
        2 ^ (2 * d - 1)) :
    mobiusCenteredHalfCarry
        ((↑(halfGreedyPrefixSupport (d - 1)) : Set ℕ) ∪ Set.Ioi d)
        (2 * d + 1) =
      3 - (wordPulse d (seamGreedyWord d).toNatWord : ℤ) := by
  have h :=
    midpointRow_lazyCenteredCarry_eq_four_mul_residual_add_three_sub_pulse
      (d := d) (R := 0) hd hskip (by simpa using hrow)
  simpa using h

/-- A nonpositive selected-ancestry complement budget makes the lower
actual word completed by the open tail strictly smaller than one half. -/
theorem nonpositiveComplementBudget_forces_lazyCofiniteSeries_lt_half
    {d : ℕ} (hd : 3 ≤ d)
    (hskip : ¬ mersenneWeight d ≤
      greedyMersenneRemainder (1 / 2 : ℝ) (d - 1))
    (hfatal : halfSelectedAncestryComplementBudget d ≤ 0) :
    erdosSupportSeries 2
        ((↑(halfGreedyPrefixSupport (d - 1)) : Set ℕ) ∪ Set.Ioi d) <
      (1 / 2 : ℝ) := by
  let P := halfGreedyPrefixSupport (d - 1)
  have hPbounds : ∀ e ∈ P, 2 ≤ e ∧ e < d :=
    halfGreedyPrefixSupport_pred_below d (by omega)
  have hcomp_ne : halfSelectedAncestryComplementBudget d ≠ 0 := by
    intro hzero
    apply halfSelectedAncestryBudget_ne_neg_correctionTail d
    unfold halfSelectedAncestryComplementBudget at hzero
    linarith
  have hcomp_neg : halfSelectedAncestryComplementBudget d < 0 :=
    lt_of_le_of_ne hfatal hcomp_ne
  have hfatal' : mersenneTail d <
      greedyMersenneRemainder (1 / 2 : ℝ) d := by
    rw [halfSelectedAncestryComplementBudget_eq_tail_sub_remainder] at hcomp_neg
    linarith
  have hremEq : greedyMersenneRemainder (1 / 2 : ℝ) d =
      greedyMersenneRemainder (1 / 2 : ℝ) (d - 1) := by
    have hskip' : ¬ mersenneWeight ((d - 1) + 1) ≤
        greedyMersenneRemainder (1 / 2 : ℝ) (d - 1) := by
      simpa [Nat.sub_add_cancel (by omega : 1 ≤ d)] using hskip
    rw [show d = (d - 1) + 1 by omega, greedyMersenneRemainder_succ,
      if_neg hskip']
    simp
  have hpref : positiveMersenneSupportValue (↑P : Set ℕ) =
      (1 / 2 : ℝ) -
        greedyMersenneRemainder (1 / 2 : ℝ) (d - 1) := by
    have hrat := greedyMersenneRemainderRat_eq_sub_finiteErdosSum
      (1 / 2 : ℚ) (d - 1)
    have hratR := congrArg (fun q : ℚ ↦ (q : ℝ)) hrat
    change
      ((greedyMersenneRemainderRat (1 / 2 : ℚ) (d - 1) : ℚ) : ℝ) =
        (((1 / 2 : ℚ) -
          finiteErdosSum
            (greedyMersennePrefixRat (1 / 2 : ℚ) (d - 1)) 2 : ℚ) : ℝ) at hratR
    rw [cast_greedyMersenneRemainderRat] at hratR
    push_cast at hratR
    rw [positiveMersenneSupportValue_eq_cast_finiteErdosSum]
    change
      ((finiteErdosSum
        (greedyMersennePrefixRat (1 / 2 : ℚ) (d - 1)) 2 : ℚ) : ℝ) = _
    linarith
  rw [← positiveMersenneSupportValue_eq_erdosSupportSeries]
  change positiveMersenneSupportValue ((↑P : Set ℕ) ∪ Set.Ioi d) < _
  rw [positiveMersenneSupportValue_union_Ioi_eq_add_tail]
  · rw [hpref, ← hremEq]
    linarith
  · intro e he
    exact ⟨by have := (hPbounds e he).1; omega, (hPbounds e he).2⟩

/-- Positivity of the cofinite endpoint converts a fatal midpoint residual
into a linear upper bound on its paired boundary pulse. -/
theorem nonpositiveComplementBudget_midpointRow_forces_pulse_le
    {d R : ℕ} (hd : 5 ≤ d)
    (hskip : ¬ mersenneWeight d ≤
      greedyMersenneRemainder (1 / 2 : ℝ) (d - 1))
    (hfatal : halfSelectedAncestryComplementBudget d ≤ 0)
    (hrow :
      localPrefixQuotient
          (insert d (halfGreedyPrefixSupport (d - 1))) (2 * d) + R =
        2 ^ (2 * d - 1)) :
    wordPulse d (seamGreedyWord d).toNatWord ≤ 4 * R + 2 := by
  let P := halfGreedyPrefixSupport (d - 1)
  let B : Set ℕ := (↑P : Set ℕ) ∪ Set.Ioi d
  have hseries : erdosSupportSeries 2 B < (1 / 2 : ℝ) := by
    simpa [B, P] using
      nonpositiveComplementBudget_forces_lazyCofiniteSeries_lt_half
        (d := d) (by omega) hskip hfatal
  have hone : 1 ∉ B := by
    intro hmem
    rcases hmem with hPone | hDone
    · exact one_not_mem_halfGreedyPrefixSupport (d - 1) hPone
    · change d < 1 at hDone
      omega
  have hcofinite : Set.Ioi d ⊆ B := by
    intro e he
    exact Or.inr he
  have hcarry :=
    midpointRow_lazyCenteredCarry_eq_four_mul_residual_add_three_sub_pulse
      (d := d) (R := R) hd hskip hrow
  have hnonneg := mobiusCenteredHalfCarry_nonneg_of_supportSeries_lt_half
    B hone hseries (2 * d + 1)
  have hne := cofiniteRightTail_ne_zero_centeredEndpoint
    B d hone hseries hcofinite
  change 0 ≤ mobiusCenteredHalfCarry B (2 * d + 1) at hnonneg
  change mobiusCenteredHalfCarry B (2 * d + 1) ≠ 0 at hne
  change mobiusCenteredHalfCarry B (2 * d + 1) =
    4 * (R : ℤ) + 3 -
      (wordPulse d (seamGreedyWord d).toNatWord : ℤ) at hcarry
  rw [hcarry] at hnonneg hne
  have hpos : (0 : ℤ) <
      4 * (R : ℤ) + 3 -
        (wordPulse d (seamGreedyWord d).toNatWord : ℤ) :=
    lt_of_le_of_ne hnonneg (Ne.symm hne)
  omega

/-- At a genuinely fatal zero-residual row, analytic nonnegativity and the
cofinite zero-endpoint exclusion force the boundary pulse to be `1` or `2`.
Thus the midpoint-zero branch lands directly in the two surviving producer
cells, never in a new cell and never in the already excluded `-3` cell. -/
theorem nonpositiveComplementBudget_midpointZero_forces_pulse_one_or_two
    {d : ℕ} (hd : 13 ≤ d)
    (hskip : ¬ mersenneWeight d ≤
      greedyMersenneRemainder (1 / 2 : ℝ) (d - 1))
    (hfatal : halfSelectedAncestryComplementBudget d ≤ 0)
    (hrow :
      localPrefixQuotient
          (insert d (halfGreedyPrefixSupport (d - 1))) (2 * d) =
        2 ^ (2 * d - 1)) :
    wordPulse d (seamGreedyWord d).toNatWord = 1 ∨
      wordPulse d (seamGreedyWord d).toNatWord = 2 := by
  let P := halfGreedyPrefixSupport (d - 1)
  let B : Set ℕ := (↑P : Set ℕ) ∪ Set.Ioi d
  have hPbounds : ∀ e ∈ P, 2 ≤ e ∧ e < d :=
    halfGreedyPrefixSupport_pred_below d (by omega)
  have hcomp_ne : halfSelectedAncestryComplementBudget d ≠ 0 := by
    intro hzero
    apply halfSelectedAncestryBudget_ne_neg_correctionTail d
    unfold halfSelectedAncestryComplementBudget at hzero
    linarith
  have hcomp_neg : halfSelectedAncestryComplementBudget d < 0 :=
    lt_of_le_of_ne hfatal hcomp_ne
  have hfatal' : mersenneTail d <
      greedyMersenneRemainder (1 / 2 : ℝ) d := by
    rw [halfSelectedAncestryComplementBudget_eq_tail_sub_remainder] at hcomp_neg
    linarith
  have hremEq : greedyMersenneRemainder (1 / 2 : ℝ) d =
      greedyMersenneRemainder (1 / 2 : ℝ) (d - 1) := by
    have hskip' : ¬ mersenneWeight ((d - 1) + 1) ≤
        greedyMersenneRemainder (1 / 2 : ℝ) (d - 1) := by
      simpa [Nat.sub_add_cancel (by omega : 1 ≤ d)] using hskip
    rw [show d = (d - 1) + 1 by omega, greedyMersenneRemainder_succ,
      if_neg hskip']
    simp
  have hpref : positiveMersenneSupportValue (↑P : Set ℕ) =
      (1 / 2 : ℝ) -
        greedyMersenneRemainder (1 / 2 : ℝ) (d - 1) := by
    have hrat := greedyMersenneRemainderRat_eq_sub_finiteErdosSum
      (1 / 2 : ℚ) (d - 1)
    have hratR := congrArg (fun q : ℚ ↦ (q : ℝ)) hrat
    change
      ((greedyMersenneRemainderRat (1 / 2 : ℚ) (d - 1) : ℚ) : ℝ) =
        (((1 / 2 : ℚ) -
          finiteErdosSum
            (greedyMersennePrefixRat (1 / 2 : ℚ) (d - 1)) 2 : ℚ) : ℝ) at hratR
    rw [cast_greedyMersenneRemainderRat] at hratR
    push_cast at hratR
    rw [positiveMersenneSupportValue_eq_cast_finiteErdosSum]
    change
      ((finiteErdosSum (greedyMersennePrefixRat (1 / 2 : ℚ) (d - 1)) 2 : ℚ) : ℝ) = _
    linarith
  have hseries : erdosSupportSeries 2 B < (1 / 2 : ℝ) := by
    rw [← positiveMersenneSupportValue_eq_erdosSupportSeries]
    change positiveMersenneSupportValue
      ((↑P : Set ℕ) ∪ Set.Ioi d) < (1 / 2 : ℝ)
    rw [positiveMersenneSupportValue_union_Ioi_eq_add_tail]
    · rw [hpref, ← hremEq]
      linarith
    · intro e he
      exact ⟨by have := (hPbounds e he).1; omega, (hPbounds e he).2⟩
  have hone : 1 ∉ B := by
    intro hmem
    rcases hmem with hPone | hDone
    · exact one_not_mem_halfGreedyPrefixSupport (d - 1) hPone
    · change d < 1 at hDone
      omega
  have hcofinite : Set.Ioi d ⊆ B := by
    intro e he
    exact Or.inr he
  have hcarry := midpointZeroRow_lazyCenteredCarry_eq_three_sub_pulse
    (d := d) (by omega) hskip hrow
  have hnonneg := mobiusCenteredHalfCarry_nonneg_of_supportSeries_lt_half
    B hone hseries (2 * d + 1)
  have hne := cofiniteRightTail_ne_zero_centeredEndpoint
    B d hone hseries hcofinite
  have hpulse_le : wordPulse d (seamGreedyWord d).toNatWord ≤ 2 := by
    change 0 ≤ mobiusCenteredHalfCarry B (2 * d + 1) at hnonneg
    change mobiusCenteredHalfCarry B (2 * d + 1) ≠ 0 at hne
    change mobiusCenteredHalfCarry B (2 * d + 1) =
      3 - (wordPulse d (seamGreedyWord d).toNatWord : ℤ) at hcarry
    rw [hcarry] at hnonneg hne
    have hpos : (0 : ℤ) <
        3 - (wordPulse d (seamGreedyWord d).toNatWord : ℤ) :=
      lt_of_le_of_ne hnonneg (Ne.symm hne)
    omega
  have h2mem := (two_three_six_mem_seamGreedySupport d hd).1
  have h2even : 2 ∣ 2 * d + 2 := by omega
  have h2odd : ¬ 2 ∣ 2 * d + 1 := by omega
  have hp2 : rowPulse d 2 = 1 := by
    simp [rowPulse, h2even, h2odd]
  have hpulse_ge : 1 ≤ wordPulse d (seamGreedyWord d).toNatWord := by
    rw [wordPulse_eq_sum_seamWordSupport]
    have hsingle := Finset.single_le_sum
      (fun e _ ↦ Nat.zero_le (rowPulse d e)) h2mem
    simpa [hp2] using hsingle
  omega

/-- The second pulse alternative is impossible.  Carry `-2` forces the
phase `d = 2 (mod 3)`, but in that phase the permanently selected ranks
`2`, `3`, and `6` already contribute three pulse units. -/
theorem nonpositiveComplementBudget_midpointZero_forces_pulse_one
    {d : ℕ} (hd : 13 ≤ d)
    (hskip : ¬ mersenneWeight d ≤
      greedyMersenneRemainder (1 / 2 : ℝ) (d - 1))
    (hfatal : halfSelectedAncestryComplementBudget d ≤ 0)
    (hrow :
      localPrefixQuotient
          (insert d (halfGreedyPrefixSupport (d - 1))) (2 * d) =
        2 ^ (2 * d - 1)) :
    wordPulse d (seamGreedyWord d).toNatWord = 1 := by
  rcases nonpositiveComplementBudget_midpointZero_forces_pulse_one_or_two
      hd hskip hfatal hrow with hpulse | hpulse
  · exact hpulse
  · let P := halfGreedyPrefixSupport (d - 1)
    have hPbounds : ∀ e ∈ P, 2 ≤ e ∧ e < d :=
      halfGreedyPrefixSupport_pred_below d (by omega)
    have hcomp_ne : halfSelectedAncestryComplementBudget d ≠ 0 := by
      intro hzero
      apply halfSelectedAncestryBudget_ne_neg_correctionTail d
      unfold halfSelectedAncestryComplementBudget at hzero
      linarith
    have hcomp_neg : halfSelectedAncestryComplementBudget d < 0 :=
      lt_of_le_of_ne hfatal hcomp_ne
    have hfatal' : mersenneTail d <
        greedyMersenneRemainder (1 / 2 : ℝ) d := by
      rw [halfSelectedAncestryComplementBudget_eq_tail_sub_remainder] at hcomp_neg
      linarith
    have hremEq : greedyMersenneRemainder (1 / 2 : ℝ) d =
        greedyMersenneRemainder (1 / 2 : ℝ) (d - 1) := by
      have hskip' : ¬ mersenneWeight ((d - 1) + 1) ≤
          greedyMersenneRemainder (1 / 2 : ℝ) (d - 1) := by
        simpa [Nat.sub_add_cancel (by omega : 1 ≤ d)] using hskip
      rw [show d = (d - 1) + 1 by omega, greedyMersenneRemainder_succ,
        if_neg hskip']
      simp
    have hpref : positiveMersenneSupportValue (↑P : Set ℕ) =
        (1 / 2 : ℝ) -
          greedyMersenneRemainder (1 / 2 : ℝ) (d - 1) := by
      have hrat := greedyMersenneRemainderRat_eq_sub_finiteErdosSum
        (1 / 2 : ℚ) (d - 1)
      have hratR := congrArg (fun q : ℚ ↦ (q : ℝ)) hrat
      change
        ((greedyMersenneRemainderRat (1 / 2 : ℚ) (d - 1) : ℚ) : ℝ) =
          (((1 / 2 : ℚ) -
            finiteErdosSum
              (greedyMersennePrefixRat (1 / 2 : ℚ) (d - 1)) 2 : ℚ) : ℝ) at hratR
      rw [cast_greedyMersenneRemainderRat] at hratR
      push_cast at hratR
      rw [positiveMersenneSupportValue_eq_cast_finiteErdosSum]
      change
        ((finiteErdosSum
          (greedyMersennePrefixRat (1 / 2 : ℚ) (d - 1)) 2 : ℚ) : ℝ) = _
      linarith
    have hseries : erdosSupportSeries 2
        ((↑P : Set ℕ) ∪ Set.Ioi d) < (1 / 2 : ℝ) := by
      rw [← positiveMersenneSupportValue_eq_erdosSupportSeries]
      rw [positiveMersenneSupportValue_union_Ioi_eq_add_tail]
      · rw [hpref, ← hremEq]
        linarith
      · intro e he
        exact ⟨by have := (hPbounds e he).1; omega, (hPbounds e he).2⟩
    obtain ⟨halignList, _⟩ :=
      midpointRealSkip_forces_seamAlignment_and_remainder
        (d := d) (R := 0) (by omega) hskip (by simpa using hrow)
    have halignWord : halfActualSeamWord d = seamGreedyWord d := by
      apply SeamRowWord.toList_injective
      rw [halfActualSeamWord_toList d (by omega), seamGreedyWord_toList]
      simpa [P] using halignList
    have hsupport : seamWordSupport (seamGreedyWord d) = P := by
      rw [← halignWord, seamWordSupport_halfActualSeamWord d (by omega)]
    have hone : 1 ∉
        (↑(seamWordSupport (seamGreedyWord d)) : Set ℕ) ∪ Set.Ioi d := by
      rw [hsupport]
      intro hmem
      rcases hmem with hPone | hDone
      · exact one_not_mem_halfGreedyPrefixSupport (d - 1) hPone
      · change d < 1 at hDone
        omega
    have hseries' : erdosSupportSeries 2
        ((↑(seamWordSupport (seamGreedyWord d)) : Set ℕ) ∪ Set.Ioi d) <
        (1 / 2 : ℝ) := by
      simpa [hsupport] using hseries
    have hcell :=
      midpointRow_seamProducerCarry_eq_four_mul_residual_sub_pulse
        (d := d) (R := 0) (by omega) hskip (by simpa using hrow)
    rw [hpulse] at hcell
    norm_num at hcell
    have hmod := finalMiddleCell_neg_two_forces_mod_three_two
      d hd hone hseries' hcell
    have hmod' : (d + 1) % 3 = 0 := by omega
    have hpulseLower :=
      wordPulse_eq_three_add_seamResidualPulse236 d hd hmod'
    omega

/-- Thus a mature fatal zero row is forced into phase zero modulo three.
The other two phases already receive at least three pulse units from the
selected ranks `2`, `3`, and `6`. -/
theorem nonpositiveComplementBudget_midpointZero_forces_mod_three_zero
    {d : ℕ} (hd : 13 ≤ d)
    (hskip : ¬ mersenneWeight d ≤
      greedyMersenneRemainder (1 / 2 : ℝ) (d - 1))
    (hfatal : halfSelectedAncestryComplementBudget d ≤ 0)
    (hrow :
      localPrefixQuotient
          (insert d (halfGreedyPrefixSupport (d - 1))) (2 * d) =
        2 ^ (2 * d - 1)) :
    d % 3 = 0 := by
  have hpulse := nonpositiveComplementBudget_midpointZero_forces_pulse_one
    hd hskip hfatal hrow
  have hmem := two_three_six_mem_seamGreedySupport d hd
  by_contra hmod
  have hmodCases : d % 3 = 1 ∨ d % 3 = 2 := by omega
  rcases hmodCases with hmod1 | hmod2
  · have h2even : 2 ∣ 2 * d + 2 := by omega
    have h2odd : ¬ 2 ∣ 2 * d + 1 := by omega
    have h3odd : 3 ∣ 2 * d + 1 :=
      Nat.dvd_iff_mod_eq_zero.mpr (by omega)
    have h3even : ¬ 3 ∣ 2 * d + 2 := by
      intro hdiv
      have hzero := Nat.dvd_iff_mod_eq_zero.mp hdiv
      omega
    have hp2 : rowPulse d 2 = 1 := by
      simp [rowPulse, h2even, h2odd]
    have hp3 : rowPulse d 3 = 2 := by
      simp [rowPulse, h3even, h3odd]
    rw [wordPulse_eq_sum_seamWordSupport] at hpulse
    have hlower : rowPulse d 2 + rowPulse d 3 ≤
        ∑ e ∈ seamWordSupport (seamGreedyWord d), rowPulse d e := by
      calc
        rowPulse d 2 + rowPulse d 3 =
            ∑ e ∈ ({2, 3} : Finset ℕ), rowPulse d e := by simp
        _ ≤ ∑ e ∈ seamWordSupport (seamGreedyWord d), rowPulse d e := by
          apply Finset.sum_le_sum_of_subset_of_nonneg
          · intro e he
            simp only [Finset.mem_insert, Finset.mem_singleton] at he
            rcases he with rfl | rfl
            · exact hmem.1
            · exact hmem.2.1
          · intro e _ _
            omega
    omega
  · have hmod' : (d + 1) % 3 = 0 := by omega
    have hpulseLower :=
      wordPulse_eq_three_add_seamResidualPulse236 d hd hmod'
    omega

#print axioms midpointRow_lazyCenteredCarry_eq_four_mul_residual_add_three_sub_pulse
#print axioms midpointRow_seamProducerCarry_eq_four_mul_residual_sub_pulse
#print axioms midpointZeroRow_lazyCenteredCarry_eq_three_sub_pulse
#print axioms nonpositiveComplementBudget_forces_lazyCofiniteSeries_lt_half
#print axioms nonpositiveComplementBudget_midpointRow_forces_pulse_le
#print axioms nonpositiveComplementBudget_midpointZero_forces_pulse_one_or_two
#print axioms nonpositiveComplementBudget_midpointZero_forces_pulse_one
#print axioms nonpositiveComplementBudget_midpointZero_forces_mod_three_zero

end

end ErdosProblems.Erdos257
