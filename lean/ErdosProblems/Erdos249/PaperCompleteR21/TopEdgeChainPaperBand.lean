import Erdos249257.TotientActualLcmTopEdgeStaircase
import Erdos249257.TotientActualLcmOrbitNonintegrality
import ErdosProblems.Erdos249.PaperCompleteR21.TopEdgeCorridorAndSeparation

/-! Item 1 of `prop:te-chain` exactly as the long #249 paper displays it.

The paper prints the adjacent-suffix midband as the two-sided condition
`2H + m + 2 ≤ suffix residue(2^a) 0 m ≤ 2^m - (2H + m + 2)`, while the tree's
`PowerTwoAdjacentSuffixMidbandSupply` uses the strictly narrower upper endpoint
`2^m - (2H + m + 3)`.  This file defines the paper's band literally, as
`PaperAdjacentSuffixMidbandSupply`, and proves every clause `prop:te-chain`
asserts about item 1 for that wider predicate:

* the pointwise dichotomy `G_a(0,m,m) ∨ G_a(0,m+1,m)` from the wide band;
* the wide band supplies `PowerTwoActualLcmTopEdgeResidueGapSupply`
  (the "first four imply the upper-endpoint condition" clause);
* the wide band suffices for irrationality of `S = ∑ φ(n)/2^n`;
* the inter-item implications of the proposition, with item 1 read in the
  paper's wide form: half-word band → item 1, flexible magnitude → item 1,
  item 1 → residue-gap supply, and the two implications not involving item 1.

The extra endpoint room the tree spends is genuinely unnecessary.  In the
contradiction branch the two failed gaps give `x > 2^m - (2H+m+2)` and
`y > 2^m - (2H+m+3)`, and both cases already close against the wide band:
if `x ≤ y` then `y - x ≥ 2H+m+2` pushes `y ≥ 2^m`, and if `y < x` then the
wide upper bound gives `x ≥ y + (2H+m+2) ≥ 2^m`.  So the narrow endpoint is
not load-bearing, and the paper's display is correct as printed.

Here `H = H(2^a) = periodLcm (2^a)` and
`suffix residue(2^a) 0 m = diagonalAdjacentSuffixResidue (2^a) 0 m`. -/

noncomputable section

namespace ErdosProblems.Erdos249.PaperCompleteR21

open Erdos249257
open Erdos249257.TotientTailPeriodKiller
open Erdos249257.DiagonalFreshLossBridge
open Erdos249257.DiagonalFreshLossBridge.PowerTwoOddWindowAffine

/-! ### The paper's item 1 -/

/-- **Item 1 of `prop:te-chain`, exactly as displayed.**  The two-sided band on
the adjacent-suffix residue at one candidate depth `m`, with the paper's upper
endpoint `2^m - (2H + m + 2)`. -/
def PaperAdjacentSuffixMidbandSupply : Prop :=
  ∀ a₀ : ℕ, ∃ a m : ℕ, a₀ ≤ a ∧ 8 ≤ a ∧
    m + 1 + (a + 6) < 2 * 2 ^ a ∧
    ((2 * periodLcm (2 ^ a) + m + 3 : ℕ) : ℤ) < (2 : ℤ) ^ m ∧
    ((2 * periodLcm (2 ^ a) + m + 2 : ℕ) : ℤ) ≤
      diagonalAdjacentSuffixResidue (2 ^ a) 0 m ∧
    diagonalAdjacentSuffixResidue (2 ^ a) 0 m ≤
      (2 : ℤ) ^ m - ((2 * periodLcm (2 ^ a) + m + 2 : ℕ) : ℤ)

/-- The paper's item 1, written out. -/
theorem paperTeChain_item_one_unfolded :
    PaperAdjacentSuffixMidbandSupply ↔
      ∀ a₀ : ℕ, ∃ a m : ℕ, a₀ ≤ a ∧ 8 ≤ a ∧
        m + 1 + (a + 6) < 2 * 2 ^ a ∧
        ((2 * periodLcm (2 ^ a) + m + 3 : ℕ) : ℤ) < (2 : ℤ) ^ m ∧
        ((2 * periodLcm (2 ^ a) + m + 2 : ℕ) : ℤ) ≤
          diagonalAdjacentSuffixResidue (2 ^ a) 0 m ∧
        diagonalAdjacentSuffixResidue (2 ^ a) 0 m ≤
          (2 : ℤ) ^ m - ((2 * periodLcm (2 ^ a) + m + 2 : ℕ) : ℤ) :=
  Iff.rfl

/-- The tree's narrower band is the special case of the paper's band, so every
producer of the narrow band produces the paper's band. -/
theorem paperAdjacentSuffixMidbandSupply_of_adjacentSuffixMidband
    (hsupply : PowerTwoAdjacentSuffixMidbandSupply) :
    PaperAdjacentSuffixMidbandSupply := by
  intro a₀
  obtain ⟨a, m, ha₀, ha8, hshort, hroom, hlo, hhi⟩ := hsupply a₀
  refine ⟨a, m, ha₀, ha8, hshort, hroom, hlo, ?_⟩
  have hstep :
      ((2 * periodLcm (2 ^ a) + m + 2 : ℕ) : ℤ) ≤
        ((2 * periodLcm (2 ^ a) + m + 3 : ℕ) : ℤ) :=
    Nat.cast_le.mpr (by omega)
  exact hhi.trans (sub_le_sub_left hstep ((2 : ℤ) ^ m))

/-! ### The wide band still forces a one-sided top-edge gap -/

/-- **One-sided adjacent-gap geometry at the paper's endpoint.**  The wide band
`2H+m+2 ≤ d ≤ 2^m - (2H+m+2)` on the adjacent-suffix displacement already gives
an upper top-edge gap at one of the two adjacent depths `m`, `m+1`.  The extra
unit of room in `PowerTwoAdjacentSuffixMidbandSupply` is not used. -/
theorem topEdgeResidueGap_or_of_paperAdjacentSuffixMidband
    {a m : ℕ}
    (hroom :
      ((2 * periodLcm (2 ^ a) + m + 3 : ℕ) : ℤ) < (2 : ℤ) ^ m)
    (hlo :
      ((2 * periodLcm (2 ^ a) + m + 2 : ℕ) : ℤ) ≤
        diagonalAdjacentSuffixResidue (2 ^ a) 0 m)
    (hhi :
      diagonalAdjacentSuffixResidue (2 ^ a) 0 m ≤
        (2 : ℤ) ^ m -
          ((2 * periodLcm (2 ^ a) + m + 2 : ℕ) : ℤ)) :
    ActualLcmTopEdgeResidueGap a 0 m m ∨
      ActualLcmTopEdgeResidueGap a 0 (m + 1) m := by
  let t : ℕ := 2 ^ a
  let H : ℕ := periodLcm t
  let M : ℤ := (2 : ℤ) ^ m
  let x : ℤ := diagonalSuffixResidue t 0 m
  let y : ℤ := diagonalSuffixResidue t 1 m
  let d : ℤ := diagonalAdjacentSuffixResidue t 0 m
  let E₀ : ℤ := ((2 * H + m + 2 : ℕ) : ℤ)
  let E₁ : ℤ := ((2 * H + m + 3 : ℕ) : ℤ)
  have hEsucc : E₁ = E₀ + 1 := by
    dsimp [E₀, E₁]
    push_cast
    ring
  have hroom' : E₁ < M := by simpa [t, H, M, E₁] using hroom
  have hlo' : E₀ ≤ d := by simpa [t, H, d, E₀] using hlo
  have hhi' : d ≤ M - E₀ := by simpa [t, H, M, d, E₀] using hhi
  have hx0 : 0 ≤ x := by
    unfold x diagonalSuffixResidue
    exact Int.emod_nonneg _ (by positivity)
  have hxM : x < M := by
    unfold x diagonalSuffixResidue M
    exact Int.emod_lt_of_pos _ (by positivity)
  have hy0 : 0 ≤ y := by
    unfold y diagonalSuffixResidue
    exact Int.emod_nonneg _ (by positivity)
  have hyM : y < M := by
    unfold y diagonalSuffixResidue M
    exact Int.emod_lt_of_pos _ (by positivity)
  have hd : d = (y - x) % M := by
    rfl
  have hd_of_le (hxy : x ≤ y) : d = y - x := by
    rw [hd, Int.emod_eq_of_lt] <;> omega
  have hd_of_gt (hyx : y < x) : d = M + y - x := by
    rw [hd, show y - x = (M + y - x) - M by ring,
      Int.sub_emod_right, Int.emod_eq_of_lt] <;> omega
  have hroom₀ : E₀ < M := by
    dsimp [E₀, E₁, H] at hroom' ⊢
    omega
  by_cases hxGap : x ≤ M - E₀
  · left
    apply (actualLcmTopEdgeResidueGap_iff_terminal a 0 m m).2
    refine ⟨le_rfl, ?_, ?_⟩
    · simpa [t, H, M, E₀] using hroom₀
    · rw [show m - m = 0 by omega]
      simp only [Nat.add_zero]
      have hxWord :
          diagonalSuffixResidue (2 ^ a) 0 m =
            windowDiscrepancy (periodLcm (2 ^ a))
              (periodLcm (2 ^ a)) m % 2 ^ m := by
        simpa using diagonalSuffixResidue_eq_windowDiscrepancy (2 ^ a) 0 m
      rw [← hxWord]
      simpa [t, H, M, x, E₀] using hxGap
  by_cases hyGap : y ≤ M - E₁
  · right
    apply (actualLcmTopEdgeResidueGap_iff_terminal a 0 (m + 1) m).2
    refine ⟨by omega, ?_, ?_⟩
    · simpa [t, H, M, E₁] using hroom'
    · rw [show m + 1 - m = 1 by omega]
      simp only [Nat.add_zero]
      have hyWord :
          diagonalSuffixResidue (2 ^ a) 1 m =
            windowDiscrepancy (periodLcm (2 ^ a))
              (periodLcm (2 ^ a) + 1) m % 2 ^ m := by
        simpa using diagonalSuffixResidue_eq_windowDiscrepancy (2 ^ a) 1 m
      rw [← hyWord]
      simpa [t, H, M, y, E₁, Nat.add_assoc] using hyGap
  exfalso
  have hxTop : M - E₀ < x := lt_of_not_ge hxGap
  have hyTop : M - E₁ < y := lt_of_not_ge hyGap
  by_cases hxy : x ≤ y
  · rw [hd_of_le hxy] at hlo'
    omega
  · rw [hd_of_gt (lt_of_not_ge hxy)] at hhi'
    omega

/-! ### What the proposition asserts about item 1 -/

/-- **Item 1, in the paper's wide form, implies the upper-endpoint condition.**
This is the item-1 half of the "the first four imply
`PowerTwoActualLcmTopEdgeResidueGapSupply`" clause. -/
theorem powerTwoActualLcmTopEdgeResidueGapSupply_of_paperAdjacentSuffixMidband
    (hsupply : PaperAdjacentSuffixMidbandSupply) :
    PowerTwoActualLcmTopEdgeResidueGapSupply := by
  intro a₀
  obtain ⟨a, m, ha₀, ha8, hshort, hroom, hlo, hhi⟩ := hsupply a₀
  rcases topEdgeResidueGap_or_of_paperAdjacentSuffixMidband hroom hlo hhi with
    hgap | hgap
  · exact ⟨a, m, m, ha₀, ha8, by omega, hgap⟩
  · exact ⟨a, m + 1, m, ha₀, ha8, by simpa [Nat.add_assoc] using hshort, hgap⟩

/-- **Item 1, in the paper's wide form, suffices for irrationality.** -/
theorem irrational_of_paperAdjacentSuffixMidbandSupply
    (hsupply : PaperAdjacentSuffixMidbandSupply) :
    Irrational (∑' n : ℕ, (Nat.totient n : ℝ) / 2 ^ n) :=
  irrational_totientSeries_of_topEdgeResidueGapSupply
    (powerTwoActualLcmTopEdgeResidueGapSupply_of_paperAdjacentSuffixMidband hsupply)

/-- The half-word band produces the paper's wide item 1. -/
theorem paperAdjacentSuffixMidbandSupply_of_oddGuardTopEdgeHalfWordBand
    (hsupply : PowerTwoOddGuardTopEdgeHalfWordBandSupply) :
    PaperAdjacentSuffixMidbandSupply :=
  paperAdjacentSuffixMidbandSupply_of_adjacentSuffixMidband
    (powerTwoAdjacentSuffixMidbandSupply_of_oddGuardTopEdgeHalfWordBand hsupply)

/-- The flexible magnitude condition produces the paper's wide item 1. -/
theorem paperAdjacentSuffixMidbandSupply_of_flexibleActualTopEdgeMagnitude
    (hsupply : PowerTwoFlexibleActualTopEdgeMagnitudeSupply) :
    PaperAdjacentSuffixMidbandSupply :=
  paperAdjacentSuffixMidbandSupply_of_adjacentSuffixMidband
    (powerTwoAdjacentSuffixMidbandSupply_of_flexibleActualTopEdgeMagnitude hsupply)

/-! ### `prop:te-chain` with item 1 read as the paper prints it -/

/-- **Each of the five conditions suffices for irrationality**, item 1 taken in
the paper's wide form. -/
theorem paperTeChain_five_sufficient_for_irrationality :
    (PaperAdjacentSuffixMidbandSupply →
        Irrational (∑' n : ℕ, (Nat.totient n : ℝ) / 2 ^ n)) ∧
      (PowerTwoOddGuardTopEdgeHalfWordBandSupply →
        Irrational (∑' n : ℕ, (Nat.totient n : ℝ) / 2 ^ n)) ∧
      (PowerTwoActualFinalTopEdgeMagnitudeSupply →
        Irrational (∑' n : ℕ, (Nat.totient n : ℝ) / 2 ^ n)) ∧
      (PowerTwoFlexibleActualTopEdgeMagnitudeSupply →
        Irrational (∑' n : ℕ, (Nat.totient n : ℝ) / 2 ^ n)) ∧
      (PowerTwoFlexibleActualTerminalDominanceSupply →
        Irrational (∑' n : ℕ, (Nat.totient n : ℝ) / 2 ^ n)) :=
  ⟨irrational_of_paperAdjacentSuffixMidbandSupply,
    irrational_totientSeries_of_oddGuardTopEdgeHalfWordBandSupply,
    irrational_totientSeries_of_actualFinalTopEdgeMagnitudeSupply,
    irrational_totientSeries_of_flexibleActualTopEdgeMagnitudeSupply,
    irrational_totientSeries_of_flexibleActualTerminalDominanceSupply⟩

/-- **The first four imply the upper-endpoint condition**, item 1 taken in the
paper's wide form. -/
theorem paperTeChain_first_four_imply_topEdgeSupply :
    (PaperAdjacentSuffixMidbandSupply → PowerTwoActualLcmTopEdgeResidueGapSupply) ∧
      (PowerTwoOddGuardTopEdgeHalfWordBandSupply →
        PowerTwoActualLcmTopEdgeResidueGapSupply) ∧
      (PowerTwoActualFinalTopEdgeMagnitudeSupply →
        PowerTwoActualLcmTopEdgeResidueGapSupply) ∧
      (PowerTwoFlexibleActualTopEdgeMagnitudeSupply →
        PowerTwoActualLcmTopEdgeResidueGapSupply) :=
  ⟨powerTwoActualLcmTopEdgeResidueGapSupply_of_paperAdjacentSuffixMidband,
    fun h => powerTwoActualLcmTopEdgeResidueGapSupply_of_paperAdjacentSuffixMidband
      (paperAdjacentSuffixMidbandSupply_of_oddGuardTopEdgeHalfWordBand h),
    fun h => powerTwoActualLcmTopEdgeResidueGapSupply_of_paperAdjacentSuffixMidband
      (paperAdjacentSuffixMidbandSupply_of_oddGuardTopEdgeHalfWordBand
        (topEdgeHalfWordBandSupply_iff_actualFinalCenteredMagnitudeSupply.mpr h)),
    fun h => powerTwoActualLcmTopEdgeResidueGapSupply_of_paperAdjacentSuffixMidband
      (paperAdjacentSuffixMidbandSupply_of_flexibleActualTopEdgeMagnitude h)⟩

/-- **The proved implications among the conditions**, item 1 taken in the
paper's wide form: midband → residue-gap, half-word band → midband, final
magnitude ⇔ half-word band, flexible magnitude → midband, final magnitude →
flexible magnitude. -/
theorem paperTeChain_relations :
    (PaperAdjacentSuffixMidbandSupply → PowerTwoActualLcmTopEdgeResidueGapSupply) ∧
      (PowerTwoOddGuardTopEdgeHalfWordBandSupply →
        PaperAdjacentSuffixMidbandSupply) ∧
      (PowerTwoOddGuardTopEdgeHalfWordBandSupply ↔
        PowerTwoActualFinalTopEdgeMagnitudeSupply) ∧
      (PowerTwoFlexibleActualTopEdgeMagnitudeSupply →
        PaperAdjacentSuffixMidbandSupply) ∧
      (PowerTwoActualFinalTopEdgeMagnitudeSupply →
        PowerTwoFlexibleActualTopEdgeMagnitudeSupply) :=
  ⟨powerTwoActualLcmTopEdgeResidueGapSupply_of_paperAdjacentSuffixMidband,
    paperAdjacentSuffixMidbandSupply_of_oddGuardTopEdgeHalfWordBand,
    topEdgeHalfWordBandSupply_iff_actualFinalCenteredMagnitudeSupply,
    paperAdjacentSuffixMidbandSupply_of_flexibleActualTopEdgeMagnitude,
    flexibleActualTopEdgeMagnitudeSupply_of_actualFinal⟩

/-- **The fifth gives nonintegrality directly by the endpoint identity.** -/
theorem paperTeChain_fifth_gives_nonintegrality :
    PowerTwoFlexibleActualTerminalDominanceSupply →
      PowerTwoActualLcmOrbitNonintegralitySupply :=
  actualLcmOrbitNonintegralitySupply_of_flexibleActualTerminalDominance

end ErdosProblems.Erdos249.PaperCompleteR21

end

#print axioms ErdosProblems.Erdos249.PaperCompleteR21.paperTeChain_item_one_unfolded
#print axioms ErdosProblems.Erdos249.PaperCompleteR21.paperAdjacentSuffixMidbandSupply_of_adjacentSuffixMidband
#print axioms ErdosProblems.Erdos249.PaperCompleteR21.topEdgeResidueGap_or_of_paperAdjacentSuffixMidband
#print axioms ErdosProblems.Erdos249.PaperCompleteR21.powerTwoActualLcmTopEdgeResidueGapSupply_of_paperAdjacentSuffixMidband
#print axioms ErdosProblems.Erdos249.PaperCompleteR21.irrational_of_paperAdjacentSuffixMidbandSupply
#print axioms ErdosProblems.Erdos249.PaperCompleteR21.paperAdjacentSuffixMidbandSupply_of_oddGuardTopEdgeHalfWordBand
#print axioms ErdosProblems.Erdos249.PaperCompleteR21.paperAdjacentSuffixMidbandSupply_of_flexibleActualTopEdgeMagnitude
#print axioms ErdosProblems.Erdos249.PaperCompleteR21.paperTeChain_five_sufficient_for_irrationality
#print axioms ErdosProblems.Erdos249.PaperCompleteR21.paperTeChain_first_four_imply_topEdgeSupply
#print axioms ErdosProblems.Erdos249.PaperCompleteR21.paperTeChain_relations
#print axioms ErdosProblems.Erdos249.PaperCompleteR21.paperTeChain_fifth_gives_nonintegrality
#print axioms ErdosProblems.Erdos249.PaperCompleteR21.teChain_item_two_unfolded
#print axioms ErdosProblems.Erdos249.PaperCompleteR21.teChain_item_three_unfolded
#print axioms ErdosProblems.Erdos249.PaperCompleteR21.teChain_item_four_unfolded
#print axioms ErdosProblems.Erdos249.PaperCompleteR21.teChain_item_five_unfolded
