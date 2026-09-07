import ErdosProblems.Erdos257.HalfCounterexampleFrontier
import ErdosProblems.Erdos257.SelectedAncestryTailSurvival
import ErdosProblems.Erdos257.SelectedFirstWindowCharge

/-!
# Erdős #257: fatal-borrow transfer to midpoint quotient rows

The exact selected-ancestry endpoint says that failure can occur only when
the complement budget becomes nonpositive.  The denominator of the real
remainder is too large for a useful separation argument, so this module
changes coordinates instead: a nonpositive complement budget at an actual
skip forces a negative integral full-shell margin, hence an exact midpoint
quotient row.

The transfer is unconditional.  It does not exclude the resulting row and
therefore does not settle Erdős #257.  Its purpose is to make the remaining
obstruction live entirely in the quotient/defect coordinates where the seam
and second-shell machinery apply.
-/

namespace ErdosProblems.Erdos257

open Erdos257PeriodNoncollapse
open Erdos257PeriodNoncollapse.HalfCylinderFiniteShadow
open Erdos257PeriodNoncollapse.HalfCylinderIntegerGreedy

/-- A fatal complement-budget state at an actual skip forces an exact
target-zero midpoint quotient row.  The same row inherits exact seam-word
alignment and identifies its residual with the seam remainder. -/
theorem nonpositiveComplementBudget_forces_midpointRow
    {d : ℕ} (hd : 3 ≤ d)
    (hskip : ¬ mersenneWeight d ≤
      greedyMersenneRemainder (1 / 2 : ℝ) (d - 1))
    (hfatal : halfSelectedAncestryComplementBudget d ≤ 0) :
    ∃ R : ℕ,
      localPrefixQuotient
          (insert d (halfGreedyPrefixSupport (d - 1))) (2 * d) + R =
          2 ^ (2 * d - 1) ∧
        stemBits d (halfGreedyPrefixSupport (d - 1)) =
          integerGreedyBits (seamWeights d) (seamSubsetTarget d) ∧
        seamIntegerGreedyRemainder d = R + 1 := by
  have hbudget_ne :
      (halfSelectedAncestryBudgetRat d : ℝ) ≠
        -mersenneCorrectionTail d :=
    halfSelectedAncestryBudget_ne_neg_correctionTail d
  have hbudget_le :
      (halfSelectedAncestryBudgetRat d : ℝ) ≤
        -mersenneCorrectionTail d := by
    unfold halfSelectedAncestryComplementBudget at hfatal
    linarith
  have hbudget_lt :
      (halfSelectedAncestryBudgetRat d : ℝ) <
        -mersenneCorrectionTail d :=
    lt_of_le_of_ne hbudget_le hbudget_ne
  have hbudget_neg : (halfSelectedAncestryBudgetRat d : ℝ) < 0 := by
    have hcorr := mersenneCorrectionTail_pos d
    linarith
  have hmarginId :=
    greedyHalfFrozenMargin_fullShell_cast_eq_selectedBudget_sub_tail
      d (by omega) hskip
  have htail : 0 ≤ binaryCoeffTail
      (supportCoeff
        (↑(halfGreedyPrefixSupport (d - 1)) : Set ℕ)) (2 * d) :=
    binaryCoeffTail_nonneg _ _
  have hmarginReal :
      (greedyHalfFrozenMargin (d - 1) d : ℝ) < 0 := by
    rw [hmarginId]
    have hpow : 0 < (2 : ℝ) ^ (2 * d) := by positivity
    nlinarith
  have hmargin : greedyHalfFrozenMargin (d - 1) d < 0 := by
    exact_mod_cast hmarginReal
  obtain ⟨R, hrow⟩ :=
    exists_midpointRow_of_fullShell_neg (d := d) (by omega) hmargin
  obtain ⟨halign, hrem⟩ :=
    midpointRealSkip_forces_seamAlignment_and_remainder
      hd hskip hrow
  exact ⟨R, hrow, halign, hrem⟩

/-- A fatal borrow is therefore either the zero-residual midpoint row or it
produces the actual-orbit two-shell incidence certificate.  The first branch
is an exact local row; the second is the logarithmic-lookahead obstruction
used by the existing seam packet. -/
theorem nonpositiveComplementBudget_forces_midpointZero_or_secondShell
    {d L : ℕ} (hd : 3 ≤ d)
    (hskip : ¬ mersenneWeight d ≤
      greedyMersenneRemainder (1 / 2 : ℝ) (d - 1))
    (hfatal : halfSelectedAncestryComplementBudget d ≤ 0)
    (hlook : 2 * Nat.sqrt (2 * d + L) + 3 ≤ 2 ^ L) :
    ∃ R : ℕ,
      localPrefixQuotient
          (insert d (halfGreedyPrefixSupport (d - 1))) (2 * d) + R =
          2 ^ (2 * d - 1) ∧
        (R = 0 ∨
          (stemBits d (halfGreedyPrefixSupport (d - 1)) =
              integerGreedyBits (seamWeights d) (seamSubsetTarget d) ∧
            seamIntegerGreedyRemainder d = R + 1 ∧
            (R - 1) * 2 ^ L <
              finiteCoeffWindowNumerator
                (↑(insert d (halfGreedyPrefixSupport (d - 1))) : Set ℕ)
                (2 * d) L)) := by
  obtain ⟨R, hrow, _halign, _hrem⟩ :=
    nonpositiveComplementBudget_forces_midpointRow hd hskip hfatal
  refine ⟨R, hrow, ?_⟩
  by_cases hR : R = 0
  · exact Or.inl hR
  · right
    exact midpointRealSkip_forces_seamSecondShellCertificate_autoCross
      hd (by omega) hskip hrow hlook

#print axioms nonpositiveComplementBudget_forces_midpointRow
#print axioms nonpositiveComplementBudget_forces_midpointZero_or_secondShell

end ErdosProblems.Erdos257
