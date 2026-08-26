import ErdosProblems.Erdos257.FatalBorrowCofiniteCarryTransfer

/-!
# Erdős #257: the complete positive fatal-residual packet

The fatal selected-ancestry branch is now split without returning to the
large rational remainder denominator.  Residual zero is handled by the unit
seam-remainder ancestry.  A positive residual is simultaneously

* square-root small;
* smaller than the seam rank and bounded by the seam support card;
* linearly dominant over the paired boundary pulse; and
* forced to cross every sufficiently long finite multiplicity window.

This module packages those independent constraints in one theorem so the
remaining positive branch can be attacked as a single quotient/defect
lattice problem.
-/

namespace ErdosProblems.Erdos257

open Set
open Erdos257PeriodNoncollapse
open Erdos257PeriodNoncollapse.HalfCylinderIntegerGreedy
open Erdos257PeriodNoncollapse.HalfCylinderFiniteShadow

noncomputable section

/-- A mature fatal borrow is either the exact zero row, or one positive
integer residual satisfying all currently proved first-shell, cofinite-carry,
square-root, and second-shell constraints. -/
theorem nonpositiveComplementBudget_forces_zero_or_positiveResidualPacket
    {d : ℕ} (hd : 13 ≤ d)
    (hskip : ¬ mersenneWeight d ≤
      greedyMersenneRemainder (1 / 2 : ℝ) (d - 1))
    (hfatal : halfSelectedAncestryComplementBudget d ≤ 0) :
    ∃ R : ℕ,
      localPrefixQuotient
          (insert d (halfGreedyPrefixSupport (d - 1))) (2 * d) + R =
          2 ^ (2 * d - 1) ∧
        (R = 0 ∨
          (1 ≤ R ∧
            R < 2 * Nat.sqrt (2 * d) + 3 ∧
            R ≤ (seamWordSupport (seamGreedyWord d)).card ∧
            seamIntegerGreedyRemainder d = R + 1 ∧
            seamIntegerGreedyRemainder d < d ∧
            wordPulse d (seamGreedyWord d).toNatWord ≤ 4 * R + 2 ∧
            producerCarry
                (insert d
                  (↑(seamWordSupport (seamGreedyWord d)) : Set ℕ)) d =
              4 * (R : ℤ) -
                (wordPulse d (seamGreedyWord d).toNatWord : ℤ) ∧
            ∀ L : ℕ,
              2 * Nat.sqrt (2 * d + L) + 3 ≤ 2 ^ L →
                (R - 1) * 2 ^ L <
                  finiteCoeffWindowNumerator
                    (↑(insert d
                      (halfGreedyPrefixSupport (d - 1))) : Set ℕ)
                    (2 * d) L)) := by
  obtain ⟨R, hrow, _, _⟩ :=
    nonpositiveComplementBudget_forces_midpointRow
      (d := d) (by omega) hskip hfatal
  refine ⟨R, hrow, ?_⟩
  by_cases hRzero : R = 0
  · exact Or.inl hRzero
  · right
    have hR : 1 ≤ R := by omega
    have hD := halfGreedyPrefixSupport_pred_below d (by omega)
    have hcross :=
      insert_halfGreedyPrefixSupport_gt_half_of_realSkip (by omega) hskip
    have hsqrt :=
      aboveMidpointResidual_lt_two_natSqrt_add_three_of_real_crossing
        (D := halfGreedyPrefixSupport (d - 1)) (d := d) (R := R)
        (by omega) hD hrow hcross
    have hcard := midpointRealSkip_forces_residual_le_seamSupportCard
      (d := d) (R := R) (by omega) hskip hrow
    have halign := midpointRealSkip_forces_seamAlignment_and_remainder
      (d := d) (R := R) (by omega) hskip hrow
    have hsmall := midpointRealSkip_forces_seamRemainder_lt_rank
      (d := d) (R := R) (by omega) hskip hrow
    have hpulse :=
      nonpositiveComplementBudget_midpointRow_forces_pulse_le
        (d := d) (R := R) (by omega) hskip hfatal hrow
    have hproducer :=
      midpointRow_seamProducerCarry_eq_four_mul_residual_sub_pulse
        (d := d) (R := R) (by omega) hskip hrow
    refine ⟨hR, hsqrt, hcard, halign.2, hsmall, hpulse, hproducer, ?_⟩
    intro L hlook
    exact
      (midpointRealSkip_forces_seamSecondShellCertificate_autoCross
        (d := d) (R := R) (L := L) (by omega) hR hskip hrow hlook).2.2

#print axioms nonpositiveComplementBudget_forces_zero_or_positiveResidualPacket

end

end ErdosProblems.Erdos257
