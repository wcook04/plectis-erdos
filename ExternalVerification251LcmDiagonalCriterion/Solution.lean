/-
Copyright (c) 2026 Will Cook. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Will Cook
-/
import ErdosProblems.Erdos251.OrderLatticeDiagonal

namespace Erdos249257.ExternalVerification251LcmDiagonalCriterion

abbrev DyadicTailRecurrence :=
  ErdosProblems.Erdos251.DyadicTailRecurrence

abbrev tailShift := ErdosProblems.Erdos251.tailShift

abbrev RatIntegral := ErdosProblems.Erdos251.RatIntegral

abbrev RealDyadicTailRecurrence :=
  ErdosProblems.Erdos251.RealDyadicTailRecurrence

abbrev realTailShift := ErdosProblems.Erdos251.realTailShift

abbrev RealIntegral := ErdosProblems.Erdos251.RealIntegral

abbrev CofinalNonintegralTailShifts :=
  ErdosProblems.Erdos251.CofinalNonintegralTailShifts

abbrev lcmDiagonalSchedule := ErdosProblems.Erdos251.lcmDiagonalSchedule

theorem notIrrationalInitial_iff_exists_integral_positive_tailShift
    {g : ℕ → ℤ} {T : ℕ → ℝ}
    (hrec : RealDyadicTailRecurrence g T) :
    ¬ Irrational (T 0) ↔
      ∃ h N : ℕ, 0 < h ∧ RealIntegral (realTailShift T h N) :=
  ErdosProblems.Erdos251.not_irrational_initial_iff_exists_integral_positive_tailShift
    hrec

theorem irrationalInitial_iff_cofinalNonintegralTailShifts
    {g : ℕ → ℤ} {T : ℕ → ℝ}
    (hrec : RealDyadicTailRecurrence g T) :
    Irrational (T 0) ↔ CofinalNonintegralTailShifts T :=
  ErdosProblems.Erdos251.irrational_initial_iff_cofinalNonintegralTailShifts hrec

theorem tailShiftIntegral_iff_orderOf_dvd
    {g : ℕ → ℤ} {T : ℕ → ℚ}
    (hrec : DyadicTailRecurrence g T) (N h : ℕ) :
    RatIntegral (tailShift T h N) ↔
      orderOf (2 : ZMod (T N).den) ∣ h :=
  ErdosProblems.Erdos251.tailShift_integral_iff_orderOf_dvd hrec N h

theorem irrationalInitial_iff_nonintegral_on_schedule
    {g : ℕ → ℤ} {T : ℕ → ℝ}
    (hrec : RealDyadicTailRecurrence g T) (s : ℕ → ℕ)
    (hpos : ∀ j, 0 < s j)
    (hdvd : ∀ h : ℕ, 0 < h → ∃ J : ℕ, ∀ j : ℕ, J ≤ j → h ∣ s j)
    (hgrow : ∀ N : ℕ, ∃ J : ℕ, ∀ j : ℕ, J ≤ j → N ≤ s j) :
    Irrational (T 0) ↔
      ∀ j : ℕ, ¬ RealIntegral (realTailShift T (s j) (s j)) :=
  ErdosProblems.Erdos251.irrational_initial_iff_nonintegral_on_schedule
    hrec s hpos hdvd hgrow

theorem irrationalInitial_iff_allLcmDiagonal_nonintegral
    {g : ℕ → ℤ} {T : ℕ → ℝ}
    (hrec : RealDyadicTailRecurrence g T) :
    Irrational (T 0) ↔
      ∀ j : ℕ,
        ¬ RealIntegral
          (realTailShift T (lcmDiagonalSchedule j) (lcmDiagonalSchedule j)) :=
  ErdosProblems.Erdos251.irrational_initial_iff_all_lcmDiagonal_nonintegral hrec

end Erdos249257.ExternalVerification251LcmDiagonalCriterion
