-- SPDX-FileCopyrightText: 2026 Will Cook
-- SPDX-License-Identifier: Apache-2.0

import ErdosProblems.Erdos1041.PaperCompleteR21.CollinearDiameterWhole

/-! The exact sharp collinear gap proposition proposed as a solved
Formal Conjectures variant. Its proof is a closed-form rewrite of the
whole-gap theorem in the public mathematical corpus. -/

namespace ErdosProblems.Erdos1041.PaperCompleteR21

open Finset
open ErdosProblems.Erdos1041.SharpCollinearChebyshev

/-- Closed-form restatement of the sharp normalized whole-gap theorem. -/
theorem exists_gap_le_sharpClosedForm {m : ℕ} (Y : Fin (m + 2) → ℝ)
    (hY : StrictMono Y) (hY0 : Y 0 = -1)
    (hY1 : Y (Fin.last (m + 1)) = 1) :
    ∃ i : Fin (m + 1), ∀ x ∈ Set.Icc (Y i.castSucc) (Y i.succ),
      |∏ j, (x - Y j)| ≤
        1 / (2 ^ ((m + 2) - 1) *
          Real.cos (Real.pi / (2 * (((m + 2 : ℕ) : ℝ)))) ^ (m + 2)) := by
  obtain ⟨i, hi⟩ := exists_gap_le_comparisonBound Y hY hY0 hY1
  refine ⟨i, ?_⟩
  intro x hx
  simpa only [comparisonBound_eq (Nat.le_add_left 2 m)] using hi x hx

#print axioms exists_gap_le_sharpClosedForm

end ErdosProblems.Erdos1041.PaperCompleteR21
