-- SPDX-FileCopyrightText: 2026 Will Cook
-- SPDX-License-Identifier: Apache-2.0
import Mathlib

namespace ErdosProblems.Erdos1041.PaperCompleteR21
open Finset

-- Signature copied from FC PR6576 head 43874b729c11b65783050871577a22f9093362a8.
theorem exists_gap_le_sharpClosedForm {m : ℕ} (Y : Fin (m + 2) → ℝ)
    (hY : StrictMono Y) (hY0 : Y 0 = -1)
    (hY1 : Y (Fin.last (m + 1)) = 1) :
    ∃ i : Fin (m + 1), ∀ x ∈ Set.Icc (Y i.castSucc) (Y i.succ),
      |∏ j, (x - Y j)| ≤
        1 / (2 ^ ((m + 2) - 1) *
          Real.cos (Real.pi / (2 * (((m + 2 : ℕ) : ℝ)))) ^ (m + 2)) := by
  sorry

end ErdosProblems.Erdos1041.PaperCompleteR21
