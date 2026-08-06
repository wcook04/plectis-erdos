/-
Copyright (c) 2026 Will Cook. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Will Cook
-/
import ExternalVerification.Statements

/-!
# Trusted statements for the external Comparator packet

The holes in this module are intentional trusted challenge statements.  This
module is not part of the project's default Lean build.  The external
Comparator job checks that `ExternalVerification.Solution` supplies these exact
declarations, uses only the configured axiom budget, and is accepted by Lean's
kernel.
-/

namespace Erdos249257.ExternalVerification

open Module MeasureTheory

theorem finrank_totientKernelThroughLevelFamily_eq (e : ℕ) (he : 1 ≤ e) :
    finrank ℚ
      (Submodule.span ℚ (Set.range (totientKernelThroughLevelFamily e))) =
        2 ^ e + 1 := by
  sorry

theorem not_finiteDimensional_span_fullTotientKernel :
    ¬ FiniteDimensional ℚ
      (Submodule.span ℚ (Set.range fullTotientKernelFamily)) := by
  sorry

theorem volume_mersenneAchievementSet : volume mersenneAchievementSet = 1 := by
  sorry

theorem irrational_erdosSum_full_support (b : ℕ) (hb : 2 ≤ b) :
    Irrational (∑' k : ℕ, (1 : ℝ) / ((b : ℝ) ^ (k + 1) - 1)) := by
  sorry

end Erdos249257.ExternalVerification
