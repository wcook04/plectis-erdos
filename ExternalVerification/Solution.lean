/-
Copyright (c) 2026 Will Cook. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Will Cook
-/
import ExternalVerification.Statements
import Erdos249257.GreedyAchievementSet
import Erdos249257.TotientMahlerDefect

/-!
# Solutions for the external Comparator packet

These thin wrappers expose four existing results through the Mathlib-only
statement vocabulary in `ExternalVerification.Statements`.  They add no new
mathematical claim: each proof is a definitional transport from the declaration
owned by the public claim registry.
-/

namespace Erdos249257.ExternalVerification

open Module MeasureTheory

theorem finrank_totientKernelThroughLevelFamily_eq (e : ℕ) (he : 1 ≤ e) :
    finrank ℚ
      (Submodule.span ℚ (Set.range (totientKernelThroughLevelFamily e))) =
        2 ^ e + 1 := by
  simpa [totientKernelThroughLevelFamily, totientKernelSeq,
    Erdos249257.totientKernelThroughLevelFamily,
    Erdos249257.totientKernelSeq] using
    Erdos249257.finrank_totientKernelThroughLevelFamily_eq e he

theorem not_finiteDimensional_span_fullTotientKernel :
    ¬ FiniteDimensional ℚ
      (Submodule.span ℚ (Set.range fullTotientKernelFamily)) := by
  simpa [fullTotientKernelFamily, totientKernelSeq,
    Erdos249257.fullTotientKernelFamily,
    Erdos249257.totientKernelSeq] using
    Erdos249257.not_finiteDimensional_span_fullTotientKernel

theorem volume_mersenneAchievementSet : volume mersenneAchievementSet = 1 := by
  simpa [mersenneAchievementSet, positiveMersenneSupportValue, mersenneWeight,
    Erdos249257.mersenneAchievementSet,
    Erdos249257.positiveMersenneSupportValue,
    Erdos249257.mersenneWeight] using
    Erdos249257.volume_mersenneAchievementSet

theorem irrational_erdosSum_full_support (b : ℕ) (hb : 2 ≤ b) :
    Irrational (∑' k : ℕ, (1 : ℝ) / ((b : ℝ) ^ (k + 1) - 1)) := by
  simpa using Erdos249257.irrational_erdosSum_full_support b hb

end Erdos249257.ExternalVerification
