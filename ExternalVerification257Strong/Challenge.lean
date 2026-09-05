/-
Copyright (c) 2026 Will Cook. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Will Cook
-/
import ExternalVerification257Strong.Statements

/-! Trusted challenge declarations; intentional holes occur only here. -/

namespace Erdos249257.ExternalVerification.Strong257


theorem irrational_erdosSupportSeries_of_summable_reciprocal
    (b : ℕ) (A : Set ℕ) (hb : 2 ≤ b) (hA : A.Infinite)
    (hsum : Summable (reciprocalSupportTerm A)) :
    Irrational (erdosSupportSeries b A) := by
  sorry

theorem irrational_erdosSupportSeries_of_orthogonalPetalBouquet_allBase
    (b : ℕ) (hb : 2 ≤ b) {A : Set ℕ} (hB : OrthogonalPetalBouquet A) :
    Irrational (erdosSupportSeries b A) := by
  sorry

theorem mem_iff_greedyBinaryDefect_sqrt_windows {x : ℝ} (hx : 0 ≤ x) :
    x ∈ mersenneAchievementSet ↔
      ∀ K : ℕ, ∃ N : ℕ, K ≤ N ∧ N < K + 2 * Nat.sqrt K + 12 ∧
        greedyBinaryDefect x (N + 1) ≤ greedyBinaryDefect x N := by
  sorry
end Erdos249257.ExternalVerification.Strong257
