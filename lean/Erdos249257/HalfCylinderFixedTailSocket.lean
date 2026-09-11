import Erdos249257.HalfCylinderHalfMembershipClassification

/-!
# Fixed-tail socket for the half-cylinder seam

This module localizes the remaining half-membership obstruction at each
actual skipped rank.  A skip is the final skip exactly when its post-decision
remainder lies strictly beyond the complete future Mersenne tail.  Thus the
global no-last-skip condition is equivalent to a pointwise tail-survival
inequality at every actual skip.

No tail-survival estimate or decision of Erdős #257 is asserted here.
-/

namespace Erdos249257

open Set

/-- A skipped rank is the last skipped rank exactly when its post-decision
residual is already fatal (strictly larger than the complete remaining tail).
This is the local one-rank form of the eventual-right obstruction. -/
theorem isLastHalfGreedySkip_iff_skip_and_fatal
    {M : ℕ} :
    IsLastHalfGreedySkip M ↔
      M ∈ greedyMersenneSkippedSupport (1 / 2 : ℝ) ∧
        GreedyMersenneFatalAt (1 / 2 : ℝ) M := by
  constructor
  · intro hlast
    refine ⟨hlast.1, ?_⟩
    unfold GreedyMersenneFatalAt
    have hle := lastHalfSkip_tail_le_remainder hlast
    have hdelta := lastHalfSkip_shiftDelta_eq_remainder_sub_tail hlast
    have hne := lastHalfSkip_shiftDelta_ne_zero hlast
    by_contra hnot
    have heq : mersenneTail M =
        greedyMersenneRemainder (1 / 2 : ℝ) M :=
      le_antisymm hle (le_of_not_gt hnot)
    apply hne
    rw [hdelta, heq]
    ring
  · rintro ⟨hskip, hfatal⟩
    refine ⟨hskip, ?_⟩
    intro m hMm hmSkip
    have hMlePred : M ≤ m - 1 := by omega
    have hfatPred : GreedyMersenneFatalAt (1 / 2 : ℝ) (m - 1) := by
      have hadd := greedyMersenneFatalAt_add hfatal (m - 1 - M)
      simpa [Nat.add_sub_of_le hMlePred] using hadd
    have htake := (greedyMersenneFatalAt_succ hfatPred).1
    have hnotSkip : m ∉ greedyMersenneSkippedSupport (1 / 2 : ℝ) := by
      rw [show m = (m - 1) + 1 by omega,
        succ_mem_greedyMersenneSkippedSupport_iff]
      simpa [show m - 1 + 1 = m by omega] using htake
    exact hnotSkip hmSkip

/-- Exact remaining arithmetic target: no final skipped rank iff every actual
skip remains on the nonfatal side of the full Mersenne tail. -/
theorem no_lastHalfGreedySkip_iff_every_skip_survives :
    (¬ ∃ M : ℕ, IsLastHalfGreedySkip M) ↔
      ∀ M : ℕ,
        M ∈ greedyMersenneSkippedSupport (1 / 2 : ℝ) →
          greedyMersenneRemainder (1 / 2 : ℝ) M ≤ mersenneTail M := by
  rw [not_exists]
  apply forall_congr'
  intro M
  rw [isLastHalfGreedySkip_iff_skip_and_fatal]
  unfold GreedyMersenneFatalAt
  push Not
  tauto

/-- Half membership is equivalently the rank-local statement that every
actual skipped decision leaves a residual on the surviving side of the full
remaining tail. -/
theorem half_mem_iff_every_actual_skip_survives :
    (1 / 2 : ℝ) ∈ mersenneAchievementSet ↔
      ∀ M : ℕ,
        M ∈ greedyMersenneSkippedSupport (1 / 2 : ℝ) →
          greedyMersenneRemainder (1 / 2 : ℝ) M ≤ mersenneTail M := by
  rw [half_mem_mersenneAchievementSet_iff_no_lastHalfGreedySkip]
  exact no_lastHalfGreedySkip_iff_every_skip_survives

#print axioms isLastHalfGreedySkip_iff_skip_and_fatal
#print axioms no_lastHalfGreedySkip_iff_every_skip_survives
#print axioms half_mem_iff_every_actual_skip_survives

end Erdos249257
