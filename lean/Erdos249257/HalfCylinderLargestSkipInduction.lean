import Erdos249257.HalfCylinderLargestSkipGap

/-!
# Linear largest-skip induction for Erdős #257

The exact adjacent-gap analysis reduces the remaining half-membership
producer to one local first-crossing statement.  A row is `late` when its
largest false rank `d` lies strictly beyond two thirds of the row.  Upper or
middle successors reset the largest false rank to the old terminal rank;
right successors preserve it.  Consequently, the only arithmetic input
needed for a global induction is that a late largest false rank cannot cross
the two-thirds boundary without an upper or middle successor.

This file proves the complete structural fan-in from that local socket to
membership of `1/2` in the Mersenne achievement set.  It deliberately leaves
the first-crossing socket as an explicit proposition.
-/

namespace Erdos249257

open Set Filter
open HalfCylinderIntegerGreedy

noncomputable section

/-- Row `s` has a largest false rank strictly beyond two thirds of the row. -/
def LargestSkipLateAt (s : ℕ) : Prop :=
  ∃ d : ℕ,
    IsLargestFalseRank (seamGreedyWord s) d ∧ 2 * s < 3 * d

/-- The sole local arithmetic socket: before a late largest false rank can
cross the two-thirds boundary, the concrete successor must take an upper or
middle branch. -/
def LargestSkipLateStepSocket : Prop :=
  ∀ (s d : ℕ) (hs : 14 ≤ s),
    IsLargestFalseRank (seamGreedyWord s) d →
      2 * s < 3 * d →
        2 * (s + 1) < 3 * d ∨
          SeamGreedyUpperOrMiddleAt s (by omega)

private theorem seamWeights_fourteen :
    seamWeights 14 =
      [89478485, 38347922, 17895697, 8659208, 4260880, 2113665,
        1052688, 525314, 262400, 131136, 65552, 32772] := by
  unfold seamWeights
  rw [seamWeightsFrom_eq_cons (by norm_num : 2 < 14),
    seamWeightsFrom_eq_cons (by norm_num : 3 < 14),
    seamWeightsFrom_eq_cons (by norm_num : 4 < 14),
    seamWeightsFrom_eq_cons (by norm_num : 5 < 14),
    seamWeightsFrom_eq_cons (by norm_num : 6 < 14),
    seamWeightsFrom_eq_cons (by norm_num : 7 < 14),
    seamWeightsFrom_eq_cons (by norm_num : 8 < 14),
    seamWeightsFrom_eq_cons (by norm_num : 9 < 14),
    seamWeightsFrom_eq_cons (by norm_num : 10 < 14),
    seamWeightsFrom_eq_cons (by norm_num : 11 < 14),
    seamWeightsFrom_eq_cons (by norm_num : 12 < 14),
    seamWeightsFrom_eq_cons (by norm_num : 13 < 14),
    seamWeightsFrom_eq_nil (by norm_num : 14 ≤ 14)]
  norm_num [truncatedMersenneWeight]

private theorem seamSubsetTarget_fourteen :
    seamSubsetTarget 14 = 134201344 := by
  norm_num [seamSubsetTarget]

private theorem integerGreedyBits_fourteen :
    integerGreedyBits (seamWeights 14) (seamSubsetTarget 14) =
      [true, true, false, false, true, true,
        false, false, false, false, false, false] := by
  rw [seamWeights_fourteen, seamSubsetTarget_fourteen]
  norm_num [integerGreedyBits]

/- The exact row-fourteen base: its terminal rank `13` is false. -/
theorem largestSkipLateAt_fourteen : LargestSkipLateAt 14 := by
  refine ⟨13, ?_, by norm_num⟩
  refine ⟨by norm_num, by norm_num, ?_, ?_⟩
  · intro hmem
    obtain ⟨i, hi, hirank⟩ := mem_seamWordSupport_iff.mp hmem
    have hieq : i = ⟨11, by norm_num⟩ := by
      apply Fin.ext
      change (i : ℕ) = 11
      omega
    subst i
    have hbits := integerGreedyBits_fourteen
    simp [seamGreedyWord, SeamRowWord.ofList, hbits] at hi
  · intro e hde hes
    omega

/-- One local first-crossing step propagates the late largest-skip
invariant. -/
theorem LargestSkipLateStepSocket.largestSkipLateAt_succ
    (hstep : LargestSkipLateStepSocket)
    {s : ℕ} (hs : 14 ≤ s) (hlate : LargestSkipLateAt s) :
    LargestSkipLateAt (s + 1) := by
  obtain ⟨d, hmax, hmargin⟩ := hlate
  let hs5 : 5 ≤ s := by omega
  by_cases hUM : SeamGreedyUpperOrMiddleAt s hs5
  · refine ⟨s,
      seamGreedyWord_succ_isLargestFalseRank_terminal_of_upperOrMiddle
        s hs5 hUM, ?_⟩
    omega
  · have hmargin' : 2 * (s + 1) < 3 * d := by
      rcases hstep s d hs hmax hmargin with hnext | hproducer
      · exact hnext
      · exact False.elim (hUM hproducer)
    have hcarry : ¬ (seamAdjacentCut s hs5).successorCarries := by
      intro hcarry
      exact hUM (Or.inl hcarry)
    have hright : (seamAdjacentCut s hs5).terminalWeight ≤
        4 * (seamAdjacentCut s hs5).remainder +
          (seamPerturbedFamily s (by omega)).gap -
          (seamAdjacentCut s hs5).belowPulse := by
      apply Nat.le_of_not_gt
      intro hmiddle
      exact hUM (Or.inr ⟨hcarry, hmiddle⟩)
    refine ⟨d, ?_, hmargin'⟩
    exact hmax.seamGreedyWord_succ_of_rightBranch hs5 hcarry hright

/-- The local socket gives the late largest-skip invariant on every row from
fourteen onward. -/
theorem largestSkipLateAt_of_stepSocket
    (hstep : LargestSkipLateStepSocket) (s : ℕ) (hs : 14 ≤ s) :
    LargestSkipLateAt s := by
  induction s, hs using Nat.le_induction with
  | base => exact largestSkipLateAt_fourteen
  | succ s hs ih =>
      exact hstep.largestSkipLateAt_succ hs ih

/-- A linear largest false rank on every late row supplies cofinal skipped
ranks in exactly the format consumed by the existing compactness theorem. -/
theorem seamGreedyUnboundedSkippedRanksAlong_of_largestSkipLateStepSocket
    (hstep : LargestSkipLateStepSocket) :
    SeamGreedyUnboundedSkippedRanksAlong (fun j : ℕ => 14 + j) := by
  classical
  have hlate : ∀ j : ℕ, LargestSkipLateAt (14 + j) := by
    intro j
    exact largestSkipLateAt_of_stepSocket hstep (14 + j) (by omega)
  choose rank hrank using hlate
  let skip : ∀ j : ℕ, Fin ((14 + j) - 2) := fun j =>
    ⟨rank j - 2, by
      rcases (hrank j).1 with ⟨_hd2, hds, _hdnot, _hfull⟩
      omega⟩
  refine ⟨skip, ?_, ?_, ?_⟩
  · simpa [Nat.add_comm] using tendsto_add_atTop_nat 14
  · apply tendsto_atTop.2
    intro B
    filter_upwards [eventually_ge_atTop (3 * B)] with j hj
    rcases (hrank j).1 with ⟨hd2, _hds, _hdnot, _hfull⟩
    have hmargin := (hrank j).2
    have hrankEq : (skip j : ℕ) + 2 = rank j := by
      dsimp [skip]
      omega
    rw [hrankEq]
    omega
  · intro j
    apply Bool.eq_false_of_not_eq_true
    intro htrue
    rcases (hrank j).1 with ⟨hd2, _hds, hdnot, _hfull⟩
    have hrankEq : rank j = (skip j : ℕ) + 2 := by
      dsimp [skip]
      omega
    have hmem : rank j ∈ seamWordSupport (seamGreedyWord (14 + j)) :=
      mem_seamWordSupport_iff.mpr ⟨skip j, htrue, hrankEq⟩
    exact hdnot hmem

/-- The first-crossing socket is sufficient for the desired #257
half-membership endpoint. -/
theorem half_mem_mersenneAchievementSet_of_largestSkipLateStepSocket
    (hstep : LargestSkipLateStepSocket) :
    (1 / 2 : ℝ) ∈ mersenneAchievementSet := by
  exact half_mem_mersenneAchievementSet_of_unboundedSkippedRanks
    (fun j : ℕ => 14 + j)
    (seamGreedyUnboundedSkippedRanksAlong_of_largestSkipLateStepSocket hstep)

#print axioms largestSkipLateAt_fourteen
#print axioms LargestSkipLateStepSocket.largestSkipLateAt_succ
#print axioms largestSkipLateAt_of_stepSocket
#print axioms seamGreedyUnboundedSkippedRanksAlong_of_largestSkipLateStepSocket
#print axioms half_mem_mersenneAchievementSet_of_largestSkipLateStepSocket

end

end Erdos249257
