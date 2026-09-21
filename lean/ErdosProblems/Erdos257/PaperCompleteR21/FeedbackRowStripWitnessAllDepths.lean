import Erdos249257.SuffixCylinderTerminalOnlyBridge
import ErdosProblems.Erdos257.PaperCompleteR21.SharedPrefixFamiliesAndMeasureDichotomy

/-!
# The feedback-row clause of the line-5411 proposition, at every depth

The long Erdős #257 manuscript `paper/reasoning-parts/erdos257/a257_front.tex`
asserts at line 5411 that a depth-`N` shared-prefix family contains a finite
support `A` with `|K_A(N)| ≤ B(N)`, `B(m) = 2⌊√m⌋ + 4`, and that **at a feedback
row this survives both outputs of the total feedback theorem**: full-cylinder
advance, or a localized one-hole seam, which can delete at most one of the
carries `3` and `4`.  No depth restriction is stated.

The existing endpoint
`ErdosProblems.Erdos257.PaperCompleteR21.paper_shared_prefix_family_strip_witness_after_feedback`
carries the extra hypothesis `27 ≤ halfStripBound (N + 1)` (equivalently
`N + 1 ≥ 144`), inherited from the protected `3..27` seam interface used by
`Erdos249257.SuffixCylinderGlobalProducer.CylinderStage.feedbackStep_or_protectedSeam`.

That hypothesis is an artefact of the interface, not of the mathematics.  The
seam output only ever deletes one carry, and the paper's own two carries `3`
and `4` lie in **every** half strip because `halfStripBound m = 2⌊√m⌋ + 4 ≥ 4`.
Running the same dichotomy through the operational in-strip split
`Erdos249257.SuffixCylinderInStrip.CylinderStage.feedbackAdvance_or_inStripTwoSheet`,
whose residual branch is the one-hole seam in retained form and which needs no
lower bound on the strip, gives the paper's clause with no depth restriction.
-/

set_option autoImplicit false

namespace ErdosProblems.Erdos257.PaperCompleteR21

open Erdos249257
open Erdos249257.HalfCarryReachability
open Erdos249257.SuffixCylinderThreshold
open Erdos249257.SuffixCylinderInStrip

/-! ## The carries `3` and `4` lie in every half strip -/

/-- `B(m) = 2⌊√m⌋ + 4 ≥ 4` for every `m`: the paper's two probe carries `3`
and `4` are admissible strip positions at every depth, with no threshold. -/
theorem four_le_halfStripBound (m : ℕ) : 4 ≤ halfStripBound m := by
  have h : halfStripBound m = 2 * Nat.sqrt m + 4 := rfl
  omega

/-! ## The seam output, at every depth -/

/-- **The paper's seam argument, unrestricted.**  A retained one-hole seam at
depth `M` deletes at most one carry, so at least one of `3` and `4` survives;
both are `≤ B(M)` by `four_le_halfStripBound`.  The surviving carry is
reachable, hence gives a terminal-only strip witness at depth `M`.  No
`27 ≤ halfStripBound M` hypothesis appears. -/
theorem halfTerminalOnlyStripWitness_of_inStripTwoSheetStage_via_carries_three_four
    {K M : ℕ} (T : InStripTwoSheetStage K M) :
    Erdos249257.HalfCarryReachability.HalfTerminalOnlyStripWitness M := by
  classical
  -- the paper's pair `{3, 4}`; the seam's single hole misses one of them
  set q : ℕ := if T.hole = 3 then 4 else 3 with hqdef
  have hq : 1 ≤ q := by
    rw [hqdef]; split_ifs <;> omega
  have hqB : q ≤ halfStripBound M := by
    have h4 := four_le_halfStripBound M
    rw [hqdef]; split_ifs <;> omega
  have hqHole : q ≠ T.hole := by
    rw [hqdef]; split_ifs with hhole <;> omega
  exact
    Erdos249257.SuffixCylinderTerminalOnlyBridge.halfTerminalOnlyStripWitness_of_halfTerminalReachable
      (T.halfTerminalReachable_of_ne_hole hq hqB hqHole)

/-! ## The advance output -/

/-- The advance output of the feedback theorem is again a full cylinder stage,
so the first clause of the proposition applies to it verbatim. -/
theorem halfTerminalOnlyStripWitness_of_feedbackAdvance
    {K M : ℕ} (S : CylinderStage K M) :
    Erdos249257.HalfCarryReachability.HalfTerminalOnlyStripWitness M :=
  Erdos249257.SuffixCylinderTerminalOnlyBridge.CylinderStage.halfTerminalOnlyStripWitness S

/-! ## The total feedback dichotomy without a depth threshold -/

/-- The paper's "total feedback theorem" at a feedback row, in the form that
carries no strip threshold: either the full cylinder advances one row, or a
localized one-hole seam is retained at the next row. -/
theorem paper_feedback_row_total_dichotomy
    {K N : ℕ} (S : CylinderStage K N) (hK1N : K + 1 ≤ N)
    (hrow : N + 1 = 2 * (K + 1)) :
    Nonempty (CylinderStage (K + 1) (N + 1)) ∨
      Nonempty (InStripTwoSheetStage K (N + 1)) :=
  Erdos249257.SuffixCylinderInStrip.CylinderStage.feedbackAdvance_or_inStripTwoSheet
    S (by omega) hK1N hrow

/-! ## The line-5411 second clause, at every depth -/

/-- **Long untitled proposition (line 5411), second clause, at every depth.**
At a feedback row `N + 1 = 2(K + 1)` of a depth-`N` shared-prefix family, the
strip witness survives *both* outputs of the total feedback theorem: the
depth-`(N+1)` family again contains a finite support `A ⊆ {2,…,N+1}` with
`|K_A(N+1)| ≤ B(N+1)`.

This is the paper's statement with no depth restriction: the hypothesis
`27 ≤ halfStripBound (N + 1)` of
`paper_shared_prefix_family_strip_witness_after_feedback` is absent, and the
redundant `1 ≤ N` is derived from `K + 1 ≤ N`. -/
theorem paper_shared_prefix_family_strip_witness_after_feedback_all_depths
    {K N : ℕ} (S : CylinderStage K N) (hK1N : K + 1 ≤ N)
    (hrow : N + 1 = 2 * (K + 1)) :
    ∃ a : Erdos249257.HalfCarryReachability.HalfWord (N + 1),
      a ⟨0, Nat.zero_lt_succ (N + 1)⟩ = false ∧
        (∀ h : 1 < N + 1 + 1, a ⟨1, h⟩ = false) ∧
        |(integerHalfCarry (wordSupport a) (N + 1 - 1) : ℝ)| ≤
          (halfStripBound (N + 1) : ℝ) := by
  rcases paper_feedback_row_total_dichotomy S hK1N hrow with hadvance | hseam
  · obtain ⟨S'⟩ := hadvance
    exact halfTerminalOnlyStripWitness_of_feedbackAdvance S'
  · obtain ⟨T⟩ := hseam
    exact halfTerminalOnlyStripWitness_of_inStripTwoSheetStage_via_carries_three_four T

/-- The threshold-carrying endpoint quoted by the paper is the specialisation
of the unrestricted one; recorded here so the improvement is visible in one
place. -/
theorem paper_shared_prefix_family_strip_witness_after_feedback_of_all_depths
    {K N : ℕ} (S : CylinderStage K N) (_hN : 1 ≤ N) (hK1N : K + 1 ≤ N)
    (hrow : N + 1 = 2 * (K + 1)) (_h27 : 27 ≤ halfStripBound (N + 1)) :
    ∃ a : Erdos249257.HalfCarryReachability.HalfWord (N + 1),
      a ⟨0, Nat.zero_lt_succ (N + 1)⟩ = false ∧
        (∀ h : 1 < N + 1 + 1, a ⟨1, h⟩ = false) ∧
        |(integerHalfCarry (wordSupport a) (N + 1 - 1) : ℝ)| ≤
          (halfStripBound (N + 1) : ℝ) := by
  exact paper_shared_prefix_family_strip_witness_after_feedback_all_depths S hK1N hrow

#print axioms four_le_halfStripBound
#print axioms halfTerminalOnlyStripWitness_of_inStripTwoSheetStage_via_carries_three_four
#print axioms halfTerminalOnlyStripWitness_of_feedbackAdvance
#print axioms paper_feedback_row_total_dichotomy
#print axioms paper_shared_prefix_family_strip_witness_after_feedback_all_depths
#print axioms paper_shared_prefix_family_strip_witness_after_feedback_of_all_depths
#print axioms ErdosProblems.Erdos257.PaperCompleteR21.paper_shared_prefix_family_contains_strip_witness

end ErdosProblems.Erdos257.PaperCompleteR21
