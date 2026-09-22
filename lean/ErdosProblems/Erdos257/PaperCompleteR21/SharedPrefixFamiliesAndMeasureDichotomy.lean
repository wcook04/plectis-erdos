import Erdos249257.SuffixCylinderTerminalOnlyBridge
import ErdosProblems.Erdos257.MersenneSubseriesRigidity

/-!
Paper-form restatements of two untitled/titled propositions of the long
Erdős #257 manuscript `paper/reasoning-parts/erdos257/a257_front.tex`:

* the untitled proposition at line 5411, on shared-prefix families at depth
  `N` and terminal-only strip witnesses;
* "Exact Lebesgue-measure dichotomy" at line 5546.

Every quantity is the paper's: the half-carry at the terminal rank is
`K_A(N) = ihc(A, N - 1) = integerHalfCarry (wordSupport a) (N - 1)`, the strip
bound is `B(m) = 2⌊√m⌋ + 4 = halfStripBound m`, and a depth-`N` family with a
shared prefix through `K` is a `CylinderStage K N`.
-/

set_option autoImplicit false

namespace ErdosProblems.Erdos257.PaperCompleteR21

open Erdos249257
open Erdos249257.HalfCarryReachability
open Erdos249257.SuffixCylinderThreshold
open MeasureTheory

/-! ## The untitled proposition at line 5411 -/

/-- The paper's `B(m) = 2⌊√m⌋ + 4` is the tree's `halfStripBound`. -/
theorem paper_strip_bound_formula (m : ℕ) :
    halfStripBound m = 2 * Nat.sqrt m + 4 :=
  rfl

/-- Long untitled proposition (line 5411), first clause.  Every shared-prefix
family at depth `N` contains a finite support `A ⊆ {2,…,N}` whose terminal
half-carry satisfies `|K_A(N)| ≤ B(N)`. -/
theorem paper_shared_prefix_family_contains_strip_witness
    {K N : ℕ} (S : CylinderStage K N) :
    ∃ a : Erdos249257.HalfCarryReachability.HalfWord N,
      a ⟨0, Nat.zero_lt_succ N⟩ = false ∧
        (∀ h : 1 < N + 1, a ⟨1, h⟩ = false) ∧
        |(integerHalfCarry (wordSupport a) (N - 1) : ℝ)| ≤
          (halfStripBound N : ℝ) :=
  Erdos249257.SuffixCylinderTerminalOnlyBridge.CylinderStage.halfTerminalOnlyStripWitness
    S

/-- Long untitled proposition (line 5411), second clause.  At a feedback row
the same conclusion survives both outputs of the total feedback theorem: full
cylinder advance, or a localized one-hole seam which can delete at most one of
the carries `3` and `4`. -/
theorem paper_shared_prefix_family_strip_witness_after_feedback
    {K N : ℕ} (S : CylinderStage K N) (hN : 1 ≤ N) (hK1N : K + 1 ≤ N)
    (hrow : N + 1 = 2 * (K + 1)) (h27 : 27 ≤ halfStripBound (N + 1)) :
    ∃ a : Erdos249257.HalfCarryReachability.HalfWord (N + 1),
      a ⟨0, Nat.zero_lt_succ (N + 1)⟩ = false ∧
        (∀ h : 1 < N + 1 + 1, a ⟨1, h⟩ = false) ∧
        |(integerHalfCarry (wordSupport a) (N + 1 - 1) : ℝ)| ≤
          (halfStripBound (N + 1) : ℝ) :=
  Erdos249257.SuffixCylinderTerminalOnlyBridge.CylinderStage.halfTerminalOnlyStripWitness_after_feedback
    S hN hK1N hrow h27

/-! ## "Exact Lebesgue-measure dichotomy" (line 5546) -/

/-- Long "Exact Lebesgue-measure dichotomy" (line 5546).  Either the omitted
set of coordinates is a finite `F`, in which case the volume of the
support-restricted Mersenne achievement set is exactly `2^{-|F|}`, or
infinitely many coordinates are omitted and the volume is exactly `0`. -/
theorem paper_volume_supportedMersenneAchievementSet_dichotomy (J : Set ℕ) :
    (∃ F : Finset ℕ,
        J = (↑F : Set ℕ)ᶜ ∧
          volume (supportedMersenneAchievementSet J) =
            ((2 : ENNReal) ^ F.card)⁻¹) ∨
      (Jᶜ.Infinite ∧ volume (supportedMersenneAchievementSet J) = 0) :=
  volume_supportedMersenneAchievementSet_dichotomy J

#print axioms paper_strip_bound_formula
#print axioms paper_shared_prefix_family_contains_strip_witness
#print axioms paper_shared_prefix_family_strip_witness_after_feedback
#print axioms paper_volume_supportedMersenneAchievementSet_dichotomy

end ErdosProblems.Erdos257.PaperCompleteR21
