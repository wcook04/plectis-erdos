import Erdos249257.RewindHalfDivisorAdapter
import Erdos249257.HalfCarrySelectedWindowBase

/-!
# Smallest post-depth-18 one-step boundary-pair counterexample

The live `HasRewindRestrictionAt` constructor and a width-valid scalar seam
do not force the marked half-divisor boundary predicate. At depth 26 the
first two exact cylinder words both contain exponent 14. The actual common
coefficient at row 27 is one, so the canonical explicit step has rewind
history `[1]`; on carries `[1,2]` this is a genuine seam pair with denominator
two. Nevertheless, at the marked half divisor for row 28, the right ancestor
still has bit 14 equal to true, so it cannot be the false extension required
by `RewindBaseHalfDivisorBoundaryPairAt`.
-/

namespace Erdos249257.RewindBoundaryPairCounterexample

open Erdos249257
open Erdos249257.HalfCarryReachability
open Erdos249257.HalfCarrySelectedWindow
open Erdos249257.HalfCarrySelectedWindowBase
open Erdos249257.FixedCoeffRewind
open Erdos249257.RewindHalfDivisorAdapter

/-- Exact depth-26 cylinder word. Exponents `2,3,6,7,14,20` form the common
prefix; exponents `21,...,26` encode `35-k` in big-endian order. -/
def depth26Word (k : ℕ) : HalfWord 26 := fun i ↦
  if i.val = 2 ∨ i.val = 3 ∨ i.val = 6 ∨ i.val = 7 ∨
      i.val = 14 ∨ i.val = 20 then true
  else if 21 ≤ i.val then
    decide (((35 - k) / 2 ^ (26 - i.val)) % 2 = 1)
  else false

/-- Executable strip and terminal check for the two carries used below. -/
def depth26EntryCheck (k : ℕ) : Bool :=
  ((List.range 26).all fun j ↦
    decide (
      (1 : ℤ) ≤ wordCarry (depth26Word k) j ∧
        wordCarry (depth26Word k) j ≤ halfStripBound (j + 1))) &&
  decide (wordCarry (depth26Word k) 25 = (k : ℤ))

def depth26FirstTwoCheck : Bool :=
  (List.range 2).all fun j ↦ depth26EntryCheck (j + 1)

theorem depth26FirstTwoCheck_eq_true : depth26FirstTwoCheck = true := by
  decide +kernel

theorem depth26EntryCheck_eq_true
    {k : ℕ} (hk : 1 ≤ k) (hk2 : k ≤ 2) :
    depth26EntryCheck k = true := by
  have htable : ∀ j ∈ List.range 2,
      depth26EntryCheck (j + 1) = true := by
    simpa [depth26FirstTwoCheck] using depth26FirstTwoCheck_eq_true
  have hkpred : k - 1 ∈ List.range 2 := by
    rw [List.mem_range]
    omega
  simpa [Nat.sub_add_cancel hk] using htable (k - 1) hkpred

theorem depth26Word_carry_bounds
    {k n : ℕ} (hk : 1 ≤ k) (hk2 : k ≤ 2)
    (hn : 1 ≤ n) (hn26 : n ≤ 26) :
    (1 : ℤ) ≤ wordCarry (depth26Word k) (n - 1) ∧
      wordCarry (depth26Word k) (n - 1) ≤ halfStripBound n := by
  have hentry := depth26EntryCheck_eq_true hk hk2
  have hrows : ((List.range 26).all fun j ↦
      decide (
        (1 : ℤ) ≤ wordCarry (depth26Word k) j ∧
          wordCarry (depth26Word k) j ≤ halfStripBound (j + 1))) = true :=
    (Bool.and_eq_true_iff.mp hentry).1
  have hpred : n - 1 ∈ List.range 26 := by
    rw [List.mem_range]
    omega
  have hrow := (List.all_eq_true.mp hrows) (n - 1) hpred
  have hdecoded :
      (1 : ℤ) ≤ wordCarry (depth26Word k) (n - 1) ∧
        wordCarry (depth26Word k) (n - 1) ≤
          halfStripBound ((n - 1) + 1) :=
    of_decide_eq_true hrow
  simpa [Nat.sub_add_cancel hn] using hdecoded

theorem depth26Word_terminal
    {k : ℕ} (hk : 1 ≤ k) (hk2 : k ≤ 2) :
    wordCarry (depth26Word k) 25 = (k : ℤ) := by
  have hentry := depth26EntryCheck_eq_true hk hk2
  exact of_decide_eq_true (Bool.and_eq_true_iff.mp hentry).2

/-- Exact selected subwindow on carries one and two at depth 26. -/
noncomputable def depth26FirstTwo : SelectedHalfWindow 26 2 := by
  refine ⟨fun k _ _ ↦ depth26Word k, ?_, ?_⟩
  · intro k hk hk2
    refine ⟨by simp [depth26Word], ?_, ?_⟩
    · intro _
      simp [depth26Word]
    · intro n hn hn26
      rw [← wordCarry_eq_integerHalfCarry]
      exact depth26Word_carry_bounds hk hk2 hn hn26
  · intro k hk hk2
    rw [← wordCarry_eq_integerHalfCarry]
    exact depth26Word_terminal hk hk2

/-- Both selected words have the actual common proper coefficient one at
row 27. -/
theorem depth26FirstTwo_selectedRowCoeff_eq_one
    (k : ℕ) (hk : 1 ≤ k) (hk2 : k ≤ 2) :
    selectedRowCoeff depth26FirstTwo k = 1 := by
  rw [selectedRowCoeff, dif_pos ⟨hk, hk2⟩]
  change (supportCoeff (wordSupport (depth26Word k)) 27 : ℤ) = 1
  rw [← wordCoeff_eq_supportCoeff_wordSupport]
  interval_cases k <;> decide

/-- The actual fixed-coefficient constructor step from depth 26 to 27,
restricted to the same two target carries. -/
noncomputable def depth27FirstTwo : SelectedHalfWindow 27 2 :=
  depth26FirstTwo.stepExplicit (C := 1) (by omega)
    (by
      unfold halfStripBound
      omega)
    depth26FirstTwo_selectedRowCoeff_eq_one
    (by omega)

/-- The live constructor records the genuine one-row rewind history `[1]`. -/
theorem depth27FirstTwo_hasRewindRestrictionAt :
    depth27FirstTwo.HasRewindRestrictionAt depth26FirstTwo
      (by omega : 26 ≤ 27) [1] := by
  simpa [depth27FirstTwo] using
    (SelectedHalfWindow.hasRewindRestrictionAt_stepExplicit
      (C := 1) depth26FirstTwo depth26FirstTwo (le_refl 26) []
      (by omega)
      (by
        unfold halfStripBound
        omega)
      depth26FirstTwo_selectedRowCoeff_eq_one
      (by omega)
      depth26FirstTwo.hasRewindRestrictionAt_nil)

theorem oneRowHistory_isSeamPair : IsSeamPair [1] 2 := by
  norm_num [IsSeamPair, rewind, parent]

theorem oneRowHistory_width : 2 ≤ denom [1] := by
  norm_num [denom]

/-- Executable marked-bit fact: the right adjacent ancestor still contains
exponent 14. -/
theorem depth26RightAncestor_bit14_true
    (hpos : 1 ≤ rewind [1] 1 + 1)
    (hbound : rewind [1] 1 + 1 ≤ 2) :
    restrictWord (by omega : 14 ≤ 26)
        (depth26FirstTwo.word (rewind [1] 1 + 1) hpos hbound)
        (Fin.last 14) = true := by
  simp [depth26FirstTwo, restrictWord, depth26Word, rewind, parent]

/-- Hence no common depth-13 parent can make the adjacent ancestors the
required true/false extensions through marked half divisor 14. -/
theorem depth26FirstTwo_not_rewindBaseHalfDivisorBoundaryPairAt
    (a : HalfWord 13) :
    ¬ RewindBaseHalfDivisorBoundaryPairAt depth26FirstTwo
      (by omega : 13 + 1 ≤ 26) [1] a := by
  rintro ⟨hleftPos, hleftBound, hrightPos, hrightBound, _hleft, hright⟩
  have hbit := congrFun hright (Fin.last 14)
  have htrue := depth26RightAncestor_bit14_true hrightPos hrightBound
  rw [htrue, extendHalfWord_last] at hbit
  contradiction

/-- Full concrete falsifier. This includes an actual explicit selected
window step, exact rewind provenance, the width hypothesis, the scalar seam,
and the doubled-row identity. Only the large protected-window buffer used by
the cofinal consumer is intentionally absent. -/
theorem depth27_actualRewindSeam_not_boundaryPair :
    depth27FirstTwo.HasRewindRestrictionAt depth26FirstTwo
        (by omega : 26 ≤ 27) [1] ∧
      IsSeamPair [1] 2 ∧
      2 ≤ denom [1] ∧
      27 + 1 = 2 * (13 + 1) ∧
      ¬ ∃ a : HalfWord 13,
        RewindBaseHalfDivisorBoundaryPairAt depth26FirstTwo
          (by omega : 13 + 1 ≤ 26) [1] a := by
  refine ⟨depth27FirstTwo_hasRewindRestrictionAt,
    oneRowHistory_isSeamPair, oneRowHistory_width, by omega, ?_⟩
  rintro ⟨a, ha⟩
  exact depth26FirstTwo_not_rewindBaseHalfDivisorBoundaryPairAt a ha

#print axioms depth26FirstTwoCheck_eq_true
#print axioms depth26FirstTwo
#print axioms depth26FirstTwo_selectedRowCoeff_eq_one
#print axioms depth27FirstTwo
#print axioms depth27FirstTwo_hasRewindRestrictionAt
#print axioms oneRowHistory_isSeamPair
#print axioms oneRowHistory_width
#print axioms depth26RightAncestor_bit14_true
#print axioms depth26FirstTwo_not_rewindBaseHalfDivisorBoundaryPairAt
#print axioms depth27_actualRewindSeam_not_boundaryPair

end Erdos249257.RewindBoundaryPairCounterexample
