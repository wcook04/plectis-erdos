import Erdos249257.SuffixCylinderProfiledGap
import Erdos249257.HalfCylinderIntegerGreedy

/-!
# Binary adjacency of profiled suffix-cylinder sheets

A profiled finite gap carries two independently evolving literal prefixes.
The lower prefix is nevertheless not arbitrary: as a binary numeral it is
the immediate successor of the upper prefix.  This module records that
relation and shows that every fixed-cutoff row preserves it.
-/

namespace Erdos249257.SuffixCylinderProfiledGap

open Erdos249257
open Erdos249257.FixedCoeffRewindPhase
open Erdos249257.HalfCarryReachability
open Erdos249257.HalfCarrySelectedWindow
open Erdos249257.SelectedSuffixCylinder
open Erdos249257.SuffixCylinderInStrip
open Erdos249257.SuffixCylinderProfiledGap

/-- The two retained cutoff words straddle one binary boundary: the lower
prefix is the immediate successor of the upper prefix. -/
def ProfiledGapStage.HasAdjacentPrefixes
    {M N : ℕ} (T : ProfiledGapStage M N) : Prop :=
  wordSuffixNumeral T.lowerPrefix 0 M =
    wordSuffixNumeral T.upperPrefix 0 M + 1

end Erdos249257.SuffixCylinderProfiledGap

namespace Erdos249257.SuffixCylinderProfiledAdjacency

open Erdos249257
open Erdos249257.FixedCoeffRewindPhase
open Erdos249257.HalfCarryReachability
open Erdos249257.HalfCarrySelectedWindow
open Erdos249257.SelectedSuffixCylinder
open Erdos249257.SuffixCylinderInStrip
open Erdos249257.SuffixCylinderProfiledGap

/-- Splitting a binary support numeral after its first `M` bits gives the
usual prefix-times-place-value plus suffix decomposition. -/
theorem supportSuffixNumeral_zero_split
    (A : Set ℕ) [DecidablePred (· ∈ A)] (M L : ℕ) :
    supportSuffixNumeral A 0 (M + L) =
      2 ^ L * supportSuffixNumeral A 0 M +
        supportSuffixNumeral A M L := by
  induction L with
  | zero => simp [supportSuffixNumeral]
  | succ L ih =>
      rw [show M + (L + 1) = (M + L) + 1 by omega]
      rw [supportSuffixNumeral, ih, supportSuffixNumeral, pow_succ]
      simp only [zero_add]
      ring

/-- Whole-word binary value decomposes across a literal cutoff. -/
theorem wordSuffixNumeral_zero_split
    {M N : ℕ} (hMN : M ≤ N) (w : HalfWord N) :
    wordSuffixNumeral w 0 N =
      2 ^ (N - M) *
          wordSuffixNumeral (restrictWord hMN w) 0 M +
        wordSuffixNumeral w M (N - M) := by
  classical
  have hpfx :
      supportSuffixNumeral (wordSupport w) 0 M =
        supportSuffixNumeral (wordSupport (restrictWord hMN w)) 0 M := by
    apply supportSuffixNumeral_congr_on
    intro j hj
    rw [wordSupport_restrictWord]
    constructor
    · intro hw
      exact ⟨hw, by simp only [Set.mem_Iic]; omega⟩
    · exact And.left
  unfold wordSuffixNumeral
  calc
    supportSuffixNumeral (wordSupport w) 0 N =
        supportSuffixNumeral (wordSupport w) 0 (M + (N - M)) := by
          rw [Nat.add_sub_of_le hMN]
    _ = 2 ^ (N - M) * supportSuffixNumeral (wordSupport w) 0 M +
          supportSuffixNumeral (wordSupport w) M (N - M) :=
      supportSuffixNumeral_zero_split (wordSupport w) M (N - M)
    _ = 2 ^ (N - M) *
          supportSuffixNumeral (wordSupport (restrictWord hMN w)) 0 M +
        supportSuffixNumeral (wordSupport w) M (N - M) := by rw [hpfx]

/-! ## Coefficient control across a binary boundary -/

/-- Appending one word bit changes a divisor coefficient by the indicator
that the new rank is both selected and a divisor of the inspected row. -/
theorem supportCoeff_wordSupport_extendHalfWord_eq
    {N m : ℕ} (w : HalfWord N) (beta : Bool) :
    supportCoeff (wordSupport (extendHalfWord w beta)) m =
      supportCoeff (wordSupport w) m +
        if beta then (if N + 1 ∈ m.divisors then 1 else 0) else 0 := by
  classical
  cases beta with
  | false => simp [wordSupport_extendHalfWord]
  | true =>
      have hnew : N + 1 ∉ wordSupport w := by
        rintro ⟨hindex, _hbit⟩
        omega
      rw [wordSupport_extendHalfWord]
      simp only [if_true]
      exact
        Erdos249257.HalfCylinderIntegerGreedy.supportCoeff_insert_eq_add_indicator
          (wordSupport w) hnew

/-- Incrementing a fixed-length binary word can create at most one new
selected divisor.  The simultaneous equality clause is the induction
invariant needed when the terminal increment does not carry. -/
theorem supportCoeff_eq_and_le_add_one_of_wordNumeral_eq_or_succ
    (m : ℕ) {N : ℕ} (lower upper : HalfWord N) :
    (wordSuffixNumeral lower 0 N = wordSuffixNumeral upper 0 N →
        supportCoeff (wordSupport lower) m =
          supportCoeff (wordSupport upper) m) ∧
      (wordSuffixNumeral lower 0 N =
          wordSuffixNumeral upper 0 N + 1 →
        supportCoeff (wordSupport lower) m ≤
          supportCoeff (wordSupport upper) m + 1) := by
  classical
  induction N with
  | zero =>
      have hlower : supportCoeff (wordSupport lower) m = 0 := by
        rw [supportCoeff_eq_card_filter]
        apply Finset.card_eq_zero.mpr
        ext d
        simp only [Finset.mem_filter]
        constructor
        · rintro ⟨hddiv, ⟨hdindex, _hbit⟩⟩
          have hdpos := Nat.pos_of_mem_divisors hddiv
          omega
        · simp
      have hupper : supportCoeff (wordSupport upper) m = 0 := by
        rw [supportCoeff_eq_card_filter]
        apply Finset.card_eq_zero.mpr
        ext d
        simp only [Finset.mem_filter]
        constructor
        · rintro ⟨hddiv, ⟨hdindex, _hbit⟩⟩
          have hdpos := Nat.pos_of_mem_divisors hddiv
          omega
        · simp
      constructor
      · intro _
        rw [hlower, hupper]
      · intro _
        rw [hlower, hupper]
        omega
  | succ N ih =>
      let lowerPrefix : HalfWord N :=
        restrictWord (Nat.le_succ N) lower
      let upperPrefix : HalfWord N :=
        restrictWord (Nat.le_succ N) upper
      let lowerBit : Bool := lower (Fin.last (N + 1))
      let upperBit : Bool := upper (Fin.last (N + 1))
      have hlowerDecomp :
          lower = extendHalfWord lowerPrefix lowerBit := by
        funext i
        refine Fin.lastCases ?_ (fun j ↦ ?_) i
        · simp [lowerBit]
        · simp only [extendHalfWord_castSucc]
          change lower j.castSucc = lower _
          apply congrArg lower
          apply Fin.ext
          rfl
      have hupperDecomp :
          upper = extendHalfWord upperPrefix upperBit := by
        funext i
        refine Fin.lastCases ?_ (fun j ↦ ?_) i
        · simp [upperBit]
        · simp only [extendHalfWord_castSucc]
          change upper j.castSucc = upper _
          apply congrArg upper
          apply Fin.ext
          rfl
      have hlowerNumeral :
          wordSuffixNumeral lower 0 (N + 1) =
            2 * wordSuffixNumeral lowerPrefix 0 N +
              if lowerBit then 1 else 0 := by
        rw [hlowerDecomp]
        simpa using supportSuffixNumeral_extendHalfWord
          (M := 0) (N := N) (Nat.zero_le N) lowerPrefix lowerBit
      have hupperNumeral :
          wordSuffixNumeral upper 0 (N + 1) =
            2 * wordSuffixNumeral upperPrefix 0 N +
              if upperBit then 1 else 0 := by
        rw [hupperDecomp]
        simpa using supportSuffixNumeral_extendHalfWord
          (M := 0) (N := N) (Nat.zero_le N) upperPrefix upperBit
      have hlowerCoeff :
          supportCoeff (wordSupport lower) m =
            supportCoeff (wordSupport lowerPrefix) m +
              if lowerBit then
                (if N + 1 ∈ m.divisors then 1 else 0)
              else 0 := by
        rw [hlowerDecomp]
        exact supportCoeff_wordSupport_extendHalfWord_eq lowerPrefix lowerBit
      have hupperCoeff :
          supportCoeff (wordSupport upper) m =
            supportCoeff (wordSupport upperPrefix) m +
              if upperBit then
                (if N + 1 ∈ m.divisors then 1 else 0)
              else 0 := by
        rw [hupperDecomp]
        exact supportCoeff_wordSupport_extendHalfWord_eq upperPrefix upperBit
      have hprefix := ih lowerPrefix upperPrefix
      constructor
      · intro heq
        rw [hlowerNumeral, hupperNumeral] at heq
        rw [hlowerCoeff, hupperCoeff]
        cases hlowerBit : lowerBit <;> cases hupperBit : upperBit <;>
          simp [hlowerBit, hupperBit] at heq ⊢
        · exact hprefix.1 (by omega)
        · omega
        · omega
        · exact hprefix.1 (by omega)
      · intro hsucc
        rw [hlowerNumeral, hupperNumeral] at hsucc
        rw [hlowerCoeff, hupperCoeff]
        cases hlowerBit : lowerBit <;> cases hupperBit : upperBit <;>
          simp [hlowerBit, hupperBit] at hsucc ⊢
        · omega
        · have hpre := hprefix.2 (by omega)
          omega
        · have hpre := hprefix.1 (by omega)
          split <;> omega
        · omega

/-- Stage form of the binary-increment bound: adjacent profiled prefixes
have lower next-row coefficient at most one above the upper coefficient. -/
theorem ProfiledGapStage.lowerNextCoeff_le_upperNextCoeff_add_one
    {M N : ℕ} (T : ProfiledGapStage M N)
    (hadjacent : T.HasAdjacentPrefixes) :
    supportCoeff (wordSupport T.lowerPrefix) (N + 1) ≤
      supportCoeff (wordSupport T.upperPrefix) (N + 1) + 1 := by
  exact
    (supportCoeff_eq_and_le_add_one_of_wordNumeral_eq_or_succ
      (N + 1) T.lowerPrefix T.upperPrefix).2 hadjacent

/-- The exact two-sheet state starts with adjacent complementary children
of its common boundary prefix. -/
theorem profiledGapStageOfTwoSheet_hasAdjacentPrefixes
    {K N : ℕ} (T : InStripTwoSheetStage K N) :
    (profiledGapStageOfTwoSheet T).HasAdjacentPrefixes := by
  have hlower := supportSuffixNumeral_extendHalfWord
    (M := 0) (N := K) (Nat.zero_le K) T.boundaryPrefix true
  have hupper := supportSuffixNumeral_extendHalfWord
    (M := 0) (N := K) (Nat.zero_le K) T.boundaryPrefix false
  unfold ProfiledGapStage.HasAdjacentPrefixes
  change wordSuffixNumeral (extendHalfWord T.boundaryPrefix true) 0 (K + 1) =
    wordSuffixNumeral (extendHalfWord T.boundaryPrefix false) 0 (K + 1) + 1
  simp at hlower hupper
  omega

#print axioms profiledGapStageOfTwoSheet_hasAdjacentPrefixes
#print axioms supportCoeff_wordSupport_extendHalfWord_eq
#print axioms supportCoeff_eq_and_le_add_one_of_wordNumeral_eq_or_succ
#print axioms ProfiledGapStage.lowerNextCoeff_le_upperNextCoeff_add_one

end Erdos249257.SuffixCylinderProfiledAdjacency

namespace Erdos249257.SuffixCylinderProfiledGap

open Erdos249257
open Erdos249257.HalfCarryReachability

/-- A profiled fixed-cutoff successor leaves both literal prefixes
unchanged, and therefore preserves their binary adjacency. -/
theorem ProfiledGapStage.advanceOfNextCoeffProfile_hasAdjacentPrefixes
    {M N lowerCoeff upperCoeff : ℕ} (T : ProfiledGapStage M N)
    (hadjacent : T.HasAdjacentPrefixes)
    (hN : 1 ≤ N)
    (hprofile : T.HasNextCoeffProfile lowerCoeff upperCoeff)
    (hchildLoPos : 1 ≤ 2 * T.gapLo - lowerCoeff - 1)
    (hupperCoeff : upperCoeff ≤ 2 * T.gapHi)
    (hchildOrder :
      2 * T.gapLo - lowerCoeff - 1 ≤ 2 * T.gapHi - upperCoeff)
    (hchildHiStrip :
      2 * T.gapHi - upperCoeff ≤ halfStripBound (N + 1))
    (hupperBuffer :
      halfStripBound (N + 1) + upperCoeff ≤ 2 * halfStripBound N) :
    (T.advanceOfNextCoeffProfile hN hprofile hchildLoPos hupperCoeff
      hchildOrder hchildHiStrip hupperBuffer).HasAdjacentPrefixes := by
  simpa only [ProfiledGapStage.HasAdjacentPrefixes,
    ProfiledGapStage.advanceOfNextCoeffProfile] using hadjacent

#print axioms ProfiledGapStage.advanceOfNextCoeffProfile_hasAdjacentPrefixes

end Erdos249257.SuffixCylinderProfiledGap
