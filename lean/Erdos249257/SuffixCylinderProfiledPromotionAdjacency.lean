import Erdos249257.SuffixCylinderProfiledAdjacency
import Erdos249257.SuffixCylinderProfiledPromotion

/-!
# Binary adjacency across profiled cutoff promotion

Cutoff promotion appends `false` to the lower prefix and `true` to the
upper prefix.  Those are again consecutive binary words whenever the old
prefixes were consecutive.
-/

namespace Erdos249257.SuffixCylinderProfiledPromotionAdjacency

open Erdos249257
open Erdos249257.HalfCarryReachability
open Erdos249257.HalfCarrySelectedWindow
open Erdos249257.SelectedSuffixCylinder
open Erdos249257.SuffixCylinderProfiledGap
open Erdos249257.SuffixCylinderProfiledAdjacency
open Erdos249257.SuffixCylinderProfiledPromotion

/-- Appending `false` shifts the whole prefix numeral left by one place. -/
theorem wordSuffixNumeral_extendHalfWord_false_zero
    {M : ℕ} (p : HalfWord M) :
    wordSuffixNumeral (extendHalfWord p false) 0 (M + 1) =
      2 * wordSuffixNumeral p 0 M := by
  have h := supportSuffixNumeral_extendHalfWord
    (M := 0) (N := M) (Nat.zero_le M) p false
  simpa using h

/-- Appending `true` shifts the whole prefix numeral left and adds one. -/
theorem wordSuffixNumeral_extendHalfWord_true_zero
    {M : ℕ} (p : HalfWord M) :
    wordSuffixNumeral (extendHalfWord p true) 0 (M + 1) =
      2 * wordSuffixNumeral p 0 M + 1 := by
  have h := supportSuffixNumeral_extendHalfWord
    (M := 0) (N := M) (Nat.zero_le M) p true
  simpa using h

#print axioms wordSuffixNumeral_extendHalfWord_false_zero
#print axioms wordSuffixNumeral_extendHalfWord_true_zero

end Erdos249257.SuffixCylinderProfiledPromotionAdjacency

namespace Erdos249257.SuffixCylinderProfiledGap

open Erdos249257
open Erdos249257.HalfCarryReachability
open Erdos249257.HalfCarrySelectedWindow
open Erdos249257.SelectedSuffixCylinder
open Erdos249257.SuffixCylinderProfiledAdjacency
open Erdos249257.SuffixCylinderProfiledPromotion
open Erdos249257.SuffixCylinderProfiledPromotionAdjacency

/-- Type-namespace adapter for the cutoff-promotion implementation. -/
noncomputable def ProfiledGapStage.promoteCutoff
    {M N : ℕ} (T : ProfiledGapStage M N)
    (hM : 4 ≤ M) (hboundary : N = 2 * M + 1) :
    ProfiledGapStage (M + 1) N :=
  Erdos249257.SuffixCylinderProfiledPromotion.ProfiledGapStage.promoteCutoff
    T hM hboundary

/-- The low-false/high-true cutoff promotion preserves the binary boundary
between the two profiled sheets. -/
theorem ProfiledGapStage.promoteCutoff_hasAdjacentPrefixes
    {M N : ℕ} (T : ProfiledGapStage M N)
    (hadjacent : T.HasAdjacentPrefixes)
    (hM : 4 ≤ M) (hboundary : N = 2 * M + 1) :
    (T.promoteCutoff hM hboundary).HasAdjacentPrefixes := by
  subst N
  change
    wordSuffixNumeral (extendHalfWord T.lowerPrefix false) 0 (M + 1) =
      wordSuffixNumeral (extendHalfWord T.upperPrefix true) 0 (M + 1) + 1
  rw [wordSuffixNumeral_extendHalfWord_false_zero,
    wordSuffixNumeral_extendHalfWord_true_zero]
  unfold ProfiledGapStage.HasAdjacentPrefixes at hadjacent
  omega

/-! ## Extreme words at the two cylinder boundaries -/

/-- When the lower selected family is nonempty, its top-indexed word has
zero suffix beyond the retained cutoff. -/
theorem ProfiledGapStage.lowerTop_suffixNumeral_eq_zero
    {M N : ℕ} (T : ProfiledGapStage M N)
    (hlowerNonempty : 2 ≤ T.gapLo) :
    wordSuffixNumeral
        (T.lower.word (T.gapLo - 1) (by omega) (le_refl _))
        M (N - M) = 0 := by
  rcases T.lowerCylinder with ⟨_prefix, hcylinder⟩
  have hendpoint :=
    (hcylinder (T.gapLo - 1) (by omega) (le_refl _)).2
  omega

/-- When the upper selected interval is nonempty, its bottom-indexed word
has the maximal all-one suffix beyond the retained cutoff. -/
theorem ProfiledGapStage.upperBottom_suffixNumeral_eq_pow_sub_one
    {M N : ℕ} (T : ProfiledGapStage M N)
    (hupperNonempty : T.gapHi < halfStripBound N) :
    wordSuffixNumeral
        (T.upper.word (T.gapHi + 1) (le_refl _) (by omega))
        M (N - M) = 2 ^ (N - M) - 1 := by
  rcases T.upperCylinder with ⟨_prefix, hcylinder⟩
  have hendpoint :=
    (hcylinder (T.gapHi + 1) (le_refl _) (by omega)).2
  rw [T.endpointSeparation] at hendpoint
  have hpowPos : 0 < 2 ^ (N - M) := pow_pos (by omega) _
  omega

/-- The top lower word and bottom upper word are consecutive as full binary
words: the former is the adjacent lower prefix followed by zeros, while the
latter is the upper prefix followed by ones. -/
theorem ProfiledGapStage.boundaryWordsAdjacent
    {M N : ℕ} (T : ProfiledGapStage M N)
    (hadjacent : T.HasAdjacentPrefixes)
    (hlowerNonempty : 2 ≤ T.gapLo)
    (hupperNonempty : T.gapHi < halfStripBound N) :
    wordSuffixNumeral
        (T.lower.word (T.gapLo - 1) (by omega) (le_refl _)) 0 N =
      wordSuffixNumeral
          (T.upper.word (T.gapHi + 1) (le_refl _) (by omega)) 0 N + 1 := by
  have hlowerTail := T.lowerTop_suffixNumeral_eq_zero hlowerNonempty
  have hupperTail :=
    T.upperBottom_suffixNumeral_eq_pow_sub_one hupperNonempty
  have hlowerPrefix :=
    T.lowerLiteral (T.gapLo - 1) (by omega) (le_refl _)
  have hupperPrefix :=
    T.upperLiteral (T.gapHi + 1) (le_refl _) (by omega)
  have hlowerSplit := wordSuffixNumeral_zero_split T.hMN
    (T.lower.word (T.gapLo - 1) (by omega) (le_refl _))
  have hupperSplit := wordSuffixNumeral_zero_split T.hMN
    (T.upper.word (T.gapHi + 1) (le_refl _) (by omega))
  rw [hlowerPrefix, hlowerTail] at hlowerSplit
  rw [hupperPrefix, hupperTail] at hupperSplit
  unfold ProfiledGapStage.HasAdjacentPrefixes at hadjacent
  rw [hadjacent, Nat.mul_add, Nat.mul_one] at hlowerSplit
  have hpowPos : 0 < 2 ^ (N - M) := pow_pos (by omega) _
  omega

#print axioms ProfiledGapStage.promoteCutoff
#print axioms ProfiledGapStage.promoteCutoff_hasAdjacentPrefixes
#print axioms ProfiledGapStage.lowerTop_suffixNumeral_eq_zero
#print axioms ProfiledGapStage.upperBottom_suffixNumeral_eq_pow_sub_one
#print axioms ProfiledGapStage.boundaryWordsAdjacent

end Erdos249257.SuffixCylinderProfiledGap
