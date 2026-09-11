import Erdos249257.SuffixCylinderProfiledAdjacency

/-!
# Exact swallow arithmetic for a profiled suffix-cylinder gap

`ProfiledGapStage` propagates two selected cylinder sheets around a closed
carry gap.  This file isolates the exact arithmetic event at which neither
tracked sheet has a canonical parent for any carry in the next protected
strip.

For a current gap `[a,b]` and sheet coefficients `cL,cU`, the lower sheet
has parents `1,...,a-1` and the upper sheet has parents
`b+1,...,R`.  The canonical fixed-coefficient inverse therefore meets one
of the sheets at the next strip `1,...,B` exactly when

`cL + 3 <= 2*a` or `2*b + 1 <= B + cU`.

Its negation is the sharp swallow cell

`2*a <= cL + 2` and `B + cU <= 2*b`.

The second section records the corresponding two-row/base-four width
recurrence.  These are structural normal forms only.  They do not prove
that a canonical profiled gap avoids the swallow cell.  Moreover, a
`ProfiledGapStage` is a selected witness subtree, not an exhaustivity
certificate for all admissible words; identifying a tracked swallow with a
fatal half gap requires an additional canonical-adjacent-cut or restart
theorem.
-/

namespace Erdos249257.SuffixCylinderProfiledSwallow

open Erdos249257
open Erdos249257.HalfCarryReachability
open Erdos249257.HalfCarrySelectedWindow
open Erdos249257.FixedCoeffRewind
open Erdos249257.SelectedSuffixCylinder
open Erdos249257.SuffixCylinderProfiledGap
open Erdos249257.SuffixCylinderProfiledAdjacency

/-! ## Exact one-row survival and swallow cells -/

/-- Some target carry in `1,...,B` has its canonical `c`-parent in the
lower parent interval `1,...,a-1`. -/
def LowerParentSurvives (a c B : ℕ) : Prop :=
  ∃ q : ℕ, 1 ≤ q ∧ q ≤ B ∧ parent c q < a

/-- Some target carry in `1,...,B` has its canonical `c`-parent in the
upper parent interval `b+1,...,R`. -/
def UpperParentSurvives (b R c B : ℕ) : Prop :=
  ∃ q : ℕ, 1 ≤ q ∧ q ≤ B ∧ b < parent c q ∧ parent c q ≤ R

/-- At least one of the two tracked parent sheets supplies a canonical
parent for the next target strip. -/
def TrackedParentSurvives
    (a b R lowerCoeff upperCoeff nextBound : ℕ) : Prop :=
  LowerParentSurvives a lowerCoeff nextBound ∨
    UpperParentSurvives b R upperCoeff nextBound

theorem lowerParentSurvives_iff
    {a c B : ℕ} (hB : 1 ≤ B) :
    LowerParentSurvives a c B ↔ c + 3 ≤ 2 * a := by
  constructor
  · rintro ⟨q, hq, _hqB, hparent⟩
    have hrec := explicitParent_bitNat_recurrence c q
    omega
  · intro hcell
    refine ⟨1, le_rfl, hB, ?_⟩
    have hrec := explicitParent_bitNat_recurrence c 1
    have hbit :
        (if decide (explicitParentBitZ c 1 = 1) then 1 else 0) ≤ 1 := by
      split <;> omega
    omega

theorem upperParentSurvives_iff
    {b R c B : ℕ} (hB : 1 ≤ B) (hbuffer : B + c ≤ 2 * R) :
    UpperParentSurvives b R c B ↔ 2 * b + 1 ≤ B + c := by
  constructor
  · rintro ⟨q, _hq, hqB, hparentLo, hparentHi⟩
    have hrec := explicitParent_bitNat_recurrence c q
    have hbit :
        (if decide (explicitParentBitZ c q = 1) then 1 else 0) ≤ 1 := by
      split <;> omega
    omega
  · intro hcell
    refine ⟨B, hB, le_rfl, ?_, ?_⟩
    · have hrec := explicitParent_bitNat_recurrence c B
      omega
    · have hrec := explicitParent_bitNat_recurrence c B
      have hbit :
          (if decide (explicitParentBitZ c B = 1) then 1 else 0) ≤ 1 := by
        split <;> omega
      omega

/-- Exact survival normal form for two independently profiled sheets. -/
theorem trackedParentSurvives_iff
    {a b R lowerCoeff upperCoeff nextBound : ℕ}
    (hB : 1 ≤ nextBound)
    (hbuffer : nextBound + upperCoeff ≤ 2 * R) :
    TrackedParentSurvives a b R lowerCoeff upperCoeff nextBound ↔
      lowerCoeff + 3 ≤ 2 * a ∨
        2 * b + 1 ≤ nextBound + upperCoeff := by
  unfold TrackedParentSurvives
  rw [lowerParentSurvives_iff hB,
    upperParentSurvives_iff hB hbuffer]

/-- Exact no-carry form: both tracked sheets miss the entire next strip iff
the transformed closed gap covers that strip from both sides. -/
theorem not_trackedParentSurvives_iff
    {a b R lowerCoeff upperCoeff nextBound : ℕ}
    (hB : 1 ≤ nextBound)
    (hbuffer : nextBound + upperCoeff ≤ 2 * R) :
    ¬ TrackedParentSurvives a b R lowerCoeff upperCoeff nextBound ↔
      2 * a ≤ lowerCoeff + 2 ∧
        nextBound + upperCoeff ≤ 2 * b := by
  rw [trackedParentSurvives_iff hB hbuffer]
  omega

/-- Stage-specialized exact survival socket.  The coefficient profile is
kept separate: this predicate records only whether a canonical parent lands
in one of the two parent intervals carried by the stage. -/
def profiledGapStageTrackedNextParentSurvives
    {M N : ℕ} (T : ProfiledGapStage M N)
    (lowerCoeff upperCoeff : ℕ) : Prop :=
  TrackedParentSurvives T.gapLo T.gapHi (halfStripBound N)
    lowerCoeff upperCoeff (halfStripBound (N + 1))

theorem profiledGapStageTrackedNextParentSurvives_iff
    {M N lowerCoeff upperCoeff : ℕ} (T : ProfiledGapStage M N)
    (hbuffer : halfStripBound (N + 1) + upperCoeff ≤
      2 * halfStripBound N) :
    profiledGapStageTrackedNextParentSurvives T lowerCoeff upperCoeff ↔
      lowerCoeff + 3 ≤ 2 * T.gapLo ∨
        2 * T.gapHi + 1 ≤ halfStripBound (N + 1) + upperCoeff := by
  exact trackedParentSurvives_iff (by
    unfold halfStripBound
    omega) hbuffer

theorem not_profiledGapStageTrackedNextParentSurvives_iff
    {M N lowerCoeff upperCoeff : ℕ} (T : ProfiledGapStage M N)
    (hbuffer : halfStripBound (N + 1) + upperCoeff ≤
      2 * halfStripBound N) :
    ¬ profiledGapStageTrackedNextParentSurvives T lowerCoeff upperCoeff ↔
      2 * T.gapLo ≤ lowerCoeff + 2 ∧
        halfStripBound (N + 1) + upperCoeff ≤ 2 * T.gapHi := by
  exact not_trackedParentSurvives_iff (by
    unfold halfStripBound
    omega) hbuffer

/-- A one-point tracked gap cannot swallow the next strip when its boundary
prefixes are binary-adjacent.  Indeed, swallowing would force the next strip
bound to be at most three, while every half strip has width at least four. -/
theorem trackedParentSurvives_of_singletonGap
    {a R lowerCoeff upperCoeff nextBound : ℕ}
    (hbound : 4 ≤ nextBound)
    (hbuffer : nextBound + upperCoeff ≤ 2 * R)
    (hcoeff : lowerCoeff ≤ upperCoeff + 1) :
    TrackedParentSurvives a a R lowerCoeff upperCoeff nextBound := by
  by_contra hnone
  have hcell :=
    (not_trackedParentSurvives_iff (by omega : 1 ≤ nextBound) hbuffer).1
      hnone
  omega

/-- The initial one-hole profiled stage, and any later profiled stage whose
closed gap has returned to one point, always has a canonical parent in one
of its two tracked sheets at the next row. -/
theorem ProfiledGapStage.trackedNextParentSurvives_of_singletonGap
    {M N : ℕ} (T : ProfiledGapStage M N)
    (hadjacent : T.HasAdjacentPrefixes)
    (hsingleton : T.gapLo = T.gapHi) :
    profiledGapStageTrackedNextParentSurvives T
      (supportCoeff (wordSupport T.lowerPrefix) (N + 1))
      (supportCoeff (wordSupport T.upperPrefix) (N + 1)) := by
  have hcoeff :
      supportCoeff (wordSupport T.lowerPrefix) (N + 1) ≤
        supportCoeff (wordSupport T.upperPrefix) (N + 1) + 1 :=
    Erdos249257.SuffixCylinderProfiledAdjacency.ProfiledGapStage.lowerNextCoeff_le_upperNextCoeff_add_one
      T hadjacent
  have hupper :
      supportCoeff (wordSupport T.upperPrefix) (N + 1) ≤
        2 * Nat.sqrt (N + 1) :=
    supportCoeff_le_two_mul_sqrt (wordSupport T.upperPrefix) (N + 1)
  have hbuffer :
      halfStripBound (N + 1) +
          supportCoeff (wordSupport T.upperPrefix) (N + 1) ≤
        2 * halfStripBound N := by
    by_cases hN0 : N = 0
    · subst N
      norm_num [halfStripBound] at hupper ⊢
      omega
    · simpa using halfStripBound_add_coeff_le_two_mul_pred
        (n := N + 1)
        (c := supportCoeff (wordSupport T.upperPrefix) (N + 1))
        (by omega : 2 ≤ N + 1) hupper
  unfold profiledGapStageTrackedNextParentSurvives
  rw [← hsingleton]
  exact trackedParentSurvives_of_singletonGap
    (by unfold halfStripBound; omega) hbuffer hcoeff

/-! ## Exact one-row and macro width recurrences -/

/-- Signed lower endpoint of the transformed closed gap. -/
def nextGapLoZ (a lowerCoeff : ℕ) : ℤ :=
  2 * (a : ℤ) - (lowerCoeff : ℤ) - 1

/-- Signed upper endpoint of the transformed closed gap. -/
def nextGapHiZ (b upperCoeff : ℕ) : ℤ :=
  2 * (b : ℤ) - (upperCoeff : ℤ)

/-- Signed inclusive width of a closed interval. -/
def signedGapWidth (lo hi : ℤ) : ℤ := hi - lo + 1

/-- One profiled row doubles the old width and adds the signed coefficient
difference. -/
theorem signedGapWidth_next
    (a b lowerCoeff upperCoeff : ℕ) :
    signedGapWidth (nextGapLoZ a lowerCoeff)
        (nextGapHiZ b upperCoeff) =
      2 * signedGapWidth (a : ℤ) (b : ℤ) +
        (lowerCoeff : ℤ) - (upperCoeff : ℤ) := by
  simp only [signedGapWidth, nextGapLoZ, nextGapHiZ]
  ring

/-- Two consecutive profiled rows send the lower gap endpoint to this
base-four affine coordinate. -/
def macroGapLoZ (a lowerOddCoeff lowerEvenCoeff : ℕ) : ℤ :=
  4 * (a : ℤ) - 2 * (lowerOddCoeff : ℤ) -
    (lowerEvenCoeff : ℤ) - 3

/-- Two consecutive profiled rows send the upper gap endpoint to this
base-four affine coordinate. -/
def macroGapHiZ (b upperOddCoeff upperEvenCoeff : ℕ) : ℤ :=
  4 * (b : ℤ) - 2 * (upperOddCoeff : ℤ) -
    (upperEvenCoeff : ℤ)

/-- Exact two-row/base-four gap-width recurrence.  The combined row pulse
on one sheet is `2*oddCoeff + evenCoeff`. -/
theorem signedGapWidth_macro
    (a b lowerOddCoeff lowerEvenCoeff upperOddCoeff upperEvenCoeff : ℕ) :
    signedGapWidth
        (macroGapLoZ a lowerOddCoeff lowerEvenCoeff)
        (macroGapHiZ b upperOddCoeff upperEvenCoeff) =
      4 * signedGapWidth (a : ℤ) (b : ℤ) +
        (2 * (lowerOddCoeff : ℤ) + (lowerEvenCoeff : ℤ)) -
        (2 * (upperOddCoeff : ℤ) + (upperEvenCoeff : ℤ)) := by
  simp only [signedGapWidth, macroGapLoZ, macroGapHiZ]
  ring

/-- A macro-step swallow together with a coefficient-pulse difference at
most two forces the old gap to occupy at least one quarter of the next
strip, up to the sharp additive two.  This is the exact remaining
quarter-band branch; it does not assert that the branch is impossible. -/
theorem nextBound_le_four_gapWidth_add_two_of_macro_swallow
    {a b nextBound lowerOddCoeff lowerEvenCoeff
      upperOddCoeff upperEvenCoeff : ℕ}
    (hab : a ≤ b)
    (hpulse :
      2 * lowerOddCoeff + lowerEvenCoeff ≤
        2 * upperOddCoeff + upperEvenCoeff + 2)
    (hswallowLo :
      macroGapLoZ a lowerOddCoeff lowerEvenCoeff ≤ 1)
    (hswallowHi :
      (nextBound : ℤ) ≤
        macroGapHiZ b upperOddCoeff upperEvenCoeff) :
    nextBound ≤ 4 * (b - a + 1) + 2 := by
  have hwidth := signedGapWidth_macro a b lowerOddCoeff lowerEvenCoeff
    upperOddCoeff upperEvenCoeff
  have hcastWidth :
      signedGapWidth (a : ℤ) (b : ℤ) = (b - a + 1 : ℕ) := by
    simp only [signedGapWidth]
    rw [Nat.cast_add, Nat.cast_sub hab]
    push_cast
    ring
  rw [hcastWidth] at hwidth
  have hpulseZ :
      2 * (lowerOddCoeff : ℤ) + (lowerEvenCoeff : ℤ) ≤
        2 * (upperOddCoeff : ℤ) + (upperEvenCoeff : ℤ) + 2 := by
    exact_mod_cast hpulse
  have hspan :
      (nextBound : ℤ) ≤
        signedGapWidth
          (macroGapLoZ a lowerOddCoeff lowerEvenCoeff)
          (macroGapHiZ b upperOddCoeff upperEvenCoeff) := by
    unfold signedGapWidth
    omega
  have hboundZ :
      (nextBound : ℤ) ≤ 4 * (b - a + 1 : ℕ) + 2 := by
    rw [hwidth] at hspan
    omega
  exact_mod_cast hboundZ

#print axioms lowerParentSurvives_iff
#print axioms upperParentSurvives_iff
#print axioms trackedParentSurvives_iff
#print axioms not_trackedParentSurvives_iff
#print axioms profiledGapStageTrackedNextParentSurvives_iff
#print axioms not_profiledGapStageTrackedNextParentSurvives_iff
#print axioms trackedParentSurvives_of_singletonGap
#print axioms ProfiledGapStage.trackedNextParentSurvives_of_singletonGap
#print axioms signedGapWidth_next
#print axioms signedGapWidth_macro
#print axioms nextBound_le_four_gapWidth_add_two_of_macro_swallow

end Erdos249257.SuffixCylinderProfiledSwallow
