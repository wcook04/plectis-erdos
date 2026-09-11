import Erdos249257.SuffixCylinderProfiledPromotionAdjacency

/-!
# Automatic stepping for profiled suffix-cylinder gaps

The core profiled successor takes an explicit coefficient profile and the
standard divisor buffer separately.  At a ready cutoff both are automatic:
the literal prefixes determine the two coefficients, and the square-root
coefficient envelope supplies the buffer.  This file packages the genuinely
remaining arithmetic cell and provides one-step and feedback-boundary
constructors which preserve binary adjacency.
-/

namespace Erdos249257.SuffixCylinderProfiledGap

open Erdos249257
open Erdos249257.HalfCarryReachability
open Erdos249257.HalfCarrySelectedWindow
open Erdos249257.SelectedSuffixCylinder
open Erdos249257.SuffixCylinderProfiledGap
open Erdos249257.SuffixCylinderProfiledAdjacency
open Erdos249257.SuffixCylinderProfiledPromotion
open Erdos249257.SuffixCylinderProfiledPromotionAdjacency

/-- The lower-sheet coefficient forced by the retained literal prefix at the
next row. -/
noncomputable def ProfiledGapStage.lowerNextCoeff
    {M N : ℕ} (T : ProfiledGapStage M N) : ℕ :=
  supportCoeff (wordSupport T.lowerPrefix) (N + 1)

/-- The upper-sheet coefficient forced by the retained literal prefix at the
next row. -/
noncomputable def ProfiledGapStage.upperNextCoeff
    {M N : ℕ} (T : ProfiledGapStage M N) : ℕ :=
  supportCoeff (wordSupport T.upperPrefix) (N + 1)

/-- The four non-generic inequalities required to retain both profiled sheets
through the next row.  Coefficient production and the divisor buffer are not
fields: they follow automatically from readiness and the universal
square-root envelope. -/
structure ProfiledGapStage.NextArithmetic
    {M N : ℕ} (T : ProfiledGapStage M N) : Prop where
  childLoPos : 1 ≤ 2 * T.gapLo - T.lowerNextCoeff - 1
  upperCoeffFits : T.upperNextCoeff ≤ 2 * T.gapHi
  childOrder :
    2 * T.gapLo - T.lowerNextCoeff - 1 ≤
      2 * T.gapHi - T.upperNextCoeff
  childHiStrip :
    2 * T.gapHi - T.upperNextCoeff ≤ halfStripBound (N + 1)

/-- The upper prefix coefficient satisfies the universal divisor envelope. -/
theorem ProfiledGapStage.upperNextCoeff_le_two_mul_sqrt
    {M N : ℕ} (T : ProfiledGapStage M N) :
    T.upperNextCoeff ≤ 2 * Nat.sqrt (N + 1) := by
  exact supportCoeff_le_two_mul_sqrt (wordSupport T.upperPrefix) (N + 1)

/-- The standard inverse-parent buffer is automatic for every positive
current row. -/
theorem ProfiledGapStage.upperNextBuffer
    {M N : ℕ} (T : ProfiledGapStage M N) (hN : 1 ≤ N) :
    halfStripBound (N + 1) + T.upperNextCoeff ≤
      2 * halfStripBound N := by
  simpa [ProfiledGapStage.upperNextCoeff] using
    halfStripBound_add_coeff_le_two_mul_pred
      (n := N + 1) (c := T.upperNextCoeff) (by omega)
      T.upperNextCoeff_le_two_mul_sqrt

/-- A ready profiled stage advances from exactly its arithmetic cell; the
per-sheet coefficient profile and upper buffer are synthesized internally. -/
noncomputable def ProfiledGapStage.advanceOfReady
    {M N : ℕ} (T : ProfiledGapStage M N)
    (hN : 1 ≤ N) (hready : T.Ready) (hnext : T.NextArithmetic) :
    ProfiledGapStage M (N + 1) :=
  T.advanceOfNextCoeffProfile hN
    (T.hasNextCoeffProfile_of_ready hready)
    hnext.childLoPos hnext.upperCoeffFits hnext.childOrder
    hnext.childHiStrip (T.upperNextBuffer hN)

/-- Automatic ready stepping preserves the adjacent-prefix invariant. -/
theorem ProfiledGapStage.advanceOfReady_hasAdjacentPrefixes
    {M N : ℕ} (T : ProfiledGapStage M N)
    (hadjacent : T.HasAdjacentPrefixes)
    (hN : 1 ≤ N) (hready : T.Ready) (hnext : T.NextArithmetic) :
    (T.advanceOfReady hN hready hnext).HasAdjacentPrefixes := by
  exact T.advanceOfNextCoeffProfile_hasAdjacentPrefixes hadjacent hN
    (T.hasNextCoeffProfile_of_ready hready)
    hnext.childLoPos hnext.upperCoeffFits hnext.childOrder
    hnext.childHiStrip (T.upperNextBuffer hN)

/-- Promoting at an odd feedback boundary makes the resulting cutoff ready
for the next coefficient row. -/
theorem ProfiledGapStage.promoteCutoff_ready
    {M N : ℕ} (T : ProfiledGapStage M N)
    (hM : 4 ≤ M) (hboundary : N = 2 * M + 1) :
    (T.promoteCutoff hM hboundary).Ready := by
  unfold ProfiledGapStage.Ready
  omega

/-- One complete feedback-boundary operation: promote the cutoff, then take
the automatically profiled next row under the promoted arithmetic cell. -/
noncomputable def ProfiledGapStage.promoteThenAdvance
    {M N : ℕ} (T : ProfiledGapStage M N)
    (hM : 4 ≤ M) (hboundary : N = 2 * M + 1)
    (hnext : (T.promoteCutoff hM hboundary).NextArithmetic) :
    ProfiledGapStage (M + 1) (N + 1) :=
  (T.promoteCutoff hM hboundary).advanceOfReady
    (by omega) (T.promoteCutoff_ready hM hboundary) hnext

/-- The complete promote-then-advance operation preserves binary adjacency. -/
theorem ProfiledGapStage.promoteThenAdvance_hasAdjacentPrefixes
    {M N : ℕ} (T : ProfiledGapStage M N)
    (hadjacent : T.HasAdjacentPrefixes)
    (hM : 4 ≤ M) (hboundary : N = 2 * M + 1)
    (hnext : (T.promoteCutoff hM hboundary).NextArithmetic) :
    (T.promoteThenAdvance hM hboundary hnext).HasAdjacentPrefixes := by
  apply ProfiledGapStage.advanceOfReady_hasAdjacentPrefixes
  exact T.promoteCutoff_hasAdjacentPrefixes hadjacent hM hboundary

#print axioms ProfiledGapStage.upperNextBuffer
#print axioms ProfiledGapStage.advanceOfReady
#print axioms ProfiledGapStage.advanceOfReady_hasAdjacentPrefixes
#print axioms ProfiledGapStage.promoteCutoff_ready
#print axioms ProfiledGapStage.promoteThenAdvance
#print axioms ProfiledGapStage.promoteThenAdvance_hasAdjacentPrefixes

end Erdos249257.SuffixCylinderProfiledGap
