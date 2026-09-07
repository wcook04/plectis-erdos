import Erdos249257.HalfCylinderPullbackCardPropagation

/-!
# Pullback-card escape is exactly the previous-middle staircase

The late-upper/right-run propagation lane can state its remaining producer
either as a lower bound on the signed pullback coordinate or as a
natural-number inequality at the preceding middle row.  The existing
middle-coordinate identity proves that these are the same producer, not two
independent routes.

This module records the reverse implication missing from the propagation
file and packages the exact equivalence.  It does not prove either producer,
cofinal half-greedy skips, half-membership, or Erdős #257.
-/

namespace Erdos249257.HalfCylinderPullbackCardPropagation

open HalfCylinderIntegerGreedy
open HalfUpperResetCriticalBand

/-- The signed-coordinate form of the late-upper producer, quantified over
the same actual largest-false, factor-range, and carry geometry as the
previous-middle staircase. -/
def LateUpperPullbackCardEscape : Prop :=
  ∀ (s d k : ℕ) (hs13 : 13 ≤ s) (hd5 : 5 ≤ d),
    IsLargestFalseRank (seamGreedyWord s) d →
    2 * s < 3 * d → s + k ≤ 2 * d + 1 →
    (seamAdjacentCut s (by omega)).successorCarries →
      (((seamWordSupport
          (seamGreedyWord (s + k + 1))).card + 2 : ℕ) : ℤ) ≤
        seamEarlierCriticalPullbackCoordinate s d k

/-- The natural previous-middle staircase supplies the signed pullback-card
margin.  This is the producer theorem from the propagation module, now
packaged at its fully quantified interface. -/
theorem lateUpperPullbackCardEscape_of_previousMiddleStaircaseEscape
    (hescape : LateUpperPreviousMiddleStaircaseEscape) :
    LateUpperPullbackCardEscape := by
  intro s d k hs13 hd5 hd hlate hfactor hcarry
  exact pullbackCard_of_lateUpperPreviousMiddleStaircaseEscape
    hescape hs13 hd hlate hfactor hcarry

/-- Conversely, the pullback-card margin already contains the whole
previous-middle staircase.  Substituting the exact middle coordinate leaves
only a linear rearrangement over the integers; casting back recovers the
natural-number producer without loss. -/
theorem previousMiddleStaircaseEscape_of_lateUpperPullbackCardEscape
    (hpull : LateUpperPullbackCardEscape) :
    LateUpperPreviousMiddleStaircaseEscape := by
  intro s d k hs13 hd5 hd hlate hfactor hcarry
  have hpullback := hpull s d k hs13 hd5 hd hlate hfactor hcarry
  have hcoordinate :=
    lateUpperReset_pullbackCoordinate_eq_previousMiddleCoordinate
      hs13 hd hlate hcarry (k := k)
  rw [hcoordinate] at hpullback
  have hNatZ :
      (((2 ^ ((2 * d + 2) - s) +
            (seamAdjacentCut d (by omega)).belowPulse + 4 +
            (seamWordSupport
              (seamGreedyWord (s + k + 1))).card + 2 : ℕ) : ℤ)) ≤
        (((4 * seamIntegerGreedyRemainder d +
            2 ^ ((2 * d + 1) - (s + k)) : ℕ) : ℤ)) := by
    push_cast at hpullback ⊢
    omega
  exact_mod_cast hNatZ

/-- **Exact route identification.**  In the actual late-upper geometry, the
pullback-card producer and the preceding-middle dyadic staircase are
equivalent.  Replacing one by the other cannot weaken the open #257 input. -/
theorem lateUpperPreviousMiddleStaircaseEscape_iff_pullbackCardEscape :
    LateUpperPreviousMiddleStaircaseEscape ↔
      LateUpperPullbackCardEscape := by
  constructor
  · exact lateUpperPullbackCardEscape_of_previousMiddleStaircaseEscape
  · exact previousMiddleStaircaseEscape_of_lateUpperPullbackCardEscape

#print axioms lateUpperPullbackCardEscape_of_previousMiddleStaircaseEscape
#print axioms previousMiddleStaircaseEscape_of_lateUpperPullbackCardEscape
#print axioms lateUpperPreviousMiddleStaircaseEscape_iff_pullbackCardEscape

end Erdos249257.HalfCylinderPullbackCardPropagation
