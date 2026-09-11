import Erdos249257.SuffixCylinderProfiledGap

/-!
# Cutoff promotion for profiled suffix-cylinder gaps

At the feedback boundary `N = 2 * M + 1`, the protected strip lies below
the new binary head weight.  The lower sheet therefore promotes through a
false head bit, while endpoint separation puts the upper interval a full
strip width beyond that head and forces a true head bit.  This preserves the
profiled two-sheet state at cutoff `M + 1` without changing its carry gap.
-/

namespace Erdos249257.SuffixCylinderProfiledPromotion

open Erdos249257
open Erdos249257.HalfCarryReachability
open Erdos249257.HalfCarrySelectedWindow
open Erdos249257.FixedCoeffRewind
open Erdos249257.SelectedSuffixCylinder
open Erdos249257.SuffixCylinderPromotion
open Erdos249257.SuffixCylinderThreshold
open Erdos249257.SuffixCylinderInStrip
open Erdos249257.SuffixCylinderProfiledGap

/-- The square-root protected strip at an odd feedback boundary lies below
the next binary head weight. -/
theorem halfStripBound_two_mul_add_one_le_pow
    {M : ℕ} (hM : 4 ≤ M) :
    halfStripBound (2 * M + 1) ≤ 2 ^ M := by
  have hquad : 2 * M + 1 ≤ M ^ 2 := by
    nlinarith
  have hsqrt : Nat.sqrt (2 * M + 1) ≤ M := by
    calc
      Nat.sqrt (2 * M + 1) ≤ Nat.sqrt (M ^ 2) :=
        Nat.sqrt_le_sqrt hquad
      _ = M := Nat.sqrt_eq' M
  have hlinear : 2 * M + 4 ≤ 2 ^ M := by
    clear hquad hsqrt
    induction M, hM using Nat.le_induction with
    | base => norm_num
    | succ M hM ih =>
        rw [pow_succ]
        omega
  unfold halfStripBound
  omega

/-- Low-side promotion for a selected initial window, including the empty
window `R = 0`.  The existing literal prefix acquires a false head bit and
the suffix-cylinder endpoint is unchanged. -/
theorem selectedHalfWindowPromoteLow
    {M N R E : ℕ} (W : SelectedHalfWindow N R)
    (hM1N : M + 1 ≤ N) (pfx : HalfWord M)
    (hpfx : ∀ k (hk : 1 ≤ k) (hkR : k ≤ R),
      restrictWord ((Nat.le_succ M).trans hM1N) (W.word k hk hkR) = pfx)
    (hcyl : HasSuffixCylinderAt W
      ((Nat.le_succ M).trans hM1N) E)
    (hbelow : E ≤ 2 ^ (N - (M + 1))) :
    HasSuffixCylinderAt W hM1N E ∧
      ∀ k (hk : 1 ≤ k) (hkR : k ≤ R),
        restrictWord hM1N (W.word k hk hkR) =
          extendHalfWord pfx false := by
  classical
  rcases hcyl with ⟨_cylinderPrefix, hcyl⟩
  have hfalse : ∀ k (hk : 1 ≤ k) (hkR : k ≤ R),
      W.word k hk hkR ⟨M + 1, by omega⟩ = false := by
    intro k hk hkR
    cases hbit : W.word k hk hkR ⟨M + 1, by omega⟩
    · rfl
    · have hhead := headPower_le_wordSuffixNumeral_of_true hM1N
          (W.word k hk hkR) hbit
      have hendpoint := (hcyl k hk hkR).2
      change wordSuffixNumeral (W.word k hk hkR) M (N - M) + k = E
        at hendpoint
      change 2 ^ (N - (M + 1)) ≤
        wordSuffixNumeral (W.word k hk hkR) M (N - M) at hhead
      omega
  have hliteral : ∀ k (hk : 1 ≤ k) (hkR : k ≤ R),
      restrictWord hM1N (W.word k hk hkR) =
        extendHalfWord pfx false := by
    intro k hk hkR
    exact restrictWord_succ_eq_extendHalfWord hM1N
      (W.word k hk hkR) pfx false (hpfx k hk hkR)
        (hfalse k hk hkR)
  constructor
  · refine ⟨extendHalfWord pfx false, ?_⟩
    intro k hk hkR
    have hendpoint := (hcyl k hk hkR).2
    have hsplit := wordSuffixNumeral_split_head hM1N
      (W.word k hk hkR)
    rw [hfalse k hk hkR] at hsplit
    simp at hsplit
    constructor
    · exact hliteral k hk hkR
    · change wordSuffixNumeral (W.word k hk hkR) (M + 1)
          (N - (M + 1)) + k = E
      change wordSuffixNumeral (W.word k hk hkR) M (N - M) =
        wordSuffixNumeral (W.word k hk hkR) (M + 1)
          (N - (M + 1)) at hsplit
      change wordSuffixNumeral (W.word k hk hkR) M (N - M) + k = E
        at hendpoint
      omega
  · exact hliteral

/-- High-side promotion for an endpoint-indexed selected interval.  The
entire interval lies above the new binary head, so the literal prefix gains
a true bit and the endpoint loses exactly that head weight. -/
theorem selectedHalfIntervalPromoteHigh
    {M N L U E : ℕ} (W : SelectedHalfInterval N L U)
    (hM1N : M + 1 ≤ N) (pfx : HalfWord M)
    (hpfx : ∀ q (hqL : L ≤ q) (hqU : q ≤ U),
      restrictWord ((Nat.le_succ M).trans hM1N) (W.word q hqL hqU) = pfx)
    (hcyl : HasSuffixCylinderOnInterval W
      ((Nat.le_succ M).trans hM1N) E)
    (hmargin : 2 ^ (N - (M + 1)) + U ≤ E) :
    HasSuffixCylinderOnInterval W hM1N
        (E - 2 ^ (N - (M + 1))) ∧
      (∀ q (hqL : L ≤ q) (hqU : q ≤ U),
        restrictWord hM1N (W.word q hqL hqU) =
          extendHalfWord pfx true) ∧
      U ≤ E - 2 ^ (N - (M + 1)) := by
  classical
  rcases hcyl with ⟨_cylinderPrefix, hcyl⟩
  have htrue : ∀ q (hqL : L ≤ q) (hqU : q ≤ U),
      W.word q hqL hqU ⟨M + 1, by omega⟩ = true := by
    intro q hqL hqU
    cases hbit : W.word q hqL hqU ⟨M + 1, by omega⟩
    · have htail := wordSuffixNumeral_lt_headPower_of_false hM1N
          (W.word q hqL hqU) hbit
      have hendpoint := (hcyl q hqL hqU).2
      change wordSuffixNumeral (W.word q hqL hqU) M (N - M) + q = E
        at hendpoint
      change wordSuffixNumeral (W.word q hqL hqU) M (N - M) <
        2 ^ (N - (M + 1)) at htail
      omega
    · rfl
  have hliteral : ∀ q (hqL : L ≤ q) (hqU : q ≤ U),
      restrictWord hM1N (W.word q hqL hqU) =
        extendHalfWord pfx true := by
    intro q hqL hqU
    exact restrictWord_succ_eq_extendHalfWord hM1N
      (W.word q hqL hqU) pfx true (hpfx q hqL hqU)
        (htrue q hqL hqU)
  constructor
  · refine ⟨extendHalfWord pfx true, ?_⟩
    intro q hqL hqU
    have hendpoint := (hcyl q hqL hqU).2
    have hsplit := wordSuffixNumeral_split_head hM1N
      (W.word q hqL hqU)
    rw [htrue q hqL hqU] at hsplit
    simp at hsplit
    constructor
    · exact hliteral q hqL hqU
    · change wordSuffixNumeral (W.word q hqL hqU) (M + 1)
          (N - (M + 1)) + q = E - 2 ^ (N - (M + 1))
      change wordSuffixNumeral (W.word q hqL hqU) M (N - M) =
        2 ^ (N - (M + 1)) +
          wordSuffixNumeral (W.word q hqL hqU) (M + 1)
            (N - (M + 1)) at hsplit
      change wordSuffixNumeral (W.word q hqL hqU) M (N - M) + q = E
        at hendpoint
      omega
  · exact ⟨hliteral, by omega⟩

/-- At an odd feedback boundary, promote both live sheets of a profiled gap
through the next cutoff bit.  The gap and selected families are unchanged;
only their extracted literal prefixes and the upper suffix endpoint are
renormalized. -/
noncomputable def ProfiledGapStage.promoteCutoff
    {M N : ℕ} (T : ProfiledGapStage M N)
    (hM : 4 ≤ M) (hboundary : N = 2 * M + 1) :
    ProfiledGapStage (M + 1) N := by
  subst N
  have hM1N : M + 1 ≤ 2 * M + 1 := by omega
  have hstrip : halfStripBound (2 * M + 1) ≤ 2 ^ M :=
    halfStripBound_two_mul_add_one_le_pow hM
  have hheadEq : (2 * M + 1) - (M + 1) = M := by omega
  have hlowerBelow : T.gapLo - 1 ≤
      2 ^ ((2 * M + 1) - (M + 1)) := by
    rw [hheadEq]
    exact (Nat.pred_le T.gapLo).trans T.gap_order |>.trans T.gapHi_le
      |>.trans hstrip
  have hlower := selectedHalfWindowPromoteLow T.lower hM1N
    T.lowerPrefix T.lowerLiteral T.lowerCylinder hlowerBelow
  have hupperMargin :
      2 ^ ((2 * M + 1) - (M + 1)) + halfStripBound (2 * M + 1) ≤
        T.upperEndpoint := by
    rw [T.endpointSeparation, hheadEq]
    have holdExponent : (2 * M + 1) - M = M + 1 := by omega
    rw [holdExponent, pow_succ]
    omega
  have hupper := selectedHalfIntervalPromoteHigh T.upper hM1N
    T.upperPrefix T.upperLiteral T.upperCylinder hupperMargin
  exact {
    hMN := hM1N
    gapLo := T.gapLo
    gapHi := T.gapHi
    gapLo_pos := T.gapLo_pos
    gap_order := T.gap_order
    gapHi_le := T.gapHi_le
    lowerPrefix := extendHalfWord T.lowerPrefix false
    lower := T.lower
    lowerCylinder := hlower.1
    lowerLiteral := hlower.2
    upperPrefix := extendHalfWord T.upperPrefix true
    upperEndpoint := T.upperEndpoint -
      2 ^ ((2 * M + 1) - (M + 1))
    upper := T.upper
    upperCylinder := hupper.1
    upperLiteral := hupper.2.1
    upperCovers := hupper.2.2
    endpointSeparation := by
      rw [T.endpointSeparation, hheadEq]
      have holdExponent : (2 * M + 1) - M = M + 1 := by omega
      rw [holdExponent, pow_succ]
      omega
  }

#print axioms selectedHalfIntervalPromoteHigh
#print axioms ProfiledGapStage.promoteCutoff

end Erdos249257.SuffixCylinderProfiledPromotion
