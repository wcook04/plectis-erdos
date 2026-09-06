import Erdos249257.HalfUpperResetCriticalBand
import Erdos249257.HalfCylinderLargestSkipInduction

/-!
# Reset square-root escape and the largest-skip crossing

This module turns the computationally discovered reset anti-concentration
pattern into an exact all-depth proof obligation.  The key integer threshold

`2 ^ ((d + 4) / 2) + 2 * d + 3`

is large enough to contain every reset which could feed a right branch at the
two-thirds crossing, but its square is at most `2 ^ (d + 5)` for `d ≥ 10`.
Thus square-root escape at every reset implies the local largest-skip socket,
which is already known to imply the desired half-membership endpoint.
-/

namespace Erdos249257

open Set Filter
open HalfCylinderIntegerGreedy
open HalfUpperResetCriticalBand

noncomputable section

/-- Signed deviation created by the branch at row `r`. -/
def seamResetDeviation (r : ℕ) : ℤ :=
  (seamIntegerGreedyRemainder (r + 1) : ℤ) -
    ((2 ^ (r + 1) : ℕ) : ℤ)

/-- A division-free integer envelope for a reset which can feed a right
branch at the two-thirds crossing of its largest false rank. -/
def resetCrossingBound (r : ℕ) : ℕ :=
  2 ^ ((r + 4) / 2) + 2 * r + 3

/-- The square formulation of reset square-root escape.  It is exactly the
irrational-exponent inequality `|dev| > 2 ^ ((r+5)/2)` after squaring. -/
def SeamResetSqrtEscape : Prop :=
  ∀ (r : ℕ) (hr5 : 5 ≤ r), 10 ≤ r →
    SeamGreedyUpperOrMiddleAt r hr5 →
      ((2 ^ (r + 5) : ℕ) : ℤ) < seamResetDeviation r ^ 2

/-- The intermediate integer form consumed by the crossing pullback. -/
def SeamResetCrossingBoundEscape : Prop :=
  ∀ (r : ℕ) (hr5 : 5 ≤ r), 10 ≤ r →
    SeamGreedyUpperOrMiddleAt r hr5 →
      resetCrossingBound r < (seamResetDeviation r).natAbs

private theorem resetCrossingBound_even_square_le (k : ℕ) :
    (2 ^ (7 + k) + 4 * k + 23) ^ 2 ≤ 2 ^ (15 + 2 * k) := by
  induction k with
  | zero => norm_num
  | succ k ih =>
      have hstep :
          2 ^ (7 + (k + 1)) + 4 * (k + 1) + 23 ≤
            2 * (2 ^ (7 + k) + 4 * k + 23) := by
        rw [show 7 + (k + 1) = (7 + k) + 1 by omega, pow_succ]
        nlinarith [show 4 ≤ 4 * k + 23 by omega]
      have hsq :
          (2 ^ (7 + (k + 1)) + 4 * (k + 1) + 23) ^ 2 ≤
            4 * (2 ^ (7 + k) + 4 * k + 23) ^ 2 := by
        nlinarith [show 0 ≤ 2 ^ (7 + (k + 1)) + 4 * (k + 1) + 23 by positivity]
      calc
        (2 ^ (7 + (k + 1)) + 4 * (k + 1) + 23) ^ 2 ≤
            4 * (2 ^ (7 + k) + 4 * k + 23) ^ 2 := hsq
        _ ≤ 4 * 2 ^ (15 + 2 * k) := by nlinarith
        _ = 2 ^ (15 + 2 * (k + 1)) := by
          rw [show 15 + 2 * (k + 1) = (15 + 2 * k) + 2 by omega,
            pow_succ, pow_succ]
          ring

private theorem resetCrossingBound_odd_square_le (k : ℕ) :
    (2 ^ (7 + k) + 4 * k + 25) ^ 2 ≤ 2 ^ (16 + 2 * k) := by
  induction k with
  | zero => norm_num
  | succ k ih =>
      have hstep :
          2 ^ (7 + (k + 1)) + 4 * (k + 1) + 25 ≤
            2 * (2 ^ (7 + k) + 4 * k + 25) := by
        rw [show 7 + (k + 1) = (7 + k) + 1 by omega, pow_succ]
        nlinarith [show 4 ≤ 4 * k + 25 by omega]
      have hsq :
          (2 ^ (7 + (k + 1)) + 4 * (k + 1) + 25) ^ 2 ≤
            4 * (2 ^ (7 + k) + 4 * k + 25) ^ 2 := by
        nlinarith [show 0 ≤ 2 ^ (7 + (k + 1)) + 4 * (k + 1) + 25 by positivity]
      calc
        (2 ^ (7 + (k + 1)) + 4 * (k + 1) + 25) ^ 2 ≤
            4 * (2 ^ (7 + k) + 4 * k + 25) ^ 2 := hsq
        _ ≤ 4 * 2 ^ (16 + 2 * k) := by nlinarith
        _ = 2 ^ (16 + 2 * (k + 1)) := by
          rw [show 16 + 2 * (k + 1) = (16 + 2 * k) + 2 by omega,
            pow_succ, pow_succ]
          ring

/-- The corrected crossing envelope fits below the square-root scale from
the first row relevant to the largest-skip socket. -/
theorem resetCrossingBound_square_le (r : ℕ) (hr : 10 ≤ r) :
    resetCrossingBound r ^ 2 ≤ 2 ^ (r + 5) := by
  obtain ⟨k, hk | hk⟩ := Nat.even_or_odd' (r - 10)
  · have hrEq : r = 10 + 2 * k := by omega
    rw [hrEq]
    unfold resetCrossingBound
    rw [show (10 + 2 * k + 4) / 2 = 7 + k by omega]
    have hbase : 2 ^ (7 + k) + 2 * (10 + 2 * k) + 3 =
        2 ^ (7 + k) + 4 * k + 23 := by omega
    rw [hbase, show 10 + 2 * k + 5 = 15 + 2 * k by omega]
    exact resetCrossingBound_even_square_le k
  · have hrEq : r = 11 + 2 * k := by omega
    rw [hrEq]
    unfold resetCrossingBound
    rw [show (11 + 2 * k + 4) / 2 = 7 + k by omega]
    have hbase : 2 ^ (7 + k) + 2 * (11 + 2 * k) + 3 =
        2 ^ (7 + k) + 4 * k + 25 := by omega
    rw [hbase, show 11 + 2 * k + 5 = 16 + 2 * k by omega]
    exact resetCrossingBound_odd_square_le k

/-- Exact power matching and correction absorption at either of the two
integer cells where a late rank crosses the two-thirds boundary. -/
private theorem crossingCell_power_and_correction
    {s d k : ℕ} (hd10 : 10 ≤ d) (hk : s = d + k + 1)
    (hlate : 2 * s < 3 * d) (hcross : 3 * d ≤ 2 * s + 2) :
    4 ^ k * 2 ^ ((d + 4) / 2) = 2 ^ (s - 1) ∧
      8 * 4 ^ (s - d) + 6 * s + 4 ≤
        12 * 4 ^ k * (2 * d - s + 4) := by
  have hk3 : 3 ≤ k := by omega
  have hpowTwo : 2 ≤ 4 ^ k := by
    calc
      2 ≤ 4 ^ 1 := by norm_num
      _ ≤ 4 ^ k := Nat.pow_le_pow_right (by norm_num) (by omega)
  have hcell : 3 * d = 2 * s + 1 ∨ 3 * d = 2 * s + 2 := by omega
  rcases hcell with hodd | heven
  · have hdEq : d = 2 * k + 3 := by omega
    have hsEq : s = 3 * k + 4 := by omega
    constructor
    · rw [hdEq, hsEq,
        show (2 * k + 3 + 4) / 2 = k + 3 by omega,
        show 3 * k + 4 - 1 = 3 * k + 3 by omega,
        show 4 ^ k = 2 ^ (2 * k) by
          rw [show 4 = 2 ^ 2 by norm_num, ← pow_mul], ← pow_add]
      congr 1
      omega
    · rw [hdEq, hsEq,
        show 3 * k + 4 - (2 * k + 3) = k + 1 by omega,
        pow_succ,
        show 2 * (2 * k + 3) - (3 * k + 4) + 4 = k + 6 by omega]
      nlinarith
  · have hdEq : d = 2 * k + 4 := by omega
    have hsEq : s = 3 * k + 5 := by omega
    constructor
    · rw [hdEq, hsEq,
        show (2 * k + 4 + 4) / 2 = k + 4 by omega,
        show 3 * k + 5 - 1 = 3 * k + 4 by omega,
        show 4 ^ k = 2 ^ (2 * k) by
          rw [show 4 = 2 ^ 2 by norm_num, ← pow_mul], ← pow_add]
      congr 1
      omega
    · rw [hdEq, hsEq,
        show 3 * k + 5 - (2 * k + 4) = k + 1 by omega,
        pow_succ,
        show 2 * (2 * k + 4) - (3 * k + 5) + 4 = k + 7 by omega]
      nlinarith

/-- A right branch at the first non-late cell pulls all the way back to a
small deviation at the reset which created the largest false rank.  The
proof reconstructs the intervening right run from the actual greedy support
and uses the exact affine pulse charge; there is no hypothetical tail. -/
theorem resetDeviation_le_crossingBound_of_late_right_crossing
    {s d : ℕ} (hs14 : 14 ≤ s)
    (hd : IsLargestFalseRank (seamGreedyWord s) d)
    (hlate : 2 * s < 3 * d) (hcross : 3 * d ≤ 2 * (s + 1))
    (hR : ¬ SeamGreedyUpperOrMiddleAt s (by omega)) :
    (seamResetDeviation d).natAbs ≤ resetCrossingBound d := by
  classical
  have hd10 : 10 ≤ d := by omega
  have hd1s : d + 1 ≤ s := Nat.succ_le_iff.mpr hd.2.1
  let k := s - (d + 1)
  have hkrow : d + 1 + k = s := by
    dsimp [k]
    exact Nat.add_sub_of_le hd1s
  have hsk : s = d + k + 1 := by omega
  obtain ⟨u, hu, hbase, hsupp⟩ :=
    exists_lowerPrefix_with_backward_support_of_lateLargestFalse
      (s := s) (d := d) (by omega) hd hlate
  have hdnot : d ∉ seamWordSupport (seamGreedyWord (d + 1)) := by
    rw [hbase]
    intro hdu
    exact (Nat.lt_irrefl d) (hu d hdu).2
  have hfalse :
      SeamRowWord.terminal (by omega) (seamGreedyWord (d + 1)) = false :=
    (not_mem_seamWordSupport_iff_false
      (seamGreedyWord (d + 1)) (by omega) (by omega)).mp hdnot
  have hreset : SeamGreedyUpperOrMiddleAt d (by omega) :=
    (seamGreedy_terminal_false_iff_upperOrMiddle d (by omega)).mp hfalse
  have hrun : ∀ (t : ℕ) (ht5 : 5 ≤ t), d + 1 ≤ t → t < s →
      ¬ (seamAdjacentCut t ht5).successorCarries ∧
        (seamAdjacentCut t ht5).terminalWeight ≤
          4 * (seamAdjacentCut t ht5).remainder +
            (seamPerturbedFamily t (by omega)).gap -
            (seamAdjacentCut t ht5).belowPulse := by
    intro t ht5 hdt hts
    exact seamRightBranch_of_fullSuffix
      (B := d + 1) (s := s) (t := t) (u := u) (by omega)
      (by
        intro e he
        exact ⟨(hu e he).1, (hu e he).2.trans (Nat.lt_succ_self d)⟩)
      hsupp hdt hts
  have hnotUM : ∀ (t : ℕ) (ht5 : 5 ≤ t), d + 1 ≤ t → t < s →
      ¬ SeamGreedyUpperOrMiddleAt t ht5 := by
    intro t ht5 hdt hts hUM
    have hpair := hrun t ht5 hdt hts
    rcases hUM with hcarry | ⟨hncarry, hmiddle⟩
    · exact hpair.1 hcarry
    · exact (Nat.not_lt_of_ge hpair.2) hmiddle
  let X : ℕ → ℤ := fun j ↦
    (seamIntegerGreedyRemainder (d + j + 1) : ℤ) -
      ((2 ^ (d + j + 1) : ℕ) : ℤ)
  let pulse : ℕ → ℕ := fun j ↦
    (seamAdjacentCut (d + j + 1) (by omega)).belowPulse
  let C := affineRightRunCharge pulse k
  have hrec : ∀ j : ℕ, j < k →
      X (j + 1) = 4 * X j - (pulse j : ℤ) - 4 := by
    intro j hj
    have hrowLt : d + j + 1 < s := by
      dsimp [k] at hj
      omega
    have hno := hnotUM (d + j + 1) (by omega) (by omega) hrowLt
    simpa [X, pulse, Nat.add_assoc] using
      rightBranch_excess_succ_eq (s := d + j + 1) (by omega) hno
  have hexact0 := affineRightExcess_exactIterate X pulse k hrec
  have hexact :
      ((seamIntegerGreedyRemainder s : ℤ) -
          ((2 ^ s : ℕ) : ℤ)) + (C : ℤ) =
        ((4 ^ k : ℕ) : ℤ) * seamResetDeviation d := by
    rw [hsk]
    simpa [X, C, seamResetDeviation] using hexact0
  have hcharge0 := seamRightRunCharge_lt_row_mul_four_pow
    (d := d) (k := k) (by omega)
  have hcharge : C < (s - 1) * 4 ^ k := by
    have hdk : d + k = s - 1 := by omega
    rw [← hdk]
    simpa [C, pulse] using hcharge0
  have hwindow := rightBranch_remainder_window
    (s := s) (d := d) (by omega) hd hlate hR
  let w : ℤ := (seamIntegerGreedyRemainder s : ℤ) -
    ((2 ^ s : ℕ) : ℤ)
  have hpowSucc : (2 : ℕ) ^ (s + 1) = 2 * 2 ^ s := by
    rw [pow_succ]
    ring
  have hpowPrev : (2 : ℕ) ^ s = 2 * 2 ^ (s - 1) := by
    calc
      2 ^ s = 2 ^ ((s - 1) + 1) := by congr 1 <;> omega
      _ = 2 ^ (s - 1) * 2 := by rw [pow_succ]
      _ = 2 * 2 ^ (s - 1) := by ring
  have hwLower : (1 : ℤ) - ((2 ^ (s - 1) : ℕ) : ℤ) ≤ w := by
    have hz : (((2 ^ (s + 1) : ℕ) : ℤ) + 4) ≤
        4 * (seamIntegerGreedyRemainder s : ℤ) := by
      exact_mod_cast hwindow.1
    have hpowSuccZ := congrArg (fun n : ℕ ↦ (n : ℤ)) hpowSucc
    have hpowPrevZ := congrArg (fun n : ℕ ↦ (n : ℤ)) hpowPrev
    push_cast at hz hpowSuccZ hpowPrevZ
    dsimp [w]
    linarith only [hz, hpowSuccZ, hpowPrevZ]
  have hwUpper :
      12 * w < 6 * (((2 ^ s : ℕ) : ℤ)) +
        8 * (((4 ^ (s - d) : ℕ) : ℤ)) + 6 * (s : ℤ) + 4 := by
    have hz := hwindow.2
    have hz' :
        12 * (seamIntegerGreedyRemainder s : ℤ) +
            3 * (((2 ^ (s + 1) : ℕ) : ℤ)) <
          4 * (3 * (((2 ^ (s + 1) : ℕ) : ℤ)) +
              2 * (((4 ^ (s - d) : ℕ) : ℤ)) + 4) +
            3 * (2 * ((s - 2 : ℕ) : ℤ)) := by
      exact_mod_cast hz
    have hpowSuccZ := congrArg (fun n : ℕ ↦ (n : ℤ)) hpowSucc
    push_cast at hz' hpowSuccZ
    have hs2 : s - 2 + 2 = s := Nat.sub_add_cancel (by omega)
    have hs2Z := congrArg (fun n : ℕ ↦ (n : ℤ)) hs2
    push_cast at hs2Z
    dsimp [w]
    linarith only [hz', hpowSuccZ, hs2Z]
  have hcell := crossingCell_power_and_correction
    (s := s) (d := d) (k := k) hd10 hsk hlate (by omega)
  have hpowerZ := congrArg (fun n : ℕ ↦ (n : ℤ)) hcell.1
  have h2ds : s ≤ 2 * d := by omega
  have hcorrCoreCast : (((2 * d - s : ℕ) : ℤ)) =
      2 * (d : ℤ) - (s : ℤ) := by
    rw [Nat.cast_sub h2ds]
    push_cast
    ring
  have hcorrZ0 :
      (((8 * 4 ^ (s - d) + 6 * s + 4 : ℕ) : ℤ)) ≤
        (((12 * 4 ^ k * (2 * d - s + 4) : ℕ) : ℤ)) := by
    exact_mod_cast hcell.2
  have hcorrZ :
      8 * (((4 ^ (s - d) : ℕ) : ℤ)) + 6 * (s : ℤ) + 4 ≤
        12 * (((4 ^ k : ℕ) : ℤ)) *
          (2 * (d : ℤ) - (s : ℤ) + 4) := by
    push_cast at hcorrZ0
    rw [hcorrCoreCast] at hcorrZ0
    exact hcorrZ0
  have hpowPrevZ := congrArg (fun n : ℕ ↦ (n : ℤ)) hpowPrev
  push_cast at hpowerZ hpowPrevZ
  let P : ℤ := ((4 ^ k : ℕ) : ℤ)
  let A : ℤ := ((2 ^ ((d + 4) / 2) : ℕ) : ℤ)
  let corr : ℤ := 2 * (d : ℤ) - (s : ℤ) + 4
  have hbaseUpper :
      6 * (((2 ^ s : ℕ) : ℤ)) +
          (8 * (((4 ^ (s - d) : ℕ) : ℤ)) + 6 * (s : ℤ) + 4) ≤
        12 * P * (A + corr) := by
    calc
      6 * (((2 ^ s : ℕ) : ℤ)) +
          (8 * (((4 ^ (s - d) : ℕ) : ℤ)) + 6 * (s : ℤ) + 4) ≤
          6 * (((2 ^ s : ℕ) : ℤ)) + 12 * P * corr := by
            simpa only [P, corr, add_comm] using
              add_le_add_left hcorrZ (6 * (((2 ^ s : ℕ) : ℤ)))
      _ = 12 * P * (A + corr) := by
        dsimp [P, A, corr]
        rw [hpowPrevZ, ← hpowerZ]
        ring
  have hwScaled : w < P * (A + corr) := by
    have h12 : 12 * w < 12 * P * (A + corr) := by
      linarith only [hwUpper, hbaseUpper]
    linarith only [h12]
  have hpowPos : (0 : ℤ) < ((4 ^ k : ℕ) : ℤ) := by positivity
  have hPpos : (0 : ℤ) < P := by simpa [P] using hpowPos
  have hs1Cast : (((s - 1 : ℕ) : ℤ)) = (s : ℤ) - 1 := by
    rw [Nat.cast_sub (by omega)]
    push_cast
    rfl
  have hchargeZ0 : (C : ℤ) <
      ((s - 1 : ℕ) : ℤ) * ((4 ^ k : ℕ) : ℤ) := by exact_mod_cast hcharge
  have hchargeZ : (C : ℤ) < ((s : ℤ) - 1) * P := by
    simpa [P, hs1Cast] using hchargeZ0
  have hexactW : w + (C : ℤ) = P * seamResetDeviation d := by
    simpa [w, P] using hexact
  by_cases hdev : 0 ≤ seamResetDeviation d
  · have hscaledDev :
        P * seamResetDeviation d < P * (A + 2 * (d : ℤ) + 3) := by
      calc
        P * seamResetDeviation d = w + (C : ℤ) := hexactW.symm
        _ < P * (A + corr) + ((s : ℤ) - 1) * P :=
          add_lt_add hwScaled hchargeZ
        _ = P * (A + 2 * (d : ℤ) + 3) := by
          dsimp [corr]
          ring
    have hdevLtZ : seamResetDeviation d < A + 2 * (d : ℤ) + 3 :=
      lt_of_mul_lt_mul_left hscaledDev hPpos.le
    have hboundCast : ((resetCrossingBound d : ℕ) : ℤ) =
        A + 2 * (d : ℤ) + 3 := by
      simp [resetCrossingBound, A]
    have hdevLt : seamResetDeviation d < (resetCrossingBound d : ℕ) := by
      rwa [hboundCast]
    have habsCast : (((seamResetDeviation d).natAbs : ℕ) : ℤ) =
        seamResetDeviation d := Int.natAbs_of_nonneg hdev
    have habsLt : (seamResetDeviation d).natAbs < resetCrossingBound d := by
      exact_mod_cast (habsCast ▸ hdevLt)
    omega
  · have hdevNeg : seamResetDeviation d < 0 := lt_of_not_ge hdev
    have hscaledNeg : P * (-seamResetDeviation d) < P * A := by
      have hCnonneg : (0 : ℤ) ≤ (C : ℤ) := by positivity
      have hPA : P * A = ((2 ^ (s - 1) : ℕ) : ℤ) := by
        simpa [P, A] using hpowerZ
      calc
        P * (-seamResetDeviation d) = -(P * seamResetDeviation d) := by ring
        _ = -(w + (C : ℤ)) := by rw [hexactW]
        _ ≤ -w := by linarith only [hCnonneg]
        _ < P * A := by
          rw [hPA]
          linarith only [hwLower]
    have hnegLt : -seamResetDeviation d < A :=
      lt_of_mul_lt_mul_left hscaledNeg hPpos.le
    have habsCast : (((seamResetDeviation d).natAbs : ℕ) : ℤ) =
        -seamResetDeviation d := Int.ofNat_natAbs_of_nonpos hdevNeg.le
    have habsLt : (seamResetDeviation d).natAbs < resetCrossingBound d := by
      have hpowLt : (seamResetDeviation d).natAbs <
          2 ^ ((d + 4) / 2) := by
        dsimp [A] at hnegLt
        exact_mod_cast (habsCast ▸ hnegLt)
      unfold resetCrossingBound
      omega
    omega
/-- Square-root escape implies the purely integral crossing-bound escape. -/
theorem SeamResetSqrtEscape.crossingBoundEscape
    (hsqrt : SeamResetSqrtEscape) : SeamResetCrossingBoundEscape := by
  intro r hr5 hr10 hreset
  have hscale := hsqrt r hr5 hr10 hreset
  have hbound := resetCrossingBound_square_le r hr10
  have hscaleNat : 2 ^ (r + 5) < (seamResetDeviation r).natAbs ^ 2 := by
    have hcast :
        ((((seamResetDeviation r).natAbs ^ 2 : ℕ) : ℤ)) =
          seamResetDeviation r ^ 2 := by simp
    rw [← hcast] at hscale
    exact_mod_cast hscale
  exact lt_of_pow_lt_pow_left' 2 (lt_of_le_of_lt hbound hscaleNat)

/-- The missing boundary rank in a late largest-false decomposition was
created by an actual upper or middle reset at that row. -/
theorem upperOrMiddleAt_largestFalseRank
    {s d : ℕ} (hs5 : 5 ≤ s) (hd5 : 5 ≤ d)
    (hd : IsLargestFalseRank (seamGreedyWord s) d)
    (hlate : 2 * s < 3 * d) :
    SeamGreedyUpperOrMiddleAt d hd5 := by
  classical
  obtain ⟨u, hu, hbase, _hsupp⟩ :=
    exists_lowerPrefix_with_backward_support_of_lateLargestFalse
      hs5 hd hlate
  have hdnot : d ∉ seamWordSupport (seamGreedyWord (d + 1)) := by
    rw [hbase]
    intro hdu
    exact (Nat.lt_irrefl d) (hu d hdu).2
  have hfalse :
      SeamRowWord.terminal (by omega) (seamGreedyWord (d + 1)) = false :=
    (not_mem_seamWordSupport_iff_false
      (seamGreedyWord (d + 1)) (by omega) (by omega)).mp hdnot
  exact (seamGreedy_terminal_false_iff_upperOrMiddle d hd5).mp hfalse

/-- Crossing-bound escape closes the exact first-crossing socket. -/
theorem SeamResetCrossingBoundEscape.largestSkipLateStepSocket
    (hescape : SeamResetCrossingBoundEscape) : LargestSkipLateStepSocket := by
  intro s d hs14 hd hlate
  by_cases hnext : 2 * (s + 1) < 3 * d
  · exact Or.inl hnext
  · right
    by_contra hR
    have hcross : 3 * d ≤ 2 * (s + 1) := by omega
    have hd10 : 10 ≤ d := by omega
    have hreset := upperOrMiddleAt_largestFalseRank
      (s := s) (d := d) (by omega) (by omega) hd hlate
    have hlarge := hescape d (by omega) hd10 hreset
    have hsmall := resetDeviation_le_crossingBound_of_late_right_crossing
      (s := s) (d := d) hs14 hd hlate hcross hR
    omega

/-- Reset square-root escape is therefore sufficient for the local socket. -/
theorem SeamResetSqrtEscape.largestSkipLateStepSocket
    (hsqrt : SeamResetSqrtEscape) : LargestSkipLateStepSocket :=
  hsqrt.crossingBoundEscape.largestSkipLateStepSocket

/-- **Reset–crossing unification.**  The all-depth square-root escape of the
actual reset deviations implies the desired Erdős #257 half-membership
endpoint. -/
theorem half_mem_mersenneAchievementSet_of_resetSqrtEscape
    (hsqrt : SeamResetSqrtEscape) :
    (1 / 2 : ℝ) ∈ mersenneAchievementSet :=
  half_mem_mersenneAchievementSet_of_largestSkipLateStepSocket
    hsqrt.largestSkipLateStepSocket

#print axioms resetCrossingBound_square_le
#print axioms resetDeviation_le_crossingBound_of_late_right_crossing
#print axioms SeamResetCrossingBoundEscape.largestSkipLateStepSocket
#print axioms half_mem_mersenneAchievementSet_of_resetSqrtEscape

end

end Erdos249257
