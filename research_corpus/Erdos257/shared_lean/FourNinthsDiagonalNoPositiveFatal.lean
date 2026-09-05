import Erdos257PeriodNoncollapse.GreedyAchievementSet

/-!
# The four-ninths diagonal and its two surviving escape mechanisms

This module formalizes the exact integer diagonal used by the positive
totient identity at `4 / 9`.  It does not prove that the diagonal stays
nonnegative, and therefore does not settle Erdős #257.

The declarations below do three proof-bearing jobs:

* execute and certify the forced initial diagonal word;
* show that an unselected step can cross below zero only after the available
  remainder has fallen below half of the selected-count reserve;
* certify the rational anchor-budget contradiction at the final positive
  boundary phase.

The remaining producer is global: exclude the last small selected margin
whose later divisor load can exhaust that reserve.
-/

namespace Erdos257PeriodNoncollapse

/-- The paired binary source pulse for `4 / 9 = 0.(011100)₂`. -/
def fourNinthsPairPulse (d : ℕ) : ℕ :=
  if d % 3 = 0 then 0 else if d % 3 = 1 then 1 else 3

/-- A finite executable state for the diagonal quotient recurrence. -/
structure FourNinthsDiagonalState where
  bits : List Bool
  rho : ℤ
deriving DecidableEq, Repr

/-- Read a one-based support bit from a finite diagonal state. -/
def fourNinthsStateBit (s : FourNinthsDiagonalState) (a : ℕ) : ℕ :=
  if s.bits[a - 1]? = some true then 1 else 0

/-- The proper-divisor load at the paired rows `2d-1, 2d`. -/
def fourNinthsDiagonalLoad (s : FourNinthsDiagonalState) (d : ℕ) : ℕ :=
  2 * ((List.range d).map (fun a =>
      if a ∣ 2 * d - 1 then fourNinthsStateBit s a else 0)).sum +
    ((List.range d).map (fun a =>
      if a ∣ 2 * d then fourNinthsStateBit s a else 0)).sum

/-- One exact quotient-greedy diagonal step. -/
def fourNinthsDiagonalStep
    (s : FourNinthsDiagonalState) : FourNinthsDiagonalState :=
  let d := s.bits.length + 1
  let T : ℤ :=
    4 * s.rho + (fourNinthsPairPulse d : ℤ) -
      (fourNinthsDiagonalLoad s d : ℤ)
  let coin : ℤ := ((2 ^ d + 1 : ℕ) : ℤ)
  let take : Bool := decide (coin ≤ T)
  { bits := s.bits ++ [take]
    rho := if take then T - coin else T }

/-- The diagonal state after `d` decisions. -/
def fourNinthsDiagonalState : ℕ → FourNinthsDiagonalState
  | 0 => ⟨[], 0⟩
  | d + 1 => fourNinthsDiagonalStep (fourNinthsDiagonalState d)

/-- Exact kernel evaluation of the first twelve decisions and remainders.
In particular, ranks `2`, `4`, and `12` are forced selected anchors. -/
theorem fourNinthsDiagonalState_twelve :
    fourNinthsDiagonalState 12 =
      ⟨[false, true, false, true, true, false,
        true, true, false, false, false, true], 2460⟩ := by
  decide

/-- Appending one diagonal decision leaves every already-existing positive
support bit unchanged. -/
theorem fourNinthsDiagonalStep_preserves_existing_bit
    (s : FourNinthsDiagonalState) {a : ℕ} (ha1 : 1 ≤ a)
    (ha : a ≤ s.bits.length) :
    fourNinthsStateBit (fourNinthsDiagonalStep s) a =
      fourNinthsStateBit s a := by
  have hindex : a - 1 < s.bits.length := by omega
  simp [fourNinthsDiagonalStep, fourNinthsStateBit,
    List.getElem?_append, hindex]

/-- The finite state after `d` diagonal decisions has exactly `d` bits. -/
theorem fourNinthsDiagonalState_bits_length (d : ℕ) :
    (fourNinthsDiagonalState d).bits.length = d := by
  induction d with
  | zero => rfl
  | succ d ih =>
      simp [fourNinthsDiagonalState, fourNinthsDiagonalStep, ih]

/-- The forced first bit of every finite exact diagonal state is unselected. -/
theorem fourNinthsDiagonalState_bit_one (d : ℕ) :
    fourNinthsStateBit (fourNinthsDiagonalState d) 1 = 0 := by
  induction d with
  | zero => rfl
  | succ d ih =>
      by_cases hzero : d = 0
      · subst d
        decide
      · have hd : 1 ≤ d := Nat.one_le_iff_ne_zero.mpr hzero
        have hlen : 1 ≤ (fourNinthsDiagonalState d).bits.length := by
          rw [fourNinthsDiagonalState_bits_length]
          exact hd
        rw [fourNinthsDiagonalState,
          fourNinthsDiagonalStep_preserves_existing_bit _ (by omega) hlen]
        exact ih

/-- The paired source pulse is three exactly in phase `2 mod 3`. -/
theorem fourNinthsPairPulse_eq_three_iff (d : ℕ) :
    fourNinthsPairPulse d = 3 ↔ d % 3 = 2 := by
  unfold fourNinthsPairPulse
  have hmod : d % 3 < 3 := Nat.mod_lt d (by omega)
  split
  · omega
  · split <;> omega

/-- At the last dyadic boundary, the next strict upward crossing has phase
`d = 4 mod 6`.  The assumptions encode the forced rank-two load and the
additional rank-four load when `d+1` is even. -/
theorem fourNinths_finalBoundary_phase
    {d A : ℕ}
    (hA : 1 ≤ A)
    (hcross : 2 + A ≤ fourNinthsPairPulse (d + 1))
    (heven : Even (d + 1) → 2 ≤ A) :
    d % 6 = 4 := by
  have hpulse : fourNinthsPairPulse (d + 1) = 3 := by
    have hle : fourNinthsPairPulse (d + 1) ≤ 3 := by
      unfold fourNinthsPairPulse
      split
      · omega
      · split <;> omega
    omega
  have hmod3 : (d + 1) % 3 = 2 :=
    (fourNinthsPairPulse_eq_three_iff (d + 1)).mp hpulse
  have hodd : ¬ Even (d + 1) := by
    intro h
    have hA2 := heven h
    omega
  have hmod6 : (d + 1) % 6 < 6 := Nat.mod_lt _ (by omega)
  have hparity : (d + 1) % 2 = 1 := Nat.not_even_iff.mp hodd
  omega

/-- The exact rational contribution of the forced ranks `2`, `4`, and `12`
in phase `d = 4 mod 6`. -/
def fourNinthsForcedAnchorBudget : ℚ :=
  1 / 3 + 1 / 15 + 256 / 4095

theorem fourNinthsForcedAnchorBudget_eq :
    fourNinthsForcedAnchorBudget = 4 / 9 + 74 / 4095 := by
  norm_num [fourNinthsForcedAnchorBudget]

theorem fourNinthsForcedAnchorBudget_gt_four_ninths :
    (4 / 9 : ℚ) < fourNinthsForcedAnchorBudget := by
  rw [fourNinthsForcedAnchorBudget_eq]
  norm_num

/-- The finite arithmetic core of the no-positive-fatal argument.  A final
boundary crossing forces phase `4 mod 6`; its forced anchors put the phase
resolvent strictly above `4/9`, while the positive-tail identity puts it
strictly below `4/9`. -/
theorem fourNinths_no_positive_fatal_anchor_contradiction
    {d A : ℕ} {resolvent : ℚ}
    (hA : 1 ≤ A)
    (hcross : 2 + A ≤ fourNinthsPairPulse (d + 1))
    (heven : Even (d + 1) → 2 ≤ A)
    (hlower : fourNinthsForcedAnchorBudget ≤ resolvent)
    (hupper : resolvent < 4 / 9) :
    False := by
  have _hphase : d % 6 = 4 :=
    fourNinths_finalBoundary_phase hA hcross heven
  have hbudget := fourNinthsForcedAnchorBudget_gt_four_ninths
  linarith

/-- The contribution coefficient of rank `a` to the paired load at diagonal
`d`.  The odd row carries weight two and the even row weight one. -/
def fourNinthsRankLoad (a d : ℕ) : ℕ :=
  (if a ∣ 2 * d - 1 then 2 else 0) + (if a ∣ 2 * d then 1 else 0)

/-- Apart from rank one, a rank cannot hit both members of the consecutive
pair `2d-1, 2d`; hence its total coefficient is at most two. -/
theorem fourNinthsRankLoad_le_two
    {a d : ℕ} (hd : 1 ≤ d) (ha : 2 ≤ a) :
    fourNinthsRankLoad a d ≤ 2 := by
  have hcoprime : Nat.Coprime (2 * d - 1) (2 * d) := by
    rw [Nat.coprime_self_sub_left (by omega : 1 ≤ 2 * d)]
    simp
  by_cases hodd : a ∣ 2 * d - 1
  · have heven : ¬ a ∣ 2 * d := by
      intro h
      have haone := Nat.eq_one_of_dvd_coprimes hcoprime hodd h
      omega
    simp [fourNinthsRankLoad, hodd, heven]
  · by_cases heven : a ∣ 2 * d
    · simp [fourNinthsRankLoad, hodd, heven]
    · simp [fourNinthsRankLoad, hodd, heven]

/-- The exact paired divisor load for an abstract rank-bit function. -/
def fourNinthsAbstractDiagonalLoad (b : ℕ → ℕ) (d : ℕ) : ℕ :=
  ∑ a ∈ Finset.range d, fourNinthsRankLoad a d * b a

/-- The executable paired load is exactly the abstract load of its state-bit
function. -/
theorem fourNinthsDiagonalLoad_eq_abstract
    (s : FourNinthsDiagonalState) (d : ℕ) :
    fourNinthsDiagonalLoad s d =
      fourNinthsAbstractDiagonalLoad (fourNinthsStateBit s) d := by
  unfold fourNinthsDiagonalLoad fourNinthsAbstractDiagonalLoad
  rw [← List.sum_toFinset _ List.nodup_range, List.toFinset_range,
    ← List.sum_toFinset _ List.nodup_range, List.toFinset_range,
    Finset.mul_sum, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro a ha
  unfold fourNinthsRankLoad
  by_cases hodd : a ∣ 2 * d - 1
  · by_cases heven : a ∣ 2 * d
    · simp [hodd, heven]
      omega
    · simp [hodd, heven]
  · by_cases heven : a ∣ 2 * d
    · simp [hodd, heven]
    · simp [hodd, heven]

/-- Once the forced rank-one bit is zero, the whole paired divisor load is
at most twice the number of selected prior ranks. -/
theorem fourNinthsAbstractDiagonalLoad_le_two_selected
    {b : ℕ → ℕ} {d : ℕ}
    (hd : 1 ≤ d) (hb1 : b 1 = 0) :
    fourNinthsAbstractDiagonalLoad b d ≤ 2 * ∑ a ∈ Finset.range d, b a := by
  rw [two_mul, ← Finset.sum_add_distrib]
  unfold fourNinthsAbstractDiagonalLoad
  apply Finset.sum_le_sum
  intro a ha_mem
  by_cases ha0 : a = 0
  · subst a
    have hodd_ne : 2 * d - 1 ≠ 0 := by omega
    have heven_ne : 2 * d ≠ 0 := by omega
    simp [fourNinthsRankLoad, hodd_ne, heven_ne]
  by_cases ha1 : a = 1
  · subst a
    simp [hb1]
  have ha2 : 2 ≤ a := by omega
  simpa [two_mul] using
    Nat.mul_le_mul_right (b a) (fourNinthsRankLoad_le_two hd ha2)

/-- A skipped step preserves (indeed, cannot decrease) the remainder once
the remainder carries two thirds of the selected-count reserve and the exact
divisor load is at most twice that count. -/
theorem fourNinths_skip_preserves_twoThirdsReserve
    {rho selected load pulse next : ℤ}
    (hreserve : 2 * selected ≤ 3 * rho)
    (hload : load ≤ 2 * selected)
    (hpulse : 0 ≤ pulse)
    (hnext : next = 4 * rho + pulse - load) :
    rho ≤ next := by
  omega

/-- A negative skipped successor forces the preceding remainder below half
the selected count.  Thus divisor load by itself is not the open mechanism;
a prior selected small margin is necessary. -/
theorem fourNinths_negative_skip_forces_halfSelectedMargin
    {rho selected load pulse next : ℤ}
    (hload : load ≤ 2 * selected)
    (hpulse : 0 ≤ pulse)
    (hnext : next = 4 * rho + pulse - load)
    (hnegative : next < 0) :
    2 * rho < selected := by
  omega

/-- Fully instantiated load form of the small-margin obstruction: for any
rank-bit function with the forced first bit zero, a negative next remainder
can occur only below two thirds of the selected-count reserve. -/
theorem fourNinths_negative_skip_forces_halfSelectedMargin_of_rankBits
    {b : ℕ → ℕ} {d : ℕ} {rho pulse next : ℤ}
    (hd : 1 ≤ d)
    (hb1 : b 1 = 0)
    (hpulse : 0 ≤ pulse)
    (hnext : next = 4 * rho + pulse - (fourNinthsAbstractDiagonalLoad b d : ℤ))
    (hnegative : next < 0) :
    2 * rho < ((∑ a ∈ Finset.range d, b a : ℕ) : ℤ) := by
  apply fourNinths_negative_skip_forces_halfSelectedMargin
      (selected := ((∑ a ∈ Finset.range d, b a : ℕ) : ℤ))
      (load := (fourNinthsAbstractDiagonalLoad b d : ℤ))
  · exact_mod_cast fourNinthsAbstractDiagonalLoad_le_two_selected hd hb1
  · exact hpulse
  · exact hnext
  · exact hnegative

/-- **Concrete small-margin obstruction.**  If the exact `4/9` diagonal ever
has a negative successor, its preceding state was already below half of the
selected-count reserve.  Thus the abstract obstruction applies directly to
the executable recurrence; it does not by itself rule out that small margin. -/
theorem fourNinthsDiagonalState_negative_successor_forces_halfSelectedMargin
    (d : ℕ) (hnegative : (fourNinthsDiagonalState (d + 1)).rho < 0) :
    2 * (fourNinthsDiagonalState d).rho <
      ((∑ a ∈ Finset.range (d + 1),
        fourNinthsStateBit (fourNinthsDiagonalState d) a : ℕ) : ℤ) := by
  have hstepnegative :
      (fourNinthsDiagonalStep (fourNinthsDiagonalState d)).rho < 0 := by
    simpa [fourNinthsDiagonalState] using hnegative
  have hnotTake : ¬
      ((2 : ℤ) ^ ((fourNinthsDiagonalState d).bits.length + 1) <
        4 * (fourNinthsDiagonalState d).rho +
          (fourNinthsPairPulse ((fourNinthsDiagonalState d).bits.length + 1) : ℤ) -
          (fourNinthsDiagonalLoad (fourNinthsDiagonalState d)
            ((fourNinthsDiagonalState d).bits.length + 1) : ℤ)) := by
    intro htake
    have hnonnegative :
        0 ≤ (fourNinthsDiagonalStep (fourNinthsDiagonalState d)).rho := by
      simp [fourNinthsDiagonalStep, htake]
    omega
  have hnext :
      (fourNinthsDiagonalStep (fourNinthsDiagonalState d)).rho =
        4 * (fourNinthsDiagonalState d).rho +
          (fourNinthsPairPulse ((fourNinthsDiagonalState d).bits.length + 1) : ℤ) -
          (fourNinthsDiagonalLoad (fourNinthsDiagonalState d)
            ((fourNinthsDiagonalState d).bits.length + 1) : ℤ) := by
    simp [fourNinthsDiagonalStep, hnotTake]
  have hlen : (fourNinthsDiagonalState d).bits.length = d :=
    fourNinthsDiagonalState_bits_length d
  rw [hlen] at hnext
  rw [fourNinthsDiagonalLoad_eq_abstract] at hnext
  apply fourNinths_negative_skip_forces_halfSelectedMargin_of_rankBits
      (b := fourNinthsStateBit (fourNinthsDiagonalState d))
      (d := d + 1)
      (pulse := (fourNinthsPairPulse (d + 1) : ℤ))
      (next := (fourNinthsDiagonalStep (fourNinthsDiagonalState d)).rho)
  · omega
  · exact fourNinthsDiagonalState_bit_one d
  · exact_mod_cast Nat.zero_le (fourNinthsPairPulse (d + 1))
  · exact hnext
  · exact hstepnegative

/-- Block form of the same obstruction.  Here `scale` is the accumulated
factor (in the intended application, `4 ^ L`) and `debt` is the weighted
divisor load across the skipped block.  The geometric load ceiling alone
forces the remainder at the last selected rank below two thirds of its
selected-count reserve before a negative block endpoint is possible. -/
theorem fourNinths_negative_skipBlock_forces_twoThirdsSelectedMargin
    {rho selected debt pulse next scale : ℤ}
    (hscale : 1 ≤ scale)
    (hselected : 0 ≤ selected)
    (hdebt : 3 * debt ≤ 2 * selected * (scale - 1))
    (hpulse : 0 ≤ pulse)
    (hnext : next = scale * rho + pulse - debt)
    (hnegative : next < 0) :
    3 * rho < 2 * selected := by
  by_contra hmargin
  have hmargin' : 2 * selected ≤ 3 * rho := le_of_not_gt hmargin
  have hscale0 : 0 ≤ scale := by omega
  have hscaled := mul_le_mul_of_nonneg_right hmargin' hscale0
  nlinarith

#print axioms fourNinthsDiagonalState_twelve
#print axioms fourNinths_finalBoundary_phase
#print axioms fourNinths_no_positive_fatal_anchor_contradiction
#print axioms fourNinths_skip_preserves_twoThirdsReserve
#print axioms fourNinths_negative_skip_forces_halfSelectedMargin
#print axioms fourNinthsAbstractDiagonalLoad_le_two_selected
#print axioms fourNinths_negative_skip_forces_halfSelectedMargin_of_rankBits
#print axioms fourNinths_negative_skipBlock_forces_twoThirdsSelectedMargin
#print axioms fourNinthsDiagonalState_negative_successor_forces_halfSelectedMargin

end Erdos257PeriodNoncollapse
