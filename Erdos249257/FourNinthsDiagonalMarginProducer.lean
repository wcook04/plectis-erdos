import Erdos249257.FourNinthsDiagonalNoPositiveFatal

/-!
# A selected-landing producer for the four-ninths diagonal

The paired-load theorem already controls every skipped row once the current
state has the reserve

`2 * selectedCount ≤ 3 * rho`.

This module makes the resulting induction explicit.  Global nonnegativity of
the executable `4 / 9` diagonal is reduced to one branch-local statement:
every selected landing recreates that reserve.  Thus skipped rows are no
longer part of the open producer.
-/

namespace Erdos249257

open Finset

/-- The number of selected ranks in the executable diagonal state after `d`
decisions.  The range deliberately matches the sum occurring in the existing
paired-load bound; rank zero aliases rank one, whose actual bit is proved zero. -/
def fourNinthsDiagonalSelectedCount (d : ℕ) : ℕ :=
  ∑ a ∈ Finset.range (d + 1),
    fourNinthsStateBit (fourNinthsDiagonalState d) a

/-- The exact predicate that the transition from depth `d` selects rank
`d+1`. -/
def FourNinthsDiagonalTakesAt (d : ℕ) : Prop :=
  (((2 ^ (d + 1) + 1 : ℕ) : ℤ) ≤
    4 * (fourNinthsDiagonalState d).rho +
      (fourNinthsPairPulse (d + 1) : ℤ) -
      (fourNinthsDiagonalLoad (fourNinthsDiagonalState d) (d + 1) : ℤ))

/-- The sole branch-local producer left by the reserve induction: every
selected landing restores the two-thirds selected-count margin. -/
def FourNinthsSelectedLandingMarginProducer : Prop :=
  ∀ d : ℕ, FourNinthsDiagonalTakesAt d →
    ((2 * fourNinthsDiagonalSelectedCount (d + 1) : ℕ) : ℤ) ≤
      3 * (fourNinthsDiagonalState (d + 1)).rho

/-- A sharper sufficient producer suggested by the exact trajectory: every
selected landing retains at least its rank in remainder.  Unlike the finite
audit, this definition has an all-depth quantifier and is not asserted here. -/
def FourNinthsSelectedLandingRankProducer : Prop :=
  ∀ d : ℕ, FourNinthsDiagonalTakesAt d →
    (((d + 1 : ℕ) : ℤ) ≤ (fourNinthsDiagonalState (d + 1)).rho)

/-! ## Why the remaining producer must use actual reachability -/

/-- An abstract depth-twelve state with the complete certified diagonal bit
word, but with a deliberately altered remainder.  It is not claimed to occur
on the executable diagonal orbit. -/
def fourNinthsLocalMarginCountermodel : FourNinthsDiagonalState :=
  ⟨[false, true, false, true, true, false,
    true, true, false, false, false, true], 2049⟩

/-- **Exact local countermodel.**  The state has the certified bit word, six
selected ranks, a huge incoming two-thirds reserve, exact rank-thirteen load
three, and the correct phase pulse one.  Nevertheless its next step takes
rank thirteen and lands at remainder one, with seven selected ranks, so the
two-thirds landing margin fails.

Consequently pulse phase, forced anchors, the paired-load ceiling, and the
incoming reserve cannot by themselves prove the actual selected-landing
producer.  Any successful proof must use a property distinguishing the real
predecessor state from this locally admissible one. -/
theorem fourNinths_localMarginCountermodel_certificate :
    fourNinthsLocalMarginCountermodel.bits.length = 12 ∧
    fourNinthsStateBit fourNinthsLocalMarginCountermodel 2 = 1 ∧
    fourNinthsStateBit fourNinthsLocalMarginCountermodel 4 = 1 ∧
    fourNinthsStateBit fourNinthsLocalMarginCountermodel 5 = 1 ∧
    fourNinthsStateBit fourNinthsLocalMarginCountermodel 12 = 1 ∧
    (∑ a ∈ Finset.range 13,
      fourNinthsStateBit fourNinthsLocalMarginCountermodel a) = 6 ∧
    fourNinthsDiagonalLoad fourNinthsLocalMarginCountermodel 13 = 3 ∧
    fourNinthsPairPulse 13 = 1 ∧
    ((2 * (∑ a ∈ Finset.range 13,
      fourNinthsStateBit fourNinthsLocalMarginCountermodel a) : ℕ) : ℤ) ≤
        3 * fourNinthsLocalMarginCountermodel.rho ∧
    (((2 ^ 13 + 1 : ℕ) : ℤ) ≤
      4 * fourNinthsLocalMarginCountermodel.rho +
        (fourNinthsPairPulse 13 : ℤ) -
        (fourNinthsDiagonalLoad fourNinthsLocalMarginCountermodel 13 : ℤ)) ∧
    (fourNinthsDiagonalStep fourNinthsLocalMarginCountermodel).rho = 1 ∧
    3 * (fourNinthsDiagonalStep fourNinthsLocalMarginCountermodel).rho <
      ((2 * (∑ a ∈ Finset.range 14,
        fourNinthsStateBit
          (fourNinthsDiagonalStep fourNinthsLocalMarginCountermodel) a) : ℕ) : ℤ) := by
  decide

/-- Rank zero has the same aliased bit as rank one, hence is zero on every
actual diagonal state. -/
theorem fourNinthsDiagonalState_bit_zero (d : ℕ) :
    fourNinthsStateBit (fourNinthsDiagonalState d) 0 = 0 := by
  simpa [fourNinthsStateBit] using fourNinthsDiagonalState_bit_one d

/-- After `d` decisions there are at most `d` selected ranks.  The aliased
rank-zero term vanishes, and each of the remaining `d` Boolean terms is at
most one. -/
theorem fourNinthsDiagonalSelectedCount_le_depth (d : ℕ) :
    fourNinthsDiagonalSelectedCount d ≤ d := by
  induction d with
  | zero => decide
  | succ d ih =>
      unfold fourNinthsDiagonalSelectedCount
      rw [show d + 1 + 1 = (d + 1) + 1 by omega,
        Finset.sum_range_succ]
      have hprior :
          (∑ a ∈ Finset.range (d + 1),
              fourNinthsStateBit (fourNinthsDiagonalState (d + 1)) a) =
            ∑ a ∈ Finset.range (d + 1),
              fourNinthsStateBit (fourNinthsDiagonalState d) a := by
        apply Finset.sum_congr rfl
        intro a ha
        have had : a ≤ d := by
          simpa [Finset.mem_range] using ha
        by_cases ha0 : a = 0
        · subst a
          rw [fourNinthsDiagonalState_bit_zero,
            fourNinthsDiagonalState_bit_zero]
        · have ha1 : 1 ≤ a := Nat.one_le_iff_ne_zero.mpr ha0
          rw [fourNinthsDiagonalState]
          exact fourNinthsDiagonalStep_preserves_existing_bit
            (fourNinthsDiagonalState d) ha1 (by
              rw [fourNinthsDiagonalState_bits_length]
              exact had)
      rw [hprior]
      have hlast :
          fourNinthsStateBit (fourNinthsDiagonalState (d + 1)) (d + 1) ≤ 1 := by
        unfold fourNinthsStateBit
        split <;> omega
      change fourNinthsDiagonalSelectedCount d +
          fourNinthsStateBit (fourNinthsDiagonalState (d + 1)) (d + 1) ≤ d + 1
      omega

/-- On a selected transition, expose the post-step remainder as the literal
overshoot above the rank-`d+1` dyadic coin. -/
theorem fourNinthsDiagonalState_rho_succ_of_takes
    (d : ℕ) (htake : FourNinthsDiagonalTakesAt d) :
    (fourNinthsDiagonalState (d + 1)).rho =
      4 * (fourNinthsDiagonalState d).rho +
        (fourNinthsPairPulse (d + 1) : ℤ) -
        (fourNinthsDiagonalLoad
          (fourNinthsDiagonalState d) (d + 1) : ℤ) -
        ((2 ^ (d + 1) + 1 : ℕ) : ℤ) := by
  have htake' :
      ((2 : ℤ) ^ (d + 1) <
        4 * (fourNinthsDiagonalState d).rho +
          (fourNinthsPairPulse (d + 1) : ℤ) -
          (fourNinthsDiagonalLoad
            (fourNinthsDiagonalState d) (d + 1) : ℤ)) := by
    unfold FourNinthsDiagonalTakesAt at htake
    push_cast at htake
    omega
  rw [fourNinthsDiagonalState]
  simp [fourNinthsDiagonalStep, fourNinthsDiagonalState_bits_length, htake']

/-- **Endpoint equivalence.**  The selected-rank producer is exactly the
claim that every selected predecessor value clears the dyadic coin by at
least the landing rank.  Equivalently, the actual orbit never selects inside
the explicit `d+1`-wide half-open bad window above the coin. -/
theorem fourNinthsSelectedLandingRankProducer_iff_endpointInequality :
    FourNinthsSelectedLandingRankProducer ↔
      ∀ d : ℕ, FourNinthsDiagonalTakesAt d →
        (((2 ^ (d + 1) + 1 : ℕ) : ℤ) + ((d + 1 : ℕ) : ℤ) ≤
          4 * (fourNinthsDiagonalState d).rho +
            (fourNinthsPairPulse (d + 1) : ℤ) -
            (fourNinthsDiagonalLoad
              (fourNinthsDiagonalState d) (d + 1) : ℤ)) := by
  constructor
  · intro hrank d htake
    have hrank' := hrank d htake
    rw [fourNinthsDiagonalState_rho_succ_of_takes d htake] at hrank'
    omega
  · intro hendpoint d htake
    have h := hendpoint d htake
    rw [fourNinthsDiagonalState_rho_succ_of_takes d htake]
    omega

/-- The selected-rank producer is sufficient for the selected-count margin:
the selected count is at most the landing rank, while the landing remainder
is at least that rank. -/
theorem fourNinthsSelectedLandingMarginProducer_of_rankProducer
    (hrank : FourNinthsSelectedLandingRankProducer) :
    FourNinthsSelectedLandingMarginProducer := by
  intro d htake
  have hcount := fourNinthsDiagonalSelectedCount_le_depth (d + 1)
  have hcountZ :
      ((fourNinthsDiagonalSelectedCount (d + 1) : ℕ) : ℤ) ≤
        ((d + 1 : ℕ) : ℤ) := by
    exact_mod_cast hcount
  have hrankZ := hrank d htake
  have hrho : 0 ≤ (fourNinthsDiagonalState (d + 1)).rho := by
    have hd : (0 : ℤ) ≤ ((d + 1 : ℕ) : ℤ) := by positivity
    exact hd.trans hrankZ
  push_cast
  linarith

/-- On a skipped transition the selected-count statistic is unchanged. -/
theorem fourNinthsDiagonalSelectedCount_succ_of_not_takes
    (d : ℕ) (hskip : ¬ FourNinthsDiagonalTakesAt d) :
    fourNinthsDiagonalSelectedCount (d + 1) =
      fourNinthsDiagonalSelectedCount d := by
  unfold fourNinthsDiagonalSelectedCount
  rw [show d + 1 + 1 = (d + 1) + 1 by omega, Finset.sum_range_succ]
  have hprior :
      (∑ a ∈ Finset.range (d + 1),
          fourNinthsStateBit (fourNinthsDiagonalState (d + 1)) a) =
        ∑ a ∈ Finset.range (d + 1),
          fourNinthsStateBit (fourNinthsDiagonalState d) a := by
    apply Finset.sum_congr rfl
    intro a ha
    have had : a ≤ d := by
      simpa [Finset.mem_range] using ha
    by_cases ha0 : a = 0
    · subst a
      rw [fourNinthsDiagonalState_bit_zero,
        fourNinthsDiagonalState_bit_zero]
    · have ha1 : 1 ≤ a := Nat.one_le_iff_ne_zero.mpr ha0
      rw [fourNinthsDiagonalState]
      exact fourNinthsDiagonalStep_preserves_existing_bit
        (fourNinthsDiagonalState d) ha1 (by
          rw [fourNinthsDiagonalState_bits_length]
          exact had)
  rw [hprior]
  have hnotTake : ¬
      ((2 : ℤ) ^ (d + 1) <
        4 * (fourNinthsDiagonalState d).rho +
          (fourNinthsPairPulse (d + 1) : ℤ) -
          (fourNinthsDiagonalLoad
            (fourNinthsDiagonalState d) (d + 1) : ℤ)) := by
    intro htake
    apply hskip
    unfold FourNinthsDiagonalTakesAt
    push_cast
    omega
  have hlast :
      fourNinthsStateBit (fourNinthsDiagonalState (d + 1)) (d + 1) = 0 := by
    rw [fourNinthsDiagonalState]
    simp [fourNinthsDiagonalStep, fourNinthsStateBit,
      fourNinthsDiagonalState_bits_length, hnotTake]
  simp [hlast]

/-- The paired divisor load at the next rank is at most twice the executable
selected count. -/
theorem fourNinthsDiagonalLoad_le_two_selectedCount (d : ℕ) :
    fourNinthsDiagonalLoad (fourNinthsDiagonalState d) (d + 1) ≤
      2 * fourNinthsDiagonalSelectedCount d := by
  rw [fourNinthsDiagonalLoad_eq_abstract]
  exact fourNinthsAbstractDiagonalLoad_le_two_selected
    (d := d + 1) (by omega) (fourNinthsDiagonalState_bit_one d)

/-- The selected-landing producer propagates the two-thirds reserve through
every executable state.  The skip case is unconditional: the existing
paired-load bound makes a skipped transition nondecreasing in `rho`. -/
theorem fourNinthsDiagonal_twoThirdsReserve_of_selectedLandingProducer
    (hproducer : FourNinthsSelectedLandingMarginProducer) :
    ∀ d : ℕ,
      ((2 * fourNinthsDiagonalSelectedCount d : ℕ) : ℤ) ≤
        3 * (fourNinthsDiagonalState d).rho := by
  intro d
  induction d with
  | zero => norm_num [fourNinthsDiagonalSelectedCount,
      fourNinthsDiagonalState, fourNinthsStateBit]
  | succ d ih =>
      by_cases htake : FourNinthsDiagonalTakesAt d
      · exact hproducer d htake
      · have hcount :=
          fourNinthsDiagonalSelectedCount_succ_of_not_takes d htake
        have hload := fourNinthsDiagonalLoad_le_two_selectedCount d
        have hnotTake : ¬
            ((2 : ℤ) ^ (d + 1) <
              4 * (fourNinthsDiagonalState d).rho +
                (fourNinthsPairPulse (d + 1) : ℤ) -
                (fourNinthsDiagonalLoad
                  (fourNinthsDiagonalState d) (d + 1) : ℤ)) := by
          intro htake'
          apply htake
          unfold FourNinthsDiagonalTakesAt
          push_cast
          omega
        have hrho :
            (fourNinthsDiagonalState d).rho ≤
              (fourNinthsDiagonalState (d + 1)).rho := by
          apply fourNinths_skip_preserves_twoThirdsReserve
              (selected := (fourNinthsDiagonalSelectedCount d : ℤ))
              (load :=
                (fourNinthsDiagonalLoad
                  (fourNinthsDiagonalState d) (d + 1) : ℤ))
              (pulse := (fourNinthsPairPulse (d + 1) : ℤ))
          · exact ih
          · exact_mod_cast hload
          · positivity
          · rw [fourNinthsDiagonalState]
            simp [fourNinthsDiagonalStep,
              fourNinthsDiagonalState_bits_length,
              hnotTake]
        rw [hcount]
        linarith

/-- Consequently the selected-landing producer proves global nonnegativity of
the exact `4 / 9` diagonal, the open arithmetic input of the counterexample
route. -/
theorem fourNinthsDiagonal_nonnegative_of_selectedLandingProducer
    (hproducer : FourNinthsSelectedLandingMarginProducer) (d : ℕ) :
    0 ≤ (fourNinthsDiagonalState d).rho := by
  have hreserve :=
    fourNinthsDiagonal_twoThirdsReserve_of_selectedLandingProducer hproducer d
  have hcount :
      0 ≤ ((fourNinthsDiagonalSelectedCount d : ℕ) : ℤ) := by positivity
  omega

/-- The sharper selected-rank producer therefore also proves global
nonnegativity of the executable diagonal. -/
theorem fourNinthsDiagonal_nonnegative_of_selectedLandingRankProducer
    (hrank : FourNinthsSelectedLandingRankProducer) (d : ℕ) :
    0 ≤ (fourNinthsDiagonalState d).rho :=
  fourNinthsDiagonal_nonnegative_of_selectedLandingProducer
    (fourNinthsSelectedLandingMarginProducer_of_rankProducer hrank) d

#print axioms fourNinthsDiagonalSelectedCount_le_depth
#print axioms fourNinths_localMarginCountermodel_certificate
#print axioms fourNinthsDiagonalState_rho_succ_of_takes
#print axioms fourNinthsSelectedLandingRankProducer_iff_endpointInequality
#print axioms fourNinthsSelectedLandingMarginProducer_of_rankProducer
#print axioms fourNinthsDiagonalSelectedCount_succ_of_not_takes
#print axioms fourNinthsDiagonalLoad_le_two_selectedCount
#print axioms fourNinthsDiagonal_twoThirdsReserve_of_selectedLandingProducer
#print axioms fourNinthsDiagonal_nonnegative_of_selectedLandingProducer
#print axioms fourNinthsDiagonal_nonnegative_of_selectedLandingRankProducer

end Erdos249257
