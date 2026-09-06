import Erdos249257.BooleanMobiusGreedyReduction

/-!
# Even-core modular nonvanishing is not a weaker escape

The half-row probe suggests testing whether the strict lower-core remainder
is nonzero modulo `2^R`.  Under the positive strict two-bank bound, that
modular condition is not a weaker invariant: divisibility by `2^R` forces the
remainder to be exactly the already-known forbidden midpoint state `2^R`.
Under the canonical coarse bound `A < 2 * 2^R + 1`, the only additional
divisible state is the top edge `2 * 2^R`.  Thus modular nonvanishing is
either exactly midpoint-hole exclusion or a strictly stronger demand.

The results below are route retirements.  They do not prove positivity, the
strict bank bound, or exclusion of the midpoint state, and hence do not
produce cofinal exact rows or settle Erdős #257.
-/

namespace Erdos249257

open BooleanMobiusGreedyReduction
open HalfCylinderIntegerGreedy

/-- A positive natural strictly below two consecutive multiples of `2^R`
is divisible by `2^R` exactly when it is the first positive multiple.

This elementary interval lemma is the exact arithmetic obstruction behind
the proposed pure modulo-`2^R` half-row invariant. -/
theorem mod_twoPow_eq_zero_iff_eq_twoPow_of_pos_of_lt_two_mul
    {A R : ℕ} (hpos : 0 < A) (hbound : A < 2 * 2 ^ R) :
    A % 2 ^ R = 0 ↔ A = 2 ^ R := by
  constructor
  · intro hmod
    have hpow : 0 < 2 ^ R := pow_pos (by norm_num) R
    have hdvd : 2 ^ R ∣ A := Nat.dvd_of_mod_eq_zero hmod
    obtain ⟨a, ha⟩ := hdvd
    have haPos : 0 < a := by
      by_contra ha0
      have haZero : a = 0 := Nat.eq_zero_of_not_pos ha0
      subst a
      simp at ha
      omega
    have haLt : a < 2 := by
      apply (Nat.mul_lt_mul_left hpow).mp
      rw [← ha]
      simpa [Nat.mul_comm] using hbound
    have haOne : a = 1 := by omega
    rw [haOne, mul_one] at ha
    exact ha
  · rintro rfl
    simp

/-- On the canonical coarse safety interval, a positive multiple of `2^R`
is either the midpoint or the single top-edge state.  This is the exact
version needed for `CofinalEvenHalfCutoffCoreSafety`, whose upper bound is
`A < 2 * 2^R + 1`. -/
theorem mod_twoPow_eq_zero_iff_eq_twoPow_or_eq_two_mul_twoPow
    {A R : ℕ} (hpos : 0 < A) (hbound : A < 2 * 2 ^ R + 1) :
    A % 2 ^ R = 0 ↔ A = 2 ^ R ∨ A = 2 * 2 ^ R := by
  constructor
  · intro hmod
    have hpow : 0 < 2 ^ R := pow_pos (by norm_num) R
    have hdvd : 2 ^ R ∣ A := Nat.dvd_of_mod_eq_zero hmod
    obtain ⟨a, ha⟩ := hdvd
    have haPos : 0 < a := by
      by_contra ha0
      have haZero : a = 0 := Nat.eq_zero_of_not_pos ha0
      subst a
      simp at ha
      omega
    have hthree : 2 * 2 ^ R + 1 ≤ 2 ^ R * 3 := by omega
    have haLt : a < 3 := by
      apply (Nat.mul_lt_mul_left hpow).mp
      rw [← ha]
      exact hbound.trans_le hthree
    rcases (show a = 1 ∨ a = 2 by omega) with haOne | haTwo
    · left
      simpa [haOne] using ha
    · right
      simpa [haTwo, Nat.mul_comm] using ha
  · rintro (rfl | rfl)
    · simp
    · simp [Nat.mul_comm]

/-- **Exact modular-route retirement for the deterministic even core.**
Subject to positivity and the strict two-bank bound, modular silence of the
actual strict-core remainder is equivalent to the forbidden midpoint hole.
Thus proving the left side false supplies no weaker route than proving the
right side false. -/
theorem evenHalfCutoffCoreRemainder_mod_twoPow_eq_zero_iff_midpointHole
    {R : ℕ}
    (hpos : 0 < evenHalfCutoffCoreRemainder R)
    (hbound : evenHalfCutoffCoreRemainder R < 2 * 2 ^ R) :
    evenHalfCutoffCoreRemainder R % 2 ^ R = 0 ↔
      evenHalfCutoffCoreRemainder R = 2 ^ R :=
  mod_twoPow_eq_zero_iff_eq_twoPow_of_pos_of_lt_two_mul hpos hbound

/-- Nonvanishing of the even-core residue is therefore exactly midpoint-hole
exclusion on the same positive strict-bank interval. -/
theorem evenHalfCutoffCoreRemainder_mod_twoPow_ne_zero_iff_ne_midpointHole
    {R : ℕ}
    (hpos : 0 < evenHalfCutoffCoreRemainder R)
    (hbound : evenHalfCutoffCoreRemainder R < 2 * 2 ^ R) :
    evenHalfCutoffCoreRemainder R % 2 ^ R ≠ 0 ↔
      evenHalfCutoffCoreRemainder R ≠ 2 ^ R := by
  exact not_congr
    (evenHalfCutoffCoreRemainder_mod_twoPow_eq_zero_iff_midpointHole
      hpos hbound)

/-- Under the exact coarse core-safety bound, modular silence is the union of
the forbidden midpoint and the top edge.  Consequently modular
nonvanishing is stronger than the existing single-hole socket unless the
strict two-bank bound is separately known. -/
theorem evenHalfCutoffCoreRemainder_mod_twoPow_eq_zero_iff_midpoint_or_top
    {R : ℕ}
    (hpos : 0 < evenHalfCutoffCoreRemainder R)
    (hbound : evenHalfCutoffCoreRemainder R < 2 * 2 ^ R + 1) :
    evenHalfCutoffCoreRemainder R % 2 ^ R = 0 ↔
      evenHalfCutoffCoreRemainder R = 2 ^ R ∨
        evenHalfCutoffCoreRemainder R = 2 * 2 ^ R :=
  mod_twoPow_eq_zero_iff_eq_twoPow_or_eq_two_mul_twoPow hpos hbound

/-- Coarse-interval residue nonvanishing excludes both distinguished
divisible states, not only the midpoint hole. -/
theorem evenHalfCutoffCoreRemainder_mod_twoPow_ne_zero_iff_ne_midpoint_and_ne_top
    {R : ℕ}
    (hpos : 0 < evenHalfCutoffCoreRemainder R)
    (hbound : evenHalfCutoffCoreRemainder R < 2 * 2 ^ R + 1) :
    evenHalfCutoffCoreRemainder R % 2 ^ R ≠ 0 ↔
      evenHalfCutoffCoreRemainder R ≠ 2 ^ R ∧
        evenHalfCutoffCoreRemainder R ≠ 2 * 2 ^ R := by
  simpa only [not_or] using
    not_congr
      (evenHalfCutoffCoreRemainder_mod_twoPow_eq_zero_iff_midpoint_or_top
        hpos hbound)

/-- The terminal midpoint coin sends the coarse top edge `2 * 2^R` to the
largest successful bank remainder `2^R - 1`.  This is an exact local-row
countermodel to treating incoming modular nonvanishing as necessary for
completion. -/
theorem integerGreedyRemainder_midpointCoin_at_topEdge
    (R : ℕ) :
    integerGreedyRemainder [2 ^ R + 1] (2 * 2 ^ R) = 2 ^ R - 1 := by
  rw [integerGreedyRemainder_cons]
  have hpow : 1 ≤ 2 ^ R := Nat.one_le_two_pow
  have htake : 2 ^ R + 1 ≤ 2 * 2 ^ R := by omega
  rw [if_pos htake, integerGreedyRemainder_nil]
  omega

/-- The same top-edge state both completes the terminal local row and is
zero modulo `2^R`.  No claim is made that the deterministic lower-core orbit
ever reaches this state; the theorem falsifies only a source-independent
local necessity claim. -/
theorem topEdge_completes_midpointCoin_and_is_modularly_silent
    (R : ℕ) :
    integerGreedyRemainder [2 ^ R + 1] (2 * 2 ^ R) < 2 ^ R ∧
      (2 * 2 ^ R) % 2 ^ R = 0 := by
  constructor
  · rw [integerGreedyRemainder_midpointCoin_at_topEdge R]
    have hpow : 0 < 2 ^ R := by positivity
    omega
  · simp [Nat.mul_comm]

/-- The midpoint and top edge have the same residue modulo `2^R`, but the
terminal midpoint coin has opposite completion outcomes on them.  Hence no
predicate of that residue class alone can characterize local completion on
the coarse two-bank interval. -/
theorem equal_mod_twoPow_but_opposite_midpointCoin_completion
    (R : ℕ) :
    (2 ^ R) % 2 ^ R = (2 * 2 ^ R) % 2 ^ R ∧
      ¬ (integerGreedyRemainder [2 ^ R + 1] (2 ^ R) < 2 ^ R) ∧
      integerGreedyRemainder [2 ^ R + 1] (2 * 2 ^ R) < 2 ^ R := by
  constructor
  · simp [Nat.mul_comm]
  constructor
  · rw [integerGreedyRemainder_cons]
    have hskip : ¬ 2 ^ R + 1 ≤ 2 ^ R := by omega
    rw [if_neg hskip, integerGreedyRemainder_nil]
    omega
  · exact (topEdge_completes_midpointCoin_and_is_modularly_silent R).1

/-- Once the coarse top edge is separately excluded, the modular condition
does become an exact completion test.  The theorem makes the extra input
explicit: without `A ≠ 2 * 2^R`, residue nonvanishing is stronger than the
canonical single-midpoint completion criterion. -/
theorem integerGreedyRemainder_even_halfCutoff_lt_iff_core_mod_twoPow_ne_zero
    {R : ℕ} (hR : 2 ≤ R)
    (hpos : 0 < evenHalfCutoffCoreRemainder R)
    (hbound : evenHalfCutoffCoreRemainder R < 2 * 2 ^ R + 1)
    (hneTop : evenHalfCutoffCoreRemainder R ≠ 2 * 2 ^ R) :
    integerGreedyRemainder
        (localMersenneWeights (2 * R) R)
        (2 ^ (2 * R - 1) - 1) < 2 ^ R ↔
      evenHalfCutoffCoreRemainder R % 2 ^ R ≠ 0 := by
  constructor
  · intro hcomplete
    have hneMidpoint :=
      ((integerGreedyRemainder_even_halfCutoff_lt_iff_core_ne hR).mp
        hcomplete).2
    exact
      (evenHalfCutoffCoreRemainder_mod_twoPow_ne_zero_iff_ne_midpoint_and_ne_top
        hpos hbound).2 ⟨hneMidpoint, hneTop⟩
  · intro hmod
    have hneMidpoint :=
      ((evenHalfCutoffCoreRemainder_mod_twoPow_ne_zero_iff_ne_midpoint_and_ne_top
        hpos hbound).1 hmod).1
    exact
      (integerGreedyRemainder_even_halfCutoff_lt_iff_core_ne hR).2
        ⟨hbound, hneMidpoint⟩

#print axioms mod_twoPow_eq_zero_iff_eq_twoPow_of_pos_of_lt_two_mul
#print axioms mod_twoPow_eq_zero_iff_eq_twoPow_or_eq_two_mul_twoPow
#print axioms evenHalfCutoffCoreRemainder_mod_twoPow_eq_zero_iff_midpointHole
#print axioms evenHalfCutoffCoreRemainder_mod_twoPow_ne_zero_iff_ne_midpointHole
#print axioms evenHalfCutoffCoreRemainder_mod_twoPow_eq_zero_iff_midpoint_or_top
#print axioms evenHalfCutoffCoreRemainder_mod_twoPow_ne_zero_iff_ne_midpoint_and_ne_top
#print axioms integerGreedyRemainder_midpointCoin_at_topEdge
#print axioms topEdge_completes_midpointCoin_and_is_modularly_silent
#print axioms equal_mod_twoPow_but_opposite_midpointCoin_completion
#print axioms integerGreedyRemainder_even_halfCutoff_lt_iff_core_mod_twoPow_ne_zero

end Erdos249257
