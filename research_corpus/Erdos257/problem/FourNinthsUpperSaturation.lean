import ErdosProblems.Erdos257.FourNinthsQuotientCompactness

/-!
# Saturated upper-boundary states of the executable 4/9 diagonal

The quotient compactness consumer needs the dyadic upper window `rho_d ≤ 2^d`.  A first
failure cannot occur from a strict predecessor: the cancellation module already proves
that a take stays strict and a skip stays closed.  The only remaining gateway is therefore
an exactly saturated state.

This module classifies that gateway.  From `rho_d = 2^d`, strict escape at the next row is
equivalent to the unique large source pulse together with paired divisor load at most one.
That sparse load forces a concrete missing ancestor near rank `2d/3`.  Conversely, ruling
out that single saturated sparse-load event proves the entire dyadic upper window.
-/

namespace ErdosProblems.Erdos257

namespace FourNinthsUpperSaturation

open Erdos257PeriodNoncollapse
open FourNinthsCoinCancellation
open FourNinthsQuotientDefect
open FourNinthsQuotientCompactness

noncomputable section

local instance (d : ℕ) : Decidable (FourNinthsDiagonalTakesAt d) :=
  Classical.propDecidable _

/-- Rank two is a permanent selected anchor after its exact base decision. -/
theorem fourNinthsDiagonalState_bit_two_of_ge
    {d : ℕ} (hd : 2 ≤ d) :
    fourNinthsStateBit (fourNinthsDiagonalState d) 2 = 1 := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hd
  induction k with
  | zero => decide
  | succ k ih =>
      rw [show 2 + (k + 1) = (2 + k) + 1 by omega]
      calc
        fourNinthsStateBit (fourNinthsDiagonalState ((2 + k) + 1)) 2 =
            fourNinthsStateBit (fourNinthsDiagonalState (2 + k)) 2 :=
          fourNinthsDiagonalState_bit_succ_eq_of_le (by omega)
        _ = 1 := ih (by omega)

theorem fourNinthsPairPulse_cases (r : ℕ) :
    fourNinthsPairPulse r = 0 ∨
      fourNinthsPairPulse r = 1 ∨ fourNinthsPairPulse r = 3 := by
  unfold fourNinthsPairPulse
  split
  · exact Or.inl rfl
  · split
    · exact Or.inr (Or.inl rfl)
    · exact Or.inr (Or.inr rfl)

/-- **Exact saturated escape classifier.**  At the dyadic boundary, the next row crosses
strictly above its new boundary exactly when the pulse is three and the paired load is at
most one. -/
theorem fourNinthsDiagonalState_saturated_crosses_iff_sparseLoad
    {d : ℕ}
    (hsaturated : (fourNinthsDiagonalState d).rho = (2 : ℤ) ^ d) :
    (2 : ℤ) ^ (d + 1) < (fourNinthsDiagonalState (d + 1)).rho ↔
      fourNinthsPairPulse (d + 1) = 3 ∧
        fourNinthsDiagonalLoad (fourNinthsDiagonalState d) (d + 1) ≤ 1 := by
  constructor
  · intro hcross
    have htake : FourNinthsDiagonalTakesAt d := by
      by_contra hskip
      have hle := fourNinthsDiagonalState_rho_succ_le_twoPow_of_not_takes d hskip
      omega
    have hformula := fourNinthsDiagonalState_rho_succ_of_takes d htake
    rw [hformula, hsaturated, pow_succ] at hcross
    push_cast at hcross
    have hpulseLe : fourNinthsPairPulse (d + 1) ≤ 3 := by
      unfold fourNinthsPairPulse
      split
      · omega
      · split <;> omega
    have hpulseNeTwo : fourNinthsPairPulse (d + 1) ≠ 2 := by
      unfold fourNinthsPairPulse
      split
      · omega
      · split <;> omega
    constructor <;> omega
  · rintro ⟨hthree, hload⟩
    have htake : FourNinthsDiagonalTakesAt d := by
      unfold FourNinthsDiagonalTakesAt
      rw [hsaturated, hthree, pow_succ]
      push_cast
      have hpow : 0 ≤ (2 : ℤ) ^ d := by positivity
      omega
    rw [fourNinthsDiagonalState_rho_succ_of_takes d htake,
      hsaturated, hthree, pow_succ]
    push_cast
    omega

/-- Excluding the unique saturated sparse-load event propagates the dyadic upper window
through every executable state. -/
theorem fourNinthsDiagonalState_upperWindow_of_saturatedLoad
    (hsaturatedLoad : ∀ d : ℕ,
      (fourNinthsDiagonalState d).rho = (2 : ℤ) ^ d →
      fourNinthsPairPulse (d + 1) = 3 →
      2 ≤ fourNinthsDiagonalLoad (fourNinthsDiagonalState d) (d + 1)) :
    ∀ d : ℕ, (fourNinthsDiagonalState d).rho ≤ (2 : ℤ) ^ d := by
  intro d
  induction d with
  | zero => decide
  | succ d ih =>
      by_cases hstrict : (fourNinthsDiagonalState d).rho < (2 : ℤ) ^ d
      · by_cases htake : FourNinthsDiagonalTakesAt d
        · exact (fourNinthsDiagonalState_rho_succ_lt_twoPow_of_takes_of_prev_lt
            d htake hstrict).le
        · exact fourNinthsDiagonalState_rho_succ_le_twoPow_of_not_takes d htake
      · have hsaturated :
          (fourNinthsDiagonalState d).rho = (2 : ℤ) ^ d := by omega
        by_contra hcross
        have hcross' :
            (2 : ℤ) ^ (d + 1) <
              (fourNinthsDiagonalState (d + 1)).rho := by omega
        have hsparse :=
          (fourNinthsDiagonalState_saturated_crosses_iff_sparseLoad
            hsaturated).mp hcross'
        have hdense := hsaturatedLoad d hsaturated hsparse.1
        omega

/-- A first saturated state has an exact predecessor coordinate: the prior remainder lies
on the dyadic midline, shifted only by one quarter of the paired load minus the periodic
pulse.  This is the anti-concentration target for ruling out saturation itself. -/
theorem fourNinthsDiagonalState_first_saturation_midline
    {d : ℕ}
    (hprev : (fourNinthsDiagonalState d).rho < (2 : ℤ) ^ d)
    (hsaturatedNext : (fourNinthsDiagonalState (d + 1)).rho =
      (2 : ℤ) ^ (d + 1)) :
    ¬ FourNinthsDiagonalTakesAt d ∧
      4 * (fourNinthsDiagonalState d).rho =
        (2 : ℤ) ^ (d + 1) +
          (fourNinthsDiagonalLoad (fourNinthsDiagonalState d) (d + 1) : ℤ) -
          (fourNinthsPairPulse (d + 1) : ℤ) := by
  have hgate := fourNinthsDiagonalState_first_upperExit_eq_skippedBoundary
    d hprev hsaturatedNext.symm.le
  refine ⟨hgate.1, ?_⟩
  have hnotTake : ¬
      ((2 : ℤ) ^ (d + 1) <
        4 * (fourNinthsDiagonalState d).rho +
          (fourNinthsPairPulse (d + 1) : ℤ) -
          (fourNinthsDiagonalLoad
            (fourNinthsDiagonalState d) (d + 1) : ℤ)) := by
    intro htake
    apply hgate.1
    unfold FourNinthsDiagonalTakesAt
    push_cast
    omega
  rw [fourNinthsDiagonalState] at hsaturatedNext
  simp [fourNinthsDiagonalStep, fourNinthsDiagonalState_bits_length,
    hnotTake] at hsaturatedNext
  omega

/-- A first saturation also forces a cheap arithmetic sieve: paired load and source pulse
must agree modulo four. -/
theorem fourNinthsDiagonalState_first_saturation_forces_loadPulse_modFour
    {d : ℕ}
    (hprev : (fourNinthsDiagonalState d).rho < (2 : ℤ) ^ d)
    (hsaturatedNext : (fourNinthsDiagonalState (d + 1)).rho =
      (2 : ℤ) ^ (d + 1)) :
    (4 : ℤ) ∣
      (fourNinthsDiagonalLoad (fourNinthsDiagonalState d) (d + 1) : ℤ) -
        (fourNinthsPairPulse (d + 1) : ℤ) := by
  have hd : 1 ≤ d := by
    by_contra h
    have hd0 : d = 0 := by omega
    subst d
    norm_num [fourNinthsDiagonalState, fourNinthsDiagonalStep,
      fourNinthsDiagonalLoad, fourNinthsPairPulse] at hsaturatedNext
  have hpow : (4 : ℤ) ∣ (2 : ℤ) ^ (d + 1) := by
    rw [show (4 : ℤ) = 2 ^ 2 by norm_num]
    exact pow_dvd_pow 2 (by omega)
  obtain ⟨k, hk⟩ := hpow
  refine ⟨(fourNinthsDiagonalState d).rho - k, ?_⟩
  have hmidline := (fourNinthsDiagonalState_first_saturation_midline
    hprev hsaturatedNext).2
  rw [hk] at hmidline
  omega

/-- The source-current anti-concentration producer: the final half of the actual
pulse/load/decision history never lands on the exact midline required to create a first
saturated state. -/
def FourNinthsSaturationMidlineAvoidance : Prop :=
  ∀ d : ℕ,
    0 ≤ (fourNinthsDiagonalState d).rho →
    (fourNinthsDiagonalState d).rho < (2 : ℤ) ^ d →
    4 * ((∑ j ∈ Finset.Ico (d / 2) d,
      (4 : ℤ) ^ (d - 1 - j) * fourNinthsDiagonalSmallIncrement j) %
        (2 : ℤ) ^ d) ≠
      (2 : ℤ) ^ (d + 1) +
        (fourNinthsDiagonalLoad (fourNinthsDiagonalState d) (d + 1) : ℤ) -
        (fourNinthsPairPulse (d + 1) : ℤ)

/-- Midline avoidance plus nonnegativity rules out every first saturation, hence gives the
strict dyadic upper strip needed by quotient compactness. -/
theorem fourNinthsDiagonalState_strictUpperWindow_of_midlineAvoidance
    (hnonneg : ∀ d : ℕ, 0 ≤ (fourNinthsDiagonalState d).rho)
    (havoid : FourNinthsSaturationMidlineAvoidance) :
    ∀ d : ℕ, (fourNinthsDiagonalState d).rho < (2 : ℤ) ^ d := by
  intro d
  induction d with
  | zero => decide
  | succ d ih =>
      by_contra hnotStrict
      have hgate := fourNinthsDiagonalState_first_upperExit_eq_skippedBoundary
        d ih (by omega)
      have hmidline := fourNinthsDiagonalState_first_saturation_midline
        ih hgate.2
      have hrho := fourNinthsDiagonalState_rho_eq_smallHistoryHalf_emod
        d (hnonneg d) ih
      apply havoid d (hnonneg d) ih
      rw [← hrho]
      exact hmidline.2

/-- A concrete final socket: the selected-landing rank producer supplies nonnegativity,
and half-history midline avoidance supplies the strict compactness window. -/
theorem four_ninths_mem_mersenneAchievementSet_of_rankProducer_of_midlineAvoidance
    (hrank : FourNinthsSelectedLandingRankProducer)
    (havoid : FourNinthsSaturationMidlineAvoidance) :
    (4 / 9 : ℝ) ∈ mersenneAchievementSet := by
  apply four_ninths_mem_mersenneAchievementSet_of_rankProducer_of_upperWindow hrank
  intro d
  exact (fourNinthsDiagonalState_strictUpperWindow_of_midlineAvoidance
    (fourNinthsDiagonal_nonnegative_of_selectedLandingRankProducer hrank)
    havoid d).le

/-- Computationally direct upper producer: no skipped remainder has the full dyadic
divisibility that saturation at its rank would require.  Bounding its 2-adic valuation by
anything strictly below the rank proves this predicate. -/
def FourNinthsSkippedRemainderTwoAdicAvoidance : Prop :=
  ∀ d : ℕ, ¬ FourNinthsDiagonalTakesAt d →
    ¬ (2 : ℤ) ^ (d + 1) ∣ (fourNinthsDiagonalState (d + 1)).rho

/-- Full-rank 2-adic avoidance on skipped rows rules out every first saturation and gives
the strict dyadic upper strip. -/
theorem fourNinthsDiagonalState_strictUpperWindow_of_twoAdicAvoidance
    (havoid : FourNinthsSkippedRemainderTwoAdicAvoidance) :
    ∀ d : ℕ, (fourNinthsDiagonalState d).rho < (2 : ℤ) ^ d := by
  intro d
  induction d with
  | zero => decide
  | succ d ih =>
      by_contra hnotStrict
      have hgate := fourNinthsDiagonalState_first_upperExit_eq_skippedBoundary
        d ih (by omega)
      apply havoid d hgate.1
      rw [hgate.2]

/-- The valuation-shaped endpoint selected by the exact audit. -/
theorem four_ninths_mem_mersenneAchievementSet_of_rankProducer_of_twoAdicAvoidance
    (hrank : FourNinthsSelectedLandingRankProducer)
    (havoid : FourNinthsSkippedRemainderTwoAdicAvoidance) :
    (4 / 9 : ℝ) ∈ mersenneAchievementSet := by
  apply four_ninths_mem_mersenneAchievementSet_of_rankProducer_of_upperWindow hrank
  intro d
  exact (fourNinthsDiagonalState_strictUpperWindow_of_twoAdicAvoidance
    havoid d).le

/-- A saturated escape forces a missing selected ancestor at rank `2a+1`, where the
saturated depth is `3a+1`.  That rank divides the odd member of the escaping row pair and
would alone contribute load two. -/
theorem fourNinthsDiagonalState_saturated_crossing_forces_ancestorHole
    {d : ℕ}
    (hsaturated : (fourNinthsDiagonalState d).rho = (2 : ℤ) ^ d)
    (hcross : (2 : ℤ) ^ (d + 1) <
      (fourNinthsDiagonalState (d + 1)).rho) :
    ∃ a : ℕ, d = 3 * a + 1 ∧
      fourNinthsStateBit (fourNinthsDiagonalState d) (2 * a + 1) = 0 := by
  have hsparse :=
    (fourNinthsDiagonalState_saturated_crosses_iff_sparseLoad
      hsaturated).mp hcross
  have hphase : (d + 1) % 3 = 2 :=
    (fourNinthsPairPulse_eq_three_iff (d + 1)).mp hsparse.1
  let a := d / 3
  have hda : d = 3 * a + 1 := by
    have hdecomp := Nat.mod_add_div d 3
    have hdmod : d % 3 = 1 := by omega
    dsimp [a]
    omega
  refine ⟨a, hda, ?_⟩
  have hbitLe := fourNinthsStateBit_le_one
    (fourNinthsDiagonalState d) (2 * a + 1)
  by_contra hbit0
  have hbit :
      fourNinthsStateBit (fourNinthsDiagonalState d) (2 * a + 1) = 1 := by
    omega
  have hmem : 2 * a + 1 ∈ Finset.range (d + 1) := by
    simp [Finset.mem_range, hda]
    omega
  have hodd : 2 * a + 1 ∣ 2 * (d + 1) - 1 := by
    use 3
    omega
  have hterm :
      2 ≤ fourNinthsRankLoad (2 * a + 1) (d + 1) *
        fourNinthsStateBit (fourNinthsDiagonalState d) (2 * a + 1) := by
    unfold fourNinthsRankLoad
    simp [hodd, hbit]
  have htermLe :
      fourNinthsRankLoad (2 * a + 1) (d + 1) *
          fourNinthsStateBit (fourNinthsDiagonalState d) (2 * a + 1) ≤
        fourNinthsAbstractDiagonalLoad
          (fourNinthsStateBit (fourNinthsDiagonalState d)) (d + 1) := by
    unfold fourNinthsAbstractDiagonalLoad
    exact Finset.single_le_sum
      (fun i _ ↦ Nat.zero_le
        (fourNinthsRankLoad i (d + 1) *
          fourNinthsStateBit (fourNinthsDiagonalState d) i)) hmem
  rw [← fourNinthsDiagonalLoad_eq_abstract] at htermLe
  omega

/-- A saturated escape makes the whole next endpoint pair invisible to every previously
selected rank above two.  Odd-endpoint divisors alone contribute load two; an even-endpoint
divisor combines with the permanent rank-two anchor to contribute load two. -/
theorem fourNinthsDiagonalState_saturated_crossing_forces_divisorHoles
    {d q : ℕ}
    (hsaturated : (fourNinthsDiagonalState d).rho = (2 : ℤ) ^ d)
    (hcross : (2 : ℤ) ^ (d + 1) <
      (fourNinthsDiagonalState (d + 1)).rho)
    (hq3 : 3 ≤ q) (hqd : q ≤ d)
    (hbit : fourNinthsStateBit (fourNinthsDiagonalState d) q = 1) :
    ¬ q ∣ 2 * (d + 1) - 1 ∧ ¬ q ∣ 2 * (d + 1) := by
  have hsparse :=
    (fourNinthsDiagonalState_saturated_crosses_iff_sparseLoad
      hsaturated).mp hcross
  have hqmem : q ∈ Finset.range (d + 1) := by
    simp [Finset.mem_range]
    omega
  have hloadEq := fourNinthsDiagonalLoad_eq_abstract
    (fourNinthsDiagonalState d) (d + 1)
  have hnotOdd : ¬ q ∣ 2 * (d + 1) - 1 := by
    intro hodd
    have hterm :
        2 ≤ fourNinthsRankLoad q (d + 1) *
          fourNinthsStateBit (fourNinthsDiagonalState d) q := by
      unfold fourNinthsRankLoad
      simp [hodd, hbit]
    have htermLe :
        fourNinthsRankLoad q (d + 1) *
            fourNinthsStateBit (fourNinthsDiagonalState d) q ≤
          fourNinthsAbstractDiagonalLoad
            (fourNinthsStateBit (fourNinthsDiagonalState d)) (d + 1) := by
      unfold fourNinthsAbstractDiagonalLoad
      exact Finset.single_le_sum
        (fun i _ ↦ Nat.zero_le
          (fourNinthsRankLoad i (d + 1) *
            fourNinthsStateBit (fourNinthsDiagonalState d) i)) hqmem
    rw [← hloadEq] at htermLe
    omega
  refine ⟨hnotOdd, ?_⟩
  intro heven
  have hd2 : 2 ≤ d := by omega
  have hbit2 := fourNinthsDiagonalState_bit_two_of_ge hd2
  have htwoOdd : ¬ 2 ∣ 2 * (d + 1) - 1 := by omega
  have htwoEven : 2 ∣ 2 * (d + 1) := by
    use d + 1
  have h2q : 2 ≠ q := by omega
  have hpairSubset : ({2, q} : Finset ℕ) ⊆ Finset.range (d + 1) := by
    intro i hi
    simp only [Finset.mem_insert, Finset.mem_singleton] at hi
    rcases hi with rfl | rfl
    · simp [Finset.mem_range]
      omega
    · exact hqmem
  have hpairLe :
      (∑ i ∈ ({2, q} : Finset ℕ),
          fourNinthsRankLoad i (d + 1) *
            fourNinthsStateBit (fourNinthsDiagonalState d) i) ≤
        fourNinthsAbstractDiagonalLoad
          (fourNinthsStateBit (fourNinthsDiagonalState d)) (d + 1) := by
    unfold fourNinthsAbstractDiagonalLoad
    apply Finset.sum_le_sum_of_subset_of_nonneg hpairSubset
    intro i _ _
    omega
  have hpair :
      (∑ i ∈ ({2, q} : Finset ℕ),
          fourNinthsRankLoad i (d + 1) *
            fourNinthsStateBit (fourNinthsDiagonalState d) i) = 2 := by
    simp [h2q, fourNinthsRankLoad, htwoOdd, htwoEven, hnotOdd, heven,
      hbit2, hbit]
  rw [hpair, ← hloadEq] at hpairLe
  omega

/-- Combined counterexample endpoint: the selected-landing rank producer supplies
nonnegativity, while the saturated-load producer supplies the dyadic compactness window. -/
theorem four_ninths_mem_mersenneAchievementSet_of_rankProducer_of_saturatedLoad
    (hrank : FourNinthsSelectedLandingRankProducer)
    (hsaturatedLoad : ∀ d : ℕ,
      (fourNinthsDiagonalState d).rho = (2 : ℤ) ^ d →
      fourNinthsPairPulse (d + 1) = 3 →
      2 ≤ fourNinthsDiagonalLoad (fourNinthsDiagonalState d) (d + 1)) :
    (4 / 9 : ℝ) ∈ mersenneAchievementSet := by
  apply four_ninths_mem_mersenneAchievementSet_of_rankProducer_of_upperWindow hrank
  exact fourNinthsDiagonalState_upperWindow_of_saturatedLoad hsaturatedLoad

#print axioms fourNinthsDiagonalState_saturated_crosses_iff_sparseLoad
#print axioms fourNinthsDiagonalState_upperWindow_of_saturatedLoad
#print axioms fourNinthsDiagonalState_first_saturation_midline
#print axioms fourNinthsDiagonalState_first_saturation_forces_loadPulse_modFour
#print axioms fourNinthsDiagonalState_strictUpperWindow_of_midlineAvoidance
#print axioms fourNinthsDiagonalState_strictUpperWindow_of_twoAdicAvoidance
#print axioms fourNinthsDiagonalState_saturated_crossing_forces_ancestorHole
#print axioms fourNinthsDiagonalState_saturated_crossing_forces_divisorHoles
#print axioms
  four_ninths_mem_mersenneAchievementSet_of_rankProducer_of_midlineAvoidance
#print axioms
  four_ninths_mem_mersenneAchievementSet_of_rankProducer_of_twoAdicAvoidance
#print axioms
  four_ninths_mem_mersenneAchievementSet_of_rankProducer_of_saturatedLoad

end

end FourNinthsUpperSaturation

end ErdosProblems.Erdos257
