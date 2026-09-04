import ErdosProblems.Erdos257.FourNinthsUpperSaturation

/-!
# Adaptive suffix certificates for skipped two-adic concentration

Full-rank divisibility of the executable four-ninths remainder is much more rigid than a
fixed congruence.  Coin cancellation turns it into simultaneous base-four divisibility of
every terminal suffix whose length is at most half the rank.  Thus a hypothetical saturated
row forces an adaptive certificate involving `Theta(d)` small pulse/load/decision increments;
no fixed suffix can capture the obstruction.

This module also records the useful asymmetry of those increments.  Once rank two is present,
every paired load is positive, so a positive small increment can occur only at the pulse-three
phase and only with load at most two.  These sparse positive digits are the only possible
counterweight to the negative carries seen in high-valuation skipped rows.
-/

namespace ErdosProblems.Erdos257

namespace FourNinthsSkippedTwoAdicAntiConcentration

open Erdos257PeriodNoncollapse
open FourNinthsCoinCancellation
open FourNinthsQuotientDefect
open FourNinthsUpperSaturation

noncomputable section

local instance (d : ℕ) : Decidable (FourNinthsDiagonalTakesAt d) :=
  Classical.propDecidable _

/-- Once the permanent rank-two anchor exists, it contributes one unit to every later
paired load through the even endpoint. -/
theorem fourNinthsDiagonalLoad_pos_of_two_le
    {d : ℕ} (hd : 2 ≤ d) :
    1 ≤ fourNinthsDiagonalLoad (fourNinthsDiagonalState d) (d + 1) := by
  have hbit := fourNinthsDiagonalState_bit_two_of_ge hd
  have hmem : 2 ∈ Finset.range (d + 1) := by
    simp [Finset.mem_range]
    omega
  have hodd : ¬ 2 ∣ 2 * (d + 1) - 1 := by omega
  have heven : 2 ∣ 2 * (d + 1) := by
    use d + 1
  have hterm :
      fourNinthsRankLoad 2 (d + 1) *
          fourNinthsStateBit (fourNinthsDiagonalState d) 2 = 1 := by
    simp [fourNinthsRankLoad, hodd, heven, hbit]
  have hle :
      fourNinthsRankLoad 2 (d + 1) *
          fourNinthsStateBit (fourNinthsDiagonalState d) 2 ≤
        fourNinthsAbstractDiagonalLoad
          (fourNinthsStateBit (fourNinthsDiagonalState d)) (d + 1) := by
    unfold fourNinthsAbstractDiagonalLoad
    exact Finset.single_le_sum
      (fun i _ ↦ Nat.zero_le
        (fourNinthsRankLoad i (d + 1) *
          fourNinthsStateBit (fourNinthsDiagonalState d) i)) hmem
  rw [hterm, ← fourNinthsDiagonalLoad_eq_abstract] at hle
  exact hle

/-- Every source-current small increment is at most two after the rank-two anchor appears.
The lower side is deliberately not bounded here: divisor loads create the negative carry. -/
theorem fourNinthsDiagonalSmallIncrement_le_two
    {d : ℕ} (hd : 2 ≤ d) :
    fourNinthsDiagonalSmallIncrement d ≤ 2 := by
  have hload := fourNinthsDiagonalLoad_pos_of_two_le hd
  have hpulse := fourNinthsPairPulse_cases (d + 1)
  rcases hpulse with hpulse | hpulse | hpulse <;>
    simp [fourNinthsDiagonalSmallIncrement, hpulse] <;> omega

/-- The negative side is only linear in the current rank.  Together with the upper bound
`2`, this makes every backward carry state finite at a fixed depth. -/
theorem fourNinthsDiagonalSmallIncrement_lowerBound (d : ℕ) :
    -(2 * (d : ℤ) + 1) ≤ fourNinthsDiagonalSmallIncrement d := by
  have hload := fourNinthsDiagonalLoad_le_two_selectedCount d
  have hcount := fourNinthsDiagonalSelectedCount_le_depth d
  have hpulse : 0 ≤ (fourNinthsPairPulse (d + 1) : ℤ) := by positivity
  by_cases htake : FourNinthsDiagonalTakesAt d <;>
    simp [fourNinthsDiagonalSmallIncrement, htake] <;>
    push_cast at * <;> omega

/-- Positive small digits are sparse-load pulse-three events.  This is the only way a
backward base-four carry can receive a positive correction after rank two. -/
theorem fourNinthsDiagonalSmallIncrement_pos_forces_sparsePulse
    {d : ℕ} (hd : 2 ≤ d)
    (hpos : 0 < fourNinthsDiagonalSmallIncrement d) :
    fourNinthsPairPulse (d + 1) = 3 ∧
      fourNinthsDiagonalLoad (fourNinthsDiagonalState d) (d + 1) ≤ 2 := by
  have hload := fourNinthsDiagonalLoad_pos_of_two_le hd
  have hpulse := fourNinthsPairPulse_cases (d + 1)
  rcases hpulse with hpulse | hpulse | hpulse
  · simp [fourNinthsDiagonalSmallIncrement, hpulse] at hpos
    omega
  · simp [fourNinthsDiagonalSmallIncrement, hpulse] at hpos
    omega
  · refine ⟨hpulse, ?_⟩
    simp [fourNinthsDiagonalSmallIncrement, hpulse] at hpos
    omega

/-- Any prefix ending before the last `k` ranks vanishes modulo `4^k`. -/
theorem fourNinthsSmallHistoryPrefix_dvd
    {d k : ℕ} (hk : k ≤ d) :
    (4 : ℤ) ^ k ∣
      ∑ j ∈ Finset.range (d - k),
        (4 : ℤ) ^ (d - 1 - j) * fourNinthsDiagonalSmallIncrement j := by
  apply Finset.dvd_sum
  intro j hj
  have hjlt : j < d - k := Finset.mem_range.mp hj
  have hexp : k ≤ d - 1 - j := by omega
  exact Dvd.dvd.mul_right (pow_dvd_pow 4 hexp) _

/-- If the actual remainder has full rank-`d` dyadic divisibility, then its complete
small-increment history has the same divisibility. -/
theorem fourNinthsSmallHistory_dvd_of_rho_dvd
    {d : ℕ}
    (hrho : (2 : ℤ) ^ d ∣ (fourNinthsDiagonalState d).rho) :
    (2 : ℤ) ^ d ∣
      fourNinthsWeightedHistory fourNinthsDiagonalSmallIncrement d := by
  obtain ⟨a, ha⟩ := hrho
  obtain ⟨b, hb⟩ := fourNinthsDiagonalDyadicHistory_dvd d
  refine ⟨a + b, ?_⟩
  calc
    fourNinthsWeightedHistory fourNinthsDiagonalSmallIncrement d =
        (fourNinthsDiagonalState d).rho +
          fourNinthsWeightedHistory fourNinthsDiagonalDyadicCharge d := by
      have hid :=
        fourNinthsDiagonalState_rho_eq_smallHistory_sub_dyadicHistory d
      linarith
    _ = (2 : ℤ) ^ d * a + (2 : ℤ) ^ d * b := by rw [ha, hb]
    _ = (2 : ℤ) ^ d * (a + b) := by ring

/-- **Adaptive suffix divisibility.**  Full-rank divisibility of `rho_d` forces the last
`k` small increments to form a multiple of `4^k`, simultaneously for every `2k ≤ d`.
Taking `k = d/2` exposes a terminal window growing linearly with the rank. -/
theorem fourNinthsSmallHistorySuffix_dvd_of_rho_dvd
    {d k : ℕ} (hk : 2 * k ≤ d)
    (hrho : (2 : ℤ) ^ d ∣ (fourNinthsDiagonalState d).rho) :
    (4 : ℤ) ^ k ∣
      ∑ j ∈ Finset.Ico (d - k) d,
        (4 : ℤ) ^ (d - 1 - j) * fourNinthsDiagonalSmallIncrement j := by
  have hk' : k ≤ d := by omega
  have hpow : (4 : ℤ) ^ k ∣ (2 : ℤ) ^ d := by
    rw [show (4 : ℤ) = 2 ^ 2 by norm_num, ← pow_mul]
    exact pow_dvd_pow 2 hk
  have hfull :
      (4 : ℤ) ^ k ∣
        ∑ j ∈ Finset.range d,
          (4 : ℤ) ^ (d - 1 - j) * fourNinthsDiagonalSmallIncrement j := by
    apply dvd_trans hpow
    simpa only [fourNinthsWeightedHistory_eq_sum] using
      fourNinthsSmallHistory_dvd_of_rho_dvd hrho
  have hprefix := fourNinthsSmallHistoryPrefix_dvd (d := d) hk'
  have hsplit :
      (∑ j ∈ Finset.range (d - k),
          (4 : ℤ) ^ (d - 1 - j) * fourNinthsDiagonalSmallIncrement j) +
        (∑ j ∈ Finset.Ico (d - k) d,
          (4 : ℤ) ^ (d - 1 - j) * fourNinthsDiagonalSmallIncrement j) =
        ∑ j ∈ Finset.range d,
          (4 : ℤ) ^ (d - 1 - j) * fourNinthsDiagonalSmallIncrement j :=
    Finset.sum_range_add_sum_Ico
      (fun j ↦ (4 : ℤ) ^ (d - 1 - j) * fourNinthsDiagonalSmallIncrement j)
      (Nat.sub_le d k)
  obtain ⟨a, ha⟩ := hfull
  obtain ⟨b, hb⟩ := hprefix
  refine ⟨a - b, ?_⟩
  calc
    (∑ j ∈ Finset.Ico (d - k) d,
        (4 : ℤ) ^ (d - 1 - j) * fourNinthsDiagonalSmallIncrement j) =
        (∑ j ∈ Finset.range d,
          (4 : ℤ) ^ (d - 1 - j) * fourNinthsDiagonalSmallIncrement j) -
        (∑ j ∈ Finset.range (d - k),
          (4 : ℤ) ^ (d - 1 - j) * fourNinthsDiagonalSmallIncrement j) := by
      rw [← hsplit]
      ring
    _ = (4 : ℤ) ^ k * a - (4 : ℤ) ^ k * b := by rw [ha, hb]
    _ = (4 : ℤ) ^ k * (a - b) := by ring

/-- A skipped row satisfying the proposed full-rank two-adic obstruction therefore emits
the entire adaptive family of suffix certificates. -/
theorem fourNinthsSkippedRemainder_forces_adaptiveSuffix
    {d k : ℕ} (hk : 2 * k ≤ d + 1)
    (_hskip : ¬ FourNinthsDiagonalTakesAt d)
    (hdiv : (2 : ℤ) ^ (d + 1) ∣ (fourNinthsDiagonalState (d + 1)).rho) :
    (4 : ℤ) ^ k ∣
      ∑ j ∈ Finset.Ico (d + 1 - k) (d + 1),
        (4 : ℤ) ^ (d + 1 - 1 - j) * fourNinthsDiagonalSmallIncrement j := by
  exact fourNinthsSmallHistorySuffix_dvd_of_rho_dvd hk hdiv

/-- The first member of the adaptive family says that the latest small increment itself
is divisible by four. -/
theorem fourNinthsLatestSmallIncrement_dvd_four_of_rho_dvd
    {d : ℕ} (hd : 1 ≤ d)
    (hrho : (2 : ℤ) ^ (d + 1) ∣ (fourNinthsDiagonalState (d + 1)).rho) :
    (4 : ℤ) ∣ fourNinthsDiagonalSmallIncrement d := by
  have hsuffix := fourNinthsSmallHistorySuffix_dvd_of_rho_dvd
    (d := d + 1) (k := 1) (by omega) hrho
  simpa using hsuffix

/-- Because small increments are at most two, the newest digit of a full-rank divisible
row cannot be positive.  High two-adic concentration therefore begins with a zero or
negative carry, exactly as in the record-valuation computations. -/
theorem fourNinthsLatestSmallIncrement_nonpos_of_rho_dvd
    {d : ℕ} (hd : 2 ≤ d)
    (hrho : (2 : ℤ) ^ (d + 1) ∣ (fourNinthsDiagonalState (d + 1)).rho) :
    fourNinthsDiagonalSmallIncrement d ≤ 0 := by
  obtain ⟨c, hc⟩ := fourNinthsLatestSmallIncrement_dvd_four_of_rho_dvd
    (by omega : 1 ≤ d) hrho
  have hle := fourNinthsDiagonalSmallIncrement_le_two hd
  by_contra hpos
  have hpos' : 0 < fourNinthsDiagonalSmallIncrement d := by omega
  rw [hc] at hpos' hle
  omega

#print axioms fourNinthsDiagonalLoad_pos_of_two_le
#print axioms fourNinthsDiagonalSmallIncrement_le_two
#print axioms fourNinthsDiagonalSmallIncrement_lowerBound
#print axioms fourNinthsDiagonalSmallIncrement_pos_forces_sparsePulse
#print axioms fourNinthsSmallHistoryPrefix_dvd
#print axioms fourNinthsSmallHistory_dvd_of_rho_dvd
#print axioms fourNinthsSmallHistorySuffix_dvd_of_rho_dvd
#print axioms fourNinthsSkippedRemainder_forces_adaptiveSuffix
#print axioms fourNinthsLatestSmallIncrement_dvd_four_of_rho_dvd
#print axioms fourNinthsLatestSmallIncrement_nonpos_of_rho_dvd

end

end FourNinthsSkippedTwoAdicAntiConcentration

end ErdosProblems.Erdos257
