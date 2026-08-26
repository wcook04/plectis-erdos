import ErdosProblems.Erdos257.FourNinthsNegativeCarryNoGo

/-!
# Midpoint reachability equation for four-ninths carries

The adaptive suffix certificates are local necessary conditions.  At an even depth `2k`,
the exact history recurrence supplies the missing source coupling: after division by `4^k`,
every selected dyadic coin in the final half becomes one binary digit.  Thus a full-rank
two-adic row ties the midpoint remainder to the complete future-half take word and the
small-increment carry.
-/

namespace ErdosProblems.Erdos257

namespace FourNinthsMidpointCarryReachability

open Erdos257PeriodNoncollapse
open FourNinthsCoinCancellation
open FourNinthsSkippedTwoAdicAntiConcentration
open FourNinthsQuotientCompactness

noncomputable section

local instance (d : ℕ) : Decidable (FourNinthsDiagonalTakesAt d) :=
  Classical.propDecidable _

/-- The small signed contribution from the final half of depth `2k`. -/
def fourNinthsMidpointSmallSuffix (k : ℕ) : ℤ :=
  ∑ j ∈ Finset.Ico k (2 * k),
    (4 : ℤ) ^ (2 * k - 1 - j) * fourNinthsDiagonalSmallIncrement j

/-- The pure dyadic-coin contribution from the same final half. -/
def fourNinthsMidpointDyadicSuffix (k : ℕ) : ℤ :=
  ∑ j ∈ Finset.Ico k (2 * k),
    (4 : ℤ) ^ (2 * k - 1 - j) * fourNinthsDiagonalDyadicCharge j

/-- The final-half take decisions read as a `k`-digit binary word, newest decision least
significant. -/
def fourNinthsMidpointTakeWord (k : ℕ) : ℤ :=
  ∑ j ∈ Finset.Ico k (2 * k),
    (2 : ℤ) ^ (2 * k - 1 - j) *
      if FourNinthsDiagonalTakesAt j then 1 else 0

/-- The small final-half contribution at odd depth `2k+1`.  The split point is
`k+1`, leaving exactly `k` base-four digits in the suffix. -/
def fourNinthsOddMidpointSmallSuffix (k : ℕ) : ℤ :=
  ∑ j ∈ Finset.Ico (k + 1) (2 * k + 1),
    (4 : ℤ) ^ (2 * k - j) * fourNinthsDiagonalSmallIncrement j

/-- The selected dyadic coins in the odd final half, after removing `4^k`.
The resulting word is even: its newest digit has binary weight two. -/
def fourNinthsOddMidpointTakeWord (k : ℕ) : ℤ :=
  ∑ j ∈ Finset.Ico (k + 1) (2 * k + 1),
    (2 : ℤ) ^ (2 * k - j + 1) *
      if FourNinthsDiagonalTakesAt j then 1 else 0

/-- Split a base-four weighted history at an arbitrary midpoint. -/
theorem fourNinthsWeightedHistory_add (q : ℕ → ℤ) (m k : ℕ) :
    fourNinthsWeightedHistory q (m + k) =
      (4 : ℤ) ^ k * fourNinthsWeightedHistory q m +
        ∑ j ∈ Finset.Ico m (m + k),
          (4 : ℤ) ^ (m + k - 1 - j) * q j := by
  rw [fourNinthsWeightedHistory_eq_sum, fourNinthsWeightedHistory_eq_sum]
  rw [← Finset.sum_range_add_sum_Ico
    (fun j ↦ (4 : ℤ) ^ (m + k - 1 - j) * q j) (Nat.le_add_right m k)]
  apply congrArg (fun z : ℤ => z +
    ∑ j ∈ Finset.Ico m (m + k), (4 : ℤ) ^ (m + k - 1 - j) * q j)
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j hj
  have hjm : j < m := Finset.mem_range.mp hj
  have hexp : m + k - 1 - j = k + (m - 1 - j) := by omega
  rw [hexp, pow_add]
  ring

/-- Exact final-half decomposition of the executable remainder. -/
theorem fourNinthsDiagonalState_rho_two_mul (k : ℕ) :
    (fourNinthsDiagonalState (2 * k)).rho =
      (4 : ℤ) ^ k * (fourNinthsDiagonalState k).rho +
        fourNinthsMidpointSmallSuffix k - fourNinthsMidpointDyadicSuffix k := by
  rw [fourNinthsDiagonalState_rho_eq_smallHistory_sub_dyadicHistory]
  have hsmall := fourNinthsWeightedHistory_add
    fourNinthsDiagonalSmallIncrement k k
  have hdyadic := fourNinthsWeightedHistory_add
    fourNinthsDiagonalDyadicCharge k k
  rw [show k + k = 2 * k by omega] at hsmall hdyadic
  rw [hsmall, hdyadic]
  simp only [fourNinthsMidpointSmallSuffix, fourNinthsMidpointDyadicSuffix]
  have hmid := fourNinthsDiagonalState_rho_eq_smallHistory_sub_dyadicHistory k
  rw [hmid]
  ring

/-- After division by `4^k`, every final-half dyadic coin is exactly one digit of the
future-half binary take word. -/
theorem fourNinthsMidpointDyadicSuffix_eq (k : ℕ) :
    fourNinthsMidpointDyadicSuffix k =
      (4 : ℤ) ^ k * fourNinthsMidpointTakeWord k := by
  unfold fourNinthsMidpointDyadicSuffix fourNinthsMidpointTakeWord
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j hj
  have hjlo : k ≤ j := (Finset.mem_Ico.mp hj).1
  have hjhi : j < 2 * k := (Finset.mem_Ico.mp hj).2
  classical
  by_cases htake : FourNinthsDiagonalTakesAt j
  · simp only [fourNinthsDiagonalDyadicCharge, htake, if_pos]
    have hexp :
        2 * (2 * k - 1 - j) + (j + 1) =
          2 * k + (2 * k - 1 - j) := by omega
    rw [show (4 : ℤ) = 2 ^ 2 by norm_num, ← pow_mul, ← pow_add,
      hexp, pow_add]
    rw [show (2 : ℤ) ^ (2 * k) = 4 ^ k by
      rw [show (4 : ℤ) = 2 ^ 2 by norm_num, ← pow_mul]]
    ring
  · simp [fourNinthsDiagonalDyadicCharge, htake]

/-- **Midpoint source-reachability equation.**  Full-rank divisibility at even depth
`2k` produces an output quotient `z` and a small carry `c`; they are not independent.
They obey `z = rho_k + c - W_k`, where `W_k` is the complete binary take word from the
future half. -/
theorem fourNinthsMidpointCarryEquation_of_rho_dvd
    {k : ℕ}
    (hrho : (2 : ℤ) ^ (2 * k) ∣ (fourNinthsDiagonalState (2 * k)).rho) :
    ∃ z c : ℤ,
      (fourNinthsDiagonalState (2 * k)).rho = (4 : ℤ) ^ k * z ∧
      fourNinthsMidpointSmallSuffix k = (4 : ℤ) ^ k * c ∧
      z = (fourNinthsDiagonalState k).rho + c - fourNinthsMidpointTakeWord k := by
  have hpow : (2 : ℤ) ^ (2 * k) = (4 : ℤ) ^ k := by
    rw [show (4 : ℤ) = 2 ^ 2 by norm_num, ← pow_mul]
  rw [hpow] at hrho
  obtain ⟨z, hz⟩ := hrho
  have hsuffix := fourNinthsSmallHistorySuffix_dvd_of_rho_dvd
    (d := 2 * k) (k := k) (by omega) (by simpa [hpow] using ⟨z, hz⟩)
  simp only [show 2 * k - k = k by omega] at hsuffix
  obtain ⟨c, hc⟩ := hsuffix
  change fourNinthsMidpointSmallSuffix k = (4 : ℤ) ^ k * c at hc
  refine ⟨z, c, hz, hc, ?_⟩
  have hstate := fourNinthsDiagonalState_rho_two_mul k
  rw [hz, hc, fourNinthsMidpointDyadicSuffix_eq] at hstate
  have hpowpos : (0 : ℤ) < (4 : ℤ) ^ k := by positivity
  nlinarith

/-- At an even saturated row, the output quotient is one.  The midpoint remainder must
therefore equal the future-half binary word minus the small carry plus one. -/
theorem fourNinthsMidpointCarryEquation_of_saturated
    {k : ℕ}
    (hsat : (fourNinthsDiagonalState (2 * k)).rho = (2 : ℤ) ^ (2 * k)) :
    ∃ c : ℤ,
      fourNinthsMidpointSmallSuffix k = (4 : ℤ) ^ k * c ∧
      (fourNinthsDiagonalState k).rho + c - fourNinthsMidpointTakeWord k = 1 := by
  have hdvd : (2 : ℤ) ^ (2 * k) ∣ (fourNinthsDiagonalState (2 * k)).rho := by
    exact ⟨1, by simpa using hsat⟩
  obtain ⟨z, c, hz, hc, heq⟩ :=
    fourNinthsMidpointCarryEquation_of_rho_dvd hdvd
  have hpow : (2 : ℤ) ^ (2 * k) = (4 : ℤ) ^ k := by
    rw [show (4 : ℤ) = 2 ^ 2 by norm_num, ← pow_mul]
  have hpowpos : (0 : ℤ) < (4 : ℤ) ^ k := by positivity
  refine ⟨c, hc, ?_⟩
  rw [hsat, hpow] at hz
  have hzone : z = 1 := by nlinarith
  rw [← heq, hzone]

/-- Once the midpoint begins beyond rank two, its whole small-increment suffix is
strictly smaller than one base-four place.  This is one-sided: negative divisor loads
are allowed to be arbitrarily large, while every positive digit is at most two. -/
theorem fourNinthsMidpointSmallSuffix_lt_fourPow
    {k : ℕ} (hk : 2 ≤ k) :
    fourNinthsMidpointSmallSuffix k < (4 : ℤ) ^ k := by
  have hterm :
      fourNinthsMidpointSmallSuffix k ≤
        ∑ j ∈ Finset.Ico k (2 * k),
          (4 : ℤ) ^ (2 * k - 1 - j) * 2 := by
    unfold fourNinthsMidpointSmallSuffix
    apply Finset.sum_le_sum
    intro j hj
    have hjlo : k ≤ j := (Finset.mem_Ico.mp hj).1
    exact mul_le_mul_of_nonneg_left
      (fourNinthsDiagonalSmallIncrement_le_two (hk.trans hjlo)) (by positivity)
  have hreflect :
      (∑ j ∈ Finset.Ico k (2 * k), (4 : ℤ) ^ (2 * k - 1 - j)) =
        ∑ j ∈ Finset.range k, (4 : ℤ) ^ j := by
    have href := Finset.sum_Ico_reflect (fun j : ℕ ↦ (4 : ℤ) ^ j) k
      (m := 2 * k) (n := 2 * k - 1) (by omega)
    rw [show 2 * k - 1 + 1 - 2 * k = 0 by omega,
      show 2 * k - 1 + 1 - k = k by omega] at href
    simpa [Nat.Ico_zero_eq_range] using href
  have hgeom := geom_sum_mul (4 : ℤ) k
  rw [← Finset.sum_mul, hreflect] at hterm
  have hsum_nonneg :
      0 ≤ ∑ j ∈ Finset.range k, (4 : ℤ) ^ j := by positivity
  nlinarith

/-- A base-four-divisible midpoint suffix therefore has a nonpositive normalized carry.
This is the analytic explanation of the computational observation that every exact
carry certificate encountered had value in `{-12, …, 0}` and never a positive value. -/
theorem fourNinthsMidpointSmallCarry_nonpos
    {k : ℕ} (hk : 2 ≤ k) {c : ℤ}
    (hc : fourNinthsMidpointSmallSuffix k = (4 : ℤ) ^ k * c) :
    c ≤ 0 := by
  have hsuffix := fourNinthsMidpointSmallSuffix_lt_fourPow hk
  rw [hc] at hsuffix
  have hpowpos : (0 : ℤ) < (4 : ℤ) ^ k := by positivity
  nlinarith

/-- Saturation forces the complete future-half binary word to lie strictly below the
actual midpoint remainder.  Unlike a free carry automaton, the word is generated by the
same greedy trajectory as that remainder. -/
theorem fourNinthsMidpointTakeWord_lt_rho_of_saturated
    {k : ℕ} (hk : 2 ≤ k)
    (hsat : (fourNinthsDiagonalState (2 * k)).rho = (2 : ℤ) ^ (2 * k)) :
    fourNinthsMidpointTakeWord k < (fourNinthsDiagonalState k).rho := by
  obtain ⟨c, hc, heq⟩ := fourNinthsMidpointCarryEquation_of_saturated hsat
  have hc0 := fourNinthsMidpointSmallCarry_nonpos hk hc
  omega

/-! ## Odd-depth companion

The same source coupling covers the parity omitted by the symmetric `2k` split.  At
depth `2k+1` the natural split is after `k+1` transitions, leaving `k` final digits.
The saturated quotient is now two instead of one. -/

theorem fourNinthsDiagonalState_rho_two_mul_add_one (k : ℕ) :
    (fourNinthsDiagonalState (2 * k + 1)).rho =
      (4 : ℤ) ^ k * (fourNinthsDiagonalState (k + 1)).rho +
        fourNinthsOddMidpointSmallSuffix k -
          (4 : ℤ) ^ k * fourNinthsOddMidpointTakeWord k := by
  rw [fourNinthsDiagonalState_rho_eq_smallHistory_sub_dyadicHistory]
  have hsmall := fourNinthsWeightedHistory_add
    fourNinthsDiagonalSmallIncrement (k + 1) k
  have hdyadic := fourNinthsWeightedHistory_add
    fourNinthsDiagonalDyadicCharge (k + 1) k
  rw [show k + 1 + k = 2 * k + 1 by omega] at hsmall hdyadic
  rw [hsmall, hdyadic]
  have hmid :=
    fourNinthsDiagonalState_rho_eq_smallHistory_sub_dyadicHistory (k + 1)
  have hsmallSuffix :
      (∑ j ∈ Finset.Ico (k + 1) (2 * k + 1),
          (4 : ℤ) ^ (2 * k + 1 - 1 - j) *
            fourNinthsDiagonalSmallIncrement j) =
        fourNinthsOddMidpointSmallSuffix k := by
    unfold fourNinthsOddMidpointSmallSuffix
    apply Finset.sum_congr rfl
    intro j hj
    congr 2
  have hdyadicSuffix :
      (∑ j ∈ Finset.Ico (k + 1) (2 * k + 1),
          (4 : ℤ) ^ (2 * k + 1 - 1 - j) *
            fourNinthsDiagonalDyadicCharge j) =
        (4 : ℤ) ^ k * fourNinthsOddMidpointTakeWord k := by
    unfold fourNinthsOddMidpointTakeWord
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j hj
    have hjlo : k + 1 ≤ j := (Finset.mem_Ico.mp hj).1
    have hjhi : j < 2 * k + 1 := (Finset.mem_Ico.mp hj).2
    classical
    by_cases htake : FourNinthsDiagonalTakesAt j
    · simp only [fourNinthsDiagonalDyadicCharge, htake, if_pos]
      have hweight : 2 * k + 1 - 1 - j = 2 * k - j := by omega
      rw [hweight]
      have hexp :
          2 * (2 * k - j) + (j + 1) =
            2 * k + (2 * k - j + 1) := by omega
      rw [show (4 : ℤ) = 2 ^ 2 by norm_num, ← pow_mul, ← pow_add,
        hexp, pow_add]
      rw [show (2 : ℤ) ^ (2 * k) = 4 ^ k by
        rw [show (4 : ℤ) = 2 ^ 2 by norm_num, ← pow_mul]]
      ring
    · simp [fourNinthsDiagonalDyadicCharge, htake]
  rw [hsmallSuffix, hdyadicSuffix, hmid]
  ring

theorem fourNinthsOddMidpointSmallSuffix_lt_fourPow
    {k : ℕ} (hk : 1 ≤ k) :
    fourNinthsOddMidpointSmallSuffix k < (4 : ℤ) ^ k := by
  have hterm :
      fourNinthsOddMidpointSmallSuffix k ≤
        ∑ j ∈ Finset.Ico (k + 1) (2 * k + 1),
          (4 : ℤ) ^ (2 * k - j) * 2 := by
    unfold fourNinthsOddMidpointSmallSuffix
    apply Finset.sum_le_sum
    intro j hj
    have hjlo : k + 1 ≤ j := (Finset.mem_Ico.mp hj).1
    exact mul_le_mul_of_nonneg_left
      (fourNinthsDiagonalSmallIncrement_le_two (by omega)) (by positivity)
  have hreflect :
      (∑ j ∈ Finset.Ico (k + 1) (2 * k + 1), (4 : ℤ) ^ (2 * k - j)) =
        ∑ j ∈ Finset.range k, (4 : ℤ) ^ j := by
    have href := Finset.sum_Ico_reflect (fun j : ℕ ↦ (4 : ℤ) ^ j) (k + 1)
      (m := 2 * k + 1) (n := 2 * k) (by omega)
    rw [show 2 * k + 1 - (2 * k + 1) = 0 by omega,
      show 2 * k + 1 - (k + 1) = k by omega] at href
    simpa [Nat.Ico_zero_eq_range] using href
  have hgeom := geom_sum_mul (4 : ℤ) k
  rw [← Finset.sum_mul, hreflect] at hterm
  have hsum_nonneg :
      0 ≤ ∑ j ∈ Finset.range k, (4 : ℤ) ^ j := by positivity
  nlinarith

/-- Odd saturation imposes the same nonpositive carry, with quotient two. -/
theorem fourNinthsOddMidpointCarryEquation_of_saturated
    {k : ℕ} (hk : 1 ≤ k)
    (hsat : (fourNinthsDiagonalState (2 * k + 1)).rho =
      (2 : ℤ) ^ (2 * k + 1)) :
    ∃ c : ℤ,
      fourNinthsOddMidpointSmallSuffix k = (4 : ℤ) ^ k * c ∧
      c ≤ 0 ∧
      (fourNinthsDiagonalState (k + 1)).rho + c -
        fourNinthsOddMidpointTakeWord k = 2 := by
  have hdvd : (2 : ℤ) ^ (2 * k + 1) ∣
      (fourNinthsDiagonalState (2 * k + 1)).rho := ⟨1, by simpa using hsat⟩
  have hsuffix := fourNinthsSmallHistorySuffix_dvd_of_rho_dvd
    (d := 2 * k + 1) (k := k) (by omega) hdvd
  simp only [show 2 * k + 1 - k = k + 1 by omega] at hsuffix
  obtain ⟨c, hc⟩ := hsuffix
  change fourNinthsOddMidpointSmallSuffix k = (4 : ℤ) ^ k * c at hc
  have hc0 : c ≤ 0 := by
    have hslt := fourNinthsOddMidpointSmallSuffix_lt_fourPow hk
    rw [hc] at hslt
    have hpowpos : (0 : ℤ) < (4 : ℤ) ^ k := by positivity
    nlinarith
  refine ⟨c, hc, hc0, ?_⟩
  have hstate := fourNinthsDiagonalState_rho_two_mul_add_one k
  rw [hsat, hc] at hstate
  have hpow : (2 : ℤ) ^ (2 * k + 1) = (4 : ℤ) ^ k * 2 := by
    rw [show 2 * k + 1 = 2 * k + 1 by rfl, pow_add, pow_one]
    rw [show (2 : ℤ) ^ (2 * k) = 4 ^ k by
      rw [show (4 : ℤ) = 2 ^ 2 by norm_num, ← pow_mul]]
  rw [hpow] at hstate
  have hpowpos : (0 : ℤ) < (4 : ℤ) ^ k := by positivity
  nlinarith

theorem fourNinthsOddMidpointTakeWord_add_two_le_rho_of_saturated
    {k : ℕ} (hk : 1 ≤ k)
    (hsat : (fourNinthsDiagonalState (2 * k + 1)).rho =
      (2 : ℤ) ^ (2 * k + 1)) :
    fourNinthsOddMidpointTakeWord k + 2 ≤
      (fourNinthsDiagonalState (k + 1)).rho := by
  obtain ⟨c, _, hc0, heq⟩ :=
    fourNinthsOddMidpointCarryEquation_of_saturated hk hsat
  omega

/-! ## Exact all-parity producer interface -/

/-- The remaining source-sensitive upper producer.  It excludes exactly the normalized
carry equalities emitted by even and odd saturation; unlike a free word-gap inequality,
the carry is required to be the actual small-history suffix. -/
def FourNinthsMidpointCarryEqualityAvoidance : Prop :=
  (∀ (k : ℕ) (c : ℤ), 2 ≤ k →
    fourNinthsMidpointSmallSuffix k = (4 : ℤ) ^ k * c →
    (fourNinthsDiagonalState k).rho + c -
      fourNinthsMidpointTakeWord k ≠ 1) ∧
  (∀ (k : ℕ) (c : ℤ), 1 ≤ k →
    fourNinthsOddMidpointSmallSuffix k = (4 : ℤ) ^ k * c →
    (fourNinthsDiagonalState (k + 1)).rho + c -
      fourNinthsOddMidpointTakeWord k ≠ 2)

/-- Avoiding the two exact midpoint equations excludes saturation at every depth. -/
theorem fourNinthsDiagonalState_ne_twoPow_of_midpointCarryEqualityAvoidance
    (havoid : FourNinthsMidpointCarryEqualityAvoidance) (d : ℕ) :
    (fourNinthsDiagonalState d).rho ≠ (2 : ℤ) ^ d := by
  rcases Nat.even_or_odd d with ⟨k, rfl⟩ | ⟨k, rfl⟩
  · by_cases hk : 2 ≤ k
    · intro hsat
      have hsat' :
          (fourNinthsDiagonalState (2 * k)).rho = (2 : ℤ) ^ (2 * k) := by
        simpa [two_mul] using hsat
      obtain ⟨c, hc, heq⟩ :=
        fourNinthsMidpointCarryEquation_of_saturated hsat'
      exact havoid.1 k c hk hc heq
    · have hkcases : k = 0 ∨ k = 1 := by omega
      rcases hkcases with rfl | rfl <;> decide
  · by_cases hk : 1 ≤ k
    · intro hsat
      have hsat' :
          (fourNinthsDiagonalState (2 * k + 1)).rho =
            (2 : ℤ) ^ (2 * k + 1) := by
        simpa [two_mul] using hsat
      obtain ⟨c, hc, _, heq⟩ :=
        fourNinthsOddMidpointCarryEquation_of_saturated hk hsat'
      exact havoid.2 k c hk hc heq
    · have hk0 : k = 0 := by omega
      subst k
      decide

/-- The midpoint equality producer propagates the strict dyadic upper strip directly.
Take rows preserve strictness; a skipped row can only reach the weak boundary, which the
all-parity midpoint theorem excludes. -/
theorem fourNinthsDiagonalState_strictUpperWindow_of_midpointCarryEqualityAvoidance
    (havoid : FourNinthsMidpointCarryEqualityAvoidance) :
    ∀ d : ℕ, (fourNinthsDiagonalState d).rho < (2 : ℤ) ^ d := by
  intro d
  induction d with
  | zero => decide
  | succ d ih =>
      by_cases htake : FourNinthsDiagonalTakesAt d
      · exact fourNinthsDiagonalState_rho_succ_lt_twoPow_of_takes_of_prev_lt
          d htake ih
      · have hle := fourNinthsDiagonalState_rho_succ_le_twoPow_of_not_takes d htake
        exact lt_of_le_of_ne hle
          (fourNinthsDiagonalState_ne_twoPow_of_midpointCarryEqualityAvoidance
            havoid (d + 1))

/-- Conversely, the strict upper strip excludes both exact midpoint equations.  Thus the
new producer is not a padded sufficient condition: it is the exact all-parity saturation
throat written in source coordinates. -/
theorem fourNinthsMidpointCarryEqualityAvoidance_of_strictUpperWindow
    (hstrict : ∀ d : ℕ,
      (fourNinthsDiagonalState d).rho < (2 : ℤ) ^ d) :
    FourNinthsMidpointCarryEqualityAvoidance := by
  constructor
  · intro k c hk hc heq
    have hstate := fourNinthsDiagonalState_rho_two_mul k
    rw [hc, fourNinthsMidpointDyadicSuffix_eq] at hstate
    have hpowpos : (0 : ℤ) < (4 : ℤ) ^ k := by positivity
    have hsaturated :
        (fourNinthsDiagonalState (2 * k)).rho = (4 : ℤ) ^ k := by
      nlinarith
    have hlt := hstrict (2 * k)
    have hpow : (2 : ℤ) ^ (2 * k) = (4 : ℤ) ^ k := by
      rw [show (4 : ℤ) = 2 ^ 2 by norm_num, ← pow_mul]
    rw [hsaturated, hpow] at hlt
    omega
  · intro k c hk hc heq
    have hstate := fourNinthsDiagonalState_rho_two_mul_add_one k
    rw [hc] at hstate
    have hpowpos : (0 : ℤ) < (4 : ℤ) ^ k := by positivity
    have hsaturated :
        (fourNinthsDiagonalState (2 * k + 1)).rho = (4 : ℤ) ^ k * 2 := by
      nlinarith
    have hlt := hstrict (2 * k + 1)
    have hpow : (2 : ℤ) ^ (2 * k + 1) = (4 : ℤ) ^ k * 2 := by
      rw [pow_add, pow_one]
      rw [show (2 : ℤ) ^ (2 * k) = 4 ^ k by
        rw [show (4 : ℤ) = 2 ^ 2 by norm_num, ← pow_mul]]
    rw [hsaturated, hpow] at hlt
    omega

theorem fourNinthsMidpointCarryEqualityAvoidance_iff_strictUpperWindow :
    FourNinthsMidpointCarryEqualityAvoidance ↔
      ∀ d : ℕ, (fourNinthsDiagonalState d).rho < (2 : ℤ) ^ d := by
  constructor
  · exact fourNinthsDiagonalState_strictUpperWindow_of_midpointCarryEqualityAvoidance
  · exact fourNinthsMidpointCarryEqualityAvoidance_of_strictUpperWindow

/-- Once the independent selected-landing rank producer supplies nonnegativity, exclusion
of the exact midpoint carry equalities closes the compactness consumer and gives `4/9`
membership.  Both producers remain explicit hypotheses. -/
theorem four_ninths_mem_mersenneAchievementSet_of_rankProducer_of_midpointCarryAvoidance
    (hrank : FourNinthsSelectedLandingRankProducer)
    (havoid : FourNinthsMidpointCarryEqualityAvoidance) :
    (4 / 9 : ℝ) ∈ mersenneAchievementSet := by
  apply four_ninths_mem_mersenneAchievementSet_of_rankProducer_of_upperWindow hrank
  intro d
  exact (fourNinthsDiagonalState_strictUpperWindow_of_midpointCarryEqualityAvoidance
    havoid d).le

#print axioms fourNinthsWeightedHistory_add
#print axioms fourNinthsDiagonalState_rho_two_mul
#print axioms fourNinthsMidpointDyadicSuffix_eq
#print axioms fourNinthsMidpointCarryEquation_of_rho_dvd
#print axioms fourNinthsMidpointCarryEquation_of_saturated
#print axioms fourNinthsMidpointSmallSuffix_lt_fourPow
#print axioms fourNinthsMidpointSmallCarry_nonpos
#print axioms fourNinthsMidpointTakeWord_lt_rho_of_saturated
#print axioms fourNinthsDiagonalState_rho_two_mul_add_one
#print axioms fourNinthsOddMidpointSmallSuffix_lt_fourPow
#print axioms fourNinthsOddMidpointCarryEquation_of_saturated
#print axioms fourNinthsOddMidpointTakeWord_add_two_le_rho_of_saturated
#print axioms fourNinthsDiagonalState_ne_twoPow_of_midpointCarryEqualityAvoidance
#print axioms
  fourNinthsDiagonalState_strictUpperWindow_of_midpointCarryEqualityAvoidance
#print axioms
  fourNinthsMidpointCarryEqualityAvoidance_iff_strictUpperWindow
#print axioms
  four_ninths_mem_mersenneAchievementSet_of_rankProducer_of_midpointCarryAvoidance

end

end FourNinthsMidpointCarryReachability

end ErdosProblems.Erdos257
