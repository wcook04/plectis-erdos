import Erdos249257.FourNinthsDiagonalHistory

/-!
# The 4/9 coin term cancels: `ρ_d` is a small-integer base-four residue

`FourNinthsDiagonalMarginInvariant.md` gives the history identity (5)

`ρ_d = Σ_{j<d} 4^(d−1−j) q_j`,  `q_j = u_{j+1} − A_{j+1} − b_{j+1}(2^(j+1)+1)`,

and closes by saying its finite facts "neither prove that the required suffix excess is
unbounded nor rule out **a genuinely nonlocal use of (5)**". This module supplies the
arithmetic core of such a use.

## The point

Split the coin `2^(j+1) + 1` into its power part and its unit. Reindexing `i = j + 1`, the
power part contributes `Σ_{i≤d} 4^(d−i) · b_i · 2^i`, and **every one of those terms is
divisible by `2^d`**, because `4^(d−i) · 2^i = 2^(2d−i)` with `2d − i ≥ d` for `i ≤ d`. So
modulo `2^d` the exponentially large coin vanishes entirely and

`ρ_d ≡ Σ_{i≤d} 4^(d−i) (u_i − A_i − b_i)  (mod 2^d)`,

a base-four sum of **small** integers: `u_i ∈ {0,1,3}`, `b_i ∈ {0,1}`, `A_i` the paired
divisor load. Terms with `i ≤ d/2` are themselves divisible by `2^d`, so only the last
`⌈d/2⌉` ranks survive. And since `0 ≤ ρ_d < 2^d` on the orbit, that residue **pins `ρ_d`
exactly** rather than merely constraining it.

Verified with zero violations for `d = 2 … 900` by
`scripts/four_ninths_coin_cancellation.py`, together with `0 ≤ ρ_d < 2^d` at all 899 ranks.

## Why it matters for the socket

The socket `b_d = 1 ⟹ d ≤ ρ_d` looked like a comparison against the exponential coin. It is
not: the coin cancels, and the surviving obligation is that a base-four sum of small
integers avoids the residues `{0,…,d−1}` modulo `2^d`. Equivalently `ρ_d < d` forces the top
`≈ d/2 − log₄ d` base-four digits of that sum to vanish simultaneously — an exact
cancellation across linearly many ranks, not a bounded-window coincidence. That is why the
depth-twelve local countermodel does not reach the statement.

This is a **reformulation with the exponential removed**, not a producer. It proves neither
the socket nor anything about Erdős 257.
-/

namespace ErdosProblems.Erdos257

namespace FourNinthsCoinCancellation

open Erdos257PeriodNoncollapse

/-- The base-four weight times the coin's power part is a single power of two. -/
theorem four_pow_mul_two_pow (k i b : ℕ) :
    4 ^ k * (b * 2 ^ i) = 2 ^ (2 * k + i) * b := by
  have h4 : (4 : ℕ) = 2 ^ 2 := by norm_num
  rw [h4, ← pow_mul]
  ring

/-- **Coin cancellation.** At base-four weight `4 ^ k` and coin power `2 ^ i`, the
contribution is divisible by `2 ^ (k + i)`.  Taking `k = d - i` this is divisibility by
`2 ^ d`: the exponentially large coin term drops out of `ρ_d` modulo `2 ^ d`. -/
theorem coinPart_dvd (k i b : ℕ) : (2 : ℕ) ^ (k + i) ∣ 4 ^ k * (b * 2 ^ i) := by
  rw [four_pow_mul_two_pow]
  exact Dvd.dvd.mul_right (pow_dvd_pow 2 (by omega)) b

/-- Terms of the surviving sum with `i ≤ d / 2` are themselves divisible by `2 ^ d`, so only
the last `⌈d/2⌉` ranks contribute modulo `2 ^ d`. Stated with `k = d - i` explicit: if the
weight exponent `k` is at least `i`, the whole term vanishes mod `2 ^ (k + i)`. -/
theorem lowRank_term_dvd (k i c : ℕ) (h : i ≤ k) : (2 : ℕ) ^ (k + i) ∣ 4 ^ k * c := by
  have h4 : (4 : ℕ) = 2 ^ 2 := by norm_num
  rw [h4, ← pow_mul]
  exact Dvd.dvd.mul_right (pow_dvd_pow 2 (by omega)) c

/-- A residue below the modulus is pinned by it: if `0 ≤ r < 2 ^ d` and `r ≡ S (mod 2 ^ d)`
then `r = S % 2 ^ d`.  This is why the congruence determines `ρ_d` exactly rather than only
constraining it. -/
theorem pinned_of_lt {r S d : ℕ} (hlt : r < 2 ^ d) (hcong : r % 2 ^ d = S % 2 ^ d) :
    r = S % 2 ^ d := by
  rw [← hcong, Nat.mod_eq_of_lt hlt]

/-! ## Connection to the executable four-ninths diagonal -/

/-- The signed part of the transition increment left after replacing a selected coin
`2^(d+1) + 1` by its unit part.  Unlike the original history increment, every summand
here is built only from the pulse, divisor load, and a zero-one selection bit. -/
noncomputable def fourNinthsDiagonalSmallIncrement (d : ℕ) : ℤ := by
  classical
  exact
    (fourNinthsPairPulse (d + 1) : ℤ) -
      (fourNinthsDiagonalLoad
        (fourNinthsDiagonalState d) (d + 1) : ℤ) -
      if FourNinthsDiagonalTakesAt d then 1 else 0

/-- The pure dyadic part of the selected coin at the transition from `d` to `d+1`. -/
noncomputable def fourNinthsDiagonalDyadicCharge (d : ℕ) : ℤ := by
  classical
  exact if FourNinthsDiagonalTakesAt d then (2 : ℤ) ^ (d + 1) else 0

/-- The exact executable history increment splits into a small signed increment and a
pure dyadic charge. -/
theorem fourNinthsDiagonalHistoryIncrement_eq_small_sub_dyadic (d : ℕ) :
    fourNinthsDiagonalHistoryIncrement d =
      fourNinthsDiagonalSmallIncrement d -
        fourNinthsDiagonalDyadicCharge d := by
  classical
  by_cases htake : FourNinthsDiagonalTakesAt d
  · simp [fourNinthsDiagonalHistoryIncrement,
      fourNinthsDiagonalHistoryCoinCharge,
      fourNinthsDiagonalSmallIncrement,
      fourNinthsDiagonalDyadicCharge, htake]
    ring
  · simp [fourNinthsDiagonalHistoryIncrement,
      fourNinthsDiagonalHistoryCoinCharge,
      fourNinthsDiagonalSmallIncrement,
      fourNinthsDiagonalDyadicCharge, htake]

/-- Base-four history respects subtraction pointwise. -/
theorem fourNinthsWeightedHistory_sub (f g : ℕ → ℤ) (d : ℕ) :
    fourNinthsWeightedHistory (fun j => f j - g j) d =
      fourNinthsWeightedHistory f d - fourNinthsWeightedHistory g d := by
  induction d with
  | zero => simp [fourNinthsWeightedHistory]
  | succ d ih =>
      rw [fourNinthsWeightedHistory, fourNinthsWeightedHistory,
        fourNinthsWeightedHistory, ih]
      ring

/-- The executable remainder is the small-integer history minus the accumulated dyadic
part of every selected coin. -/
theorem fourNinthsDiagonalState_rho_eq_smallHistory_sub_dyadicHistory (d : ℕ) :
    (fourNinthsDiagonalState d).rho =
      fourNinthsWeightedHistory fourNinthsDiagonalSmallIncrement d -
        fourNinthsWeightedHistory fourNinthsDiagonalDyadicCharge d := by
  rw [fourNinthsDiagonalState_rho_eq_weightedHistory]
  calc
    fourNinthsWeightedHistory fourNinthsDiagonalHistoryIncrement d =
        fourNinthsWeightedHistory
          (fun j => fourNinthsDiagonalSmallIncrement j -
            fourNinthsDiagonalDyadicCharge j) d := by
      apply congrArg (fun q : ℕ → ℤ => fourNinthsWeightedHistory q d)
      funext j
      exact fourNinthsDiagonalHistoryIncrement_eq_small_sub_dyadic j
    _ = fourNinthsWeightedHistory fourNinthsDiagonalSmallIncrement d -
          fourNinthsWeightedHistory fourNinthsDiagonalDyadicCharge d :=
      fourNinthsWeightedHistory_sub _ _ d

/-- Every accumulated dyadic coin contribution through depth `d` is divisible by `2^d`.
This is the executable version of coin cancellation, rather than a detached term lemma. -/
theorem fourNinthsDiagonalDyadicHistory_dvd (d : ℕ) :
    (2 : ℤ) ^ d ∣
      fourNinthsWeightedHistory fourNinthsDiagonalDyadicCharge d := by
  induction d with
  | zero => simp [fourNinthsWeightedHistory]
  | succ d ih =>
      obtain ⟨k, hk⟩ := ih
      classical
      by_cases htake : FourNinthsDiagonalTakesAt d
      · refine ⟨2 * k + 1, ?_⟩
        rw [fourNinthsWeightedHistory, hk, pow_succ]
        simp [fourNinthsDiagonalDyadicCharge, htake]
        ring
      · refine ⟨2 * k, ?_⟩
        rw [fourNinthsWeightedHistory, hk, pow_succ]
        simp [fourNinthsDiagonalDyadicCharge, htake]
        ring

/-- **Executable coin cancellation.**  The actual four-ninths diagonal remainder is
congruent modulo `2^d` to a base-four history containing only small signed increments. -/
theorem fourNinthsDiagonalState_rho_modEq_smallHistory (d : ℕ) :
    Int.ModEq ((2 : ℤ) ^ d)
      (fourNinthsDiagonalState d).rho
      (fourNinthsWeightedHistory fourNinthsDiagonalSmallIncrement d) := by
  rw [Int.modEq_iff_dvd,
    fourNinthsDiagonalState_rho_eq_smallHistory_sub_dyadicHistory]
  simpa using fourNinthsDiagonalDyadicHistory_dvd d

/-- Literal finite-sum form of executable coin cancellation.  This is the exact
small-integer residue asserted in the accompanying research packet. -/
theorem fourNinthsDiagonalState_rho_modEq_smallHistorySum (d : ℕ) :
    Int.ModEq ((2 : ℤ) ^ d)
      (fourNinthsDiagonalState d).rho
      (∑ j ∈ Finset.range d,
        (4 : ℤ) ^ (d - 1 - j) * fourNinthsDiagonalSmallIncrement j) := by
  simpa only [fourNinthsWeightedHistory_eq_sum] using
    fourNinthsDiagonalState_rho_modEq_smallHistory d

/-- A small-increment term from the first half of the history is already divisible by the
full modulus `2^d`.  This is the signed, executable counterpart of `lowRank_term_dvd`. -/
theorem fourNinthsLowRankSmallIncrementTerm_dvd
    {d j : ℕ} (hj : j < d / 2) :
    (2 : ℤ) ^ d ∣
      (4 : ℤ) ^ (d - 1 - j) * fourNinthsDiagonalSmallIncrement j := by
  have hexponent : d ≤ 2 * (d - 1 - j) := by omega
  rw [show (4 : ℤ) = 2 ^ 2 by norm_num, ← pow_mul]
  exact Dvd.dvd.mul_right (pow_dvd_pow 2 hexponent) _

/-- The complete low half of the executable small-integer history vanishes modulo `2^d`. -/
theorem fourNinthsLowRankSmallHistory_dvd (d : ℕ) :
    (2 : ℤ) ^ d ∣
      ∑ j ∈ Finset.range (d / 2),
        (4 : ℤ) ^ (d - 1 - j) * fourNinthsDiagonalSmallIncrement j := by
  apply Finset.dvd_sum
  intro j hj
  exact fourNinthsLowRankSmallIncrementTerm_dvd (Finset.mem_range.mp hj)

/-- **Half-window executable coin cancellation.**  Only ranks in the final half of the
actual pulse/load/decision history can affect the remainder modulo `2^d`. -/
theorem fourNinthsDiagonalState_rho_modEq_smallHistoryHalf (d : ℕ) :
    Int.ModEq ((2 : ℤ) ^ d)
      (fourNinthsDiagonalState d).rho
      (∑ j ∈ Finset.Ico (d / 2) d,
        (4 : ℤ) ^ (d - 1 - j) * fourNinthsDiagonalSmallIncrement j) := by
  let f : ℕ → ℤ := fun j =>
    (4 : ℤ) ^ (d - 1 - j) * fourNinthsDiagonalSmallIncrement j
  have hsplit :
      (∑ j ∈ Finset.range (d / 2), f j) +
          (∑ j ∈ Finset.Ico (d / 2) d, f j) =
        ∑ j ∈ Finset.range d, f j :=
    Finset.sum_range_add_sum_Ico f (Nat.div_le_self d 2)
  have hprefix : (2 : ℤ) ^ d ∣ ∑ j ∈ Finset.range (d / 2), f j := by
    simpa only [f] using fourNinthsLowRankSmallHistory_dvd d
  have hfullSuffix :
      Int.ModEq ((2 : ℤ) ^ d)
        (∑ j ∈ Finset.range d, f j)
        (∑ j ∈ Finset.Ico (d / 2) d, f j) := by
    rw [Int.modEq_iff_dvd]
    obtain ⟨k, hk⟩ := hprefix
    refine ⟨-k, ?_⟩
    rw [← hsplit, hk]
    ring
  exact (fourNinthsDiagonalState_rho_modEq_smallHistorySum d).trans
    (by simpa only [f] using hfullSuffix)

/-- Inside the canonical interval `[0,2^d)`, the half-window residue pins the executable
remainder exactly. -/
theorem fourNinthsDiagonalState_rho_eq_smallHistoryHalf_emod
    (d : ℕ)
    (hnonneg : 0 ≤ (fourNinthsDiagonalState d).rho)
    (hlt : (fourNinthsDiagonalState d).rho < (2 : ℤ) ^ d) :
    (fourNinthsDiagonalState d).rho =
      (∑ j ∈ Finset.Ico (d / 2) d,
        (4 : ℤ) ^ (d - 1 - j) * fourNinthsDiagonalSmallIncrement j) %
          (2 : ℤ) ^ d := by
  have hmod := fourNinthsDiagonalState_rho_modEq_smallHistoryHalf d
  rw [Int.ModEq] at hmod
  calc
    (fourNinthsDiagonalState d).rho =
        (fourNinthsDiagonalState d).rho % (2 : ℤ) ^ d :=
      (Int.emod_eq_of_lt hnonneg hlt).symm
    _ = _ := hmod

/-- A selected transition always lands nonnegatively; this uses only the literal take
comparison and does not assume the global selected-landing producer. -/
theorem fourNinthsDiagonalState_rho_succ_nonnegative_of_takes
    (d : ℕ) (htake : FourNinthsDiagonalTakesAt d) :
    0 ≤ (fourNinthsDiagonalState (d + 1)).rho := by
  rw [fourNinthsDiagonalState_rho_succ_of_takes d htake]
  exact sub_nonneg.mpr htake

/-- A selected transition from inside the dyadic strip lands strictly inside the next
strip.  Hence an upper-strip escape cannot be created by a selected row. -/
theorem fourNinthsDiagonalState_rho_succ_lt_twoPow_of_takes_of_prev_lt
    (d : ℕ) (htake : FourNinthsDiagonalTakesAt d)
    (hprev : (fourNinthsDiagonalState d).rho < (2 : ℤ) ^ d) :
    (fourNinthsDiagonalState (d + 1)).rho < (2 : ℤ) ^ (d + 1) := by
  have hpulse : (fourNinthsPairPulse (d + 1) : ℤ) ≤ 3 := by
    unfold fourNinthsPairPulse
    by_cases hzero : (d + 1) % 3 = 0
    · simp [hzero]
    · by_cases hone : (d + 1) % 3 = 1
      · simp [hzero, hone]
      · simp [hzero, hone]
  have hpowpos : 0 < (2 : ℤ) ^ d := by positivity
  rw [fourNinthsDiagonalState_rho_succ_of_takes d htake]
  push_cast
  rw [pow_succ]
  have hload :
      0 ≤ (fourNinthsDiagonalLoad
        (fourNinthsDiagonalState d) (d + 1) : ℤ) := by positivity
  omega

/-- A skipped transition is at most the next dyadic boundary. -/
theorem fourNinthsDiagonalState_rho_succ_le_twoPow_of_not_takes
    (d : ℕ) (hskip : ¬ FourNinthsDiagonalTakesAt d) :
    (fourNinthsDiagonalState (d + 1)).rho ≤ (2 : ℤ) ^ (d + 1) := by
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
  rw [fourNinthsDiagonalState]
  simp [fourNinthsDiagonalStep, fourNinthsDiagonalState_bits_length, hnotTake]
  omega

/-- **Exact upper-strip gateway.**  From a state strictly below `2^d`, a first failure of
the next strict strip bound must be a skipped row landing exactly on `2^(d+1)`. -/
theorem fourNinthsDiagonalState_first_upperExit_eq_skippedBoundary
    (d : ℕ)
    (hprev : (fourNinthsDiagonalState d).rho < (2 : ℤ) ^ d)
    (hexit : (2 : ℤ) ^ (d + 1) ≤
      (fourNinthsDiagonalState (d + 1)).rho) :
    ¬ FourNinthsDiagonalTakesAt d ∧
      (fourNinthsDiagonalState (d + 1)).rho = (2 : ℤ) ^ (d + 1) := by
  by_cases htake : FourNinthsDiagonalTakesAt d
  · have hlt :=
      fourNinthsDiagonalState_rho_succ_lt_twoPow_of_takes_of_prev_lt
        d htake hprev
    omega
  · refine ⟨htake, ?_⟩
    have hle := fourNinthsDiagonalState_rho_succ_le_twoPow_of_not_takes d htake
    omega

/-- While the predecessor is inside its dyadic strip, a selected landing is exactly the
Euclidean residue of the last half of the small pulse/load/decision history. -/
theorem fourNinthsDiagonalState_rho_succ_eq_smallHistoryHalf_emod_of_takes
    (d : ℕ) (htake : FourNinthsDiagonalTakesAt d)
    (hprev : (fourNinthsDiagonalState d).rho < (2 : ℤ) ^ d) :
    (fourNinthsDiagonalState (d + 1)).rho =
      (∑ j ∈ Finset.Ico ((d + 1) / 2) (d + 1),
        (4 : ℤ) ^ (d + 1 - 1 - j) * fourNinthsDiagonalSmallIncrement j) %
          (2 : ℤ) ^ (d + 1) := by
  apply fourNinthsDiagonalState_rho_eq_smallHistoryHalf_emod
  · exact fourNinthsDiagonalState_rho_succ_nonnegative_of_takes d htake
  · exact fourNinthsDiagonalState_rho_succ_lt_twoPow_of_takes_of_prev_lt
      d htake hprev

#print axioms four_pow_mul_two_pow
#print axioms coinPart_dvd
#print axioms lowRank_term_dvd
#print axioms pinned_of_lt
#print axioms fourNinthsDiagonalHistoryIncrement_eq_small_sub_dyadic
#print axioms fourNinthsWeightedHistory_sub
#print axioms fourNinthsDiagonalState_rho_eq_smallHistory_sub_dyadicHistory
#print axioms fourNinthsDiagonalDyadicHistory_dvd
#print axioms fourNinthsDiagonalState_rho_modEq_smallHistory
#print axioms fourNinthsDiagonalState_rho_modEq_smallHistorySum
#print axioms fourNinthsLowRankSmallIncrementTerm_dvd
#print axioms fourNinthsLowRankSmallHistory_dvd
#print axioms fourNinthsDiagonalState_rho_modEq_smallHistoryHalf
#print axioms fourNinthsDiagonalState_rho_eq_smallHistoryHalf_emod
#print axioms fourNinthsDiagonalState_rho_succ_nonnegative_of_takes
#print axioms fourNinthsDiagonalState_rho_succ_lt_twoPow_of_takes_of_prev_lt
#print axioms fourNinthsDiagonalState_rho_succ_le_twoPow_of_not_takes
#print axioms fourNinthsDiagonalState_first_upperExit_eq_skippedBoundary
#print axioms fourNinthsDiagonalState_rho_succ_eq_smallHistoryHalf_emod_of_takes

end FourNinthsCoinCancellation

end ErdosProblems.Erdos257
