import Erdos249257.DyadicPrefixCompression

/-!
# Dyadic safety on the initial unit-numerator segment

This module isolates a finite, exact part of the half-greedy analysis for the Mersenne weights
`1 / (2^k - 1)`.  The arithmetic observation is elementary: if a positive residual has
displayed numerator `1` and rank `k` is skipped, then the denominator lies beyond
`2^k - 1`; integrality leaves no point strictly between `2^k - 1` and `2^k`, so the
residual is at most the dyadic benchmark `2^{-k}`.

For the actual half-greedy prefix, direct rational evaluation shows that the displayed numerator
is `1` at every decision index `n ≤ 19`.  Combining the computation with the abstract
integer-gap lemma proves dyadic safety, in both excess and block coordinates, for every skipped
decision in that finite range.

## Scope

The result stops at `n = 19`.  It does not determine the next displayed numerator, prove that
rank `20` is selected, propagate any estimate after later selections, or establish dyadic safety
for the full orbit.  It therefore proves no representation of `1 / 2`, no unconditional
half-membership, and no solution of Erdős Problem #257.
-/

namespace Erdos249257

/-! ## A unit numerator leaves no unsafe dyadic gap -/

/-- If a residual with displayed numerator `1` skips rank `k`, then it satisfies the
corresponding dyadic block bound.  The proof is the absence of an integer strictly between
`2^k - 1` and `2^k`. -/
theorem blockDyadicSafeAt_of_unit_skip
    {D k : ℕ} (hskip : ¬ BlockTakeAt 1 D k) :
    BlockDyadicSafeAt 1 D k := by
  unfold BlockTakeAt BlockDyadicSafeAt at *
  have hlt : 2 ^ k - 1 < 2 * D := by
    simpa [not_le] using hskip
  have hpow : 1 ≤ 2 ^ k := Nat.one_le_pow _ _ (by omega)
  have : 2 ^ k ≤ 2 * D := by
    have := Nat.add_one_le_of_lt hlt
    rwa [Nat.sub_add_cancel hpow] at this
  simpa using this

/-- A real skip with displayed numerator `1` is the abstract unit block-skip condition. -/
theorem greedyHalf_unit_skip_blockTake
    (n : ℕ)
    (hp : halfGreedyResidualDisplayedNumerator n = 1)
    (hskip : ¬ mersenneWeight (n + 1) ≤
      greedyMersenneRemainder (1 / 2 : ℝ) n) :
    ¬ BlockTakeAt 1 (halfGreedyPrefixDenominator n) (n + 1) := by
  have habs :
      (halfGreedyResidualDisplayedNumerator n).natAbs = 1 := by
    simp [hp]
  have hiff := greedyHalf_take_iff_BlockTakeAt n
  rw [hiff, habs] at hskip
  exact hskip

/-- A skipped unit-numerator residual satisfies the dyadic block bound. -/
theorem greedyHalf_unit_skip_blockDyadicSafe
    (n : ℕ)
    (hp : halfGreedyResidualDisplayedNumerator n = 1)
    (hskip : ¬ mersenneWeight (n + 1) ≤
      greedyMersenneRemainder (1 / 2 : ℝ) n) :
    BlockDyadicSafeAt 1 (halfGreedyPrefixDenominator n) (n + 1) :=
  blockDyadicSafeAt_of_unit_skip
    (greedyHalf_unit_skip_blockTake n hp hskip)

/-- In excess coordinates, a skipped unit-numerator residual has nonpositive dyadic excess. -/
theorem halfGreedy_skip_dyadic_safe_of_unit_numerator
    (n : ℕ)
    (hp : halfGreedyResidualDisplayedNumerator n = 1)
    (hskip : ¬ mersenneWeight (n + 1) ≤
      greedyMersenneRemainder (1 / 2 : ℝ) n) :
    halfGreedyNextDyadicExcessNumerator n ≤ 0 := by
  have hsafe := greedyHalf_unit_skip_blockDyadicSafe n hp hskip
  have hpabs :
      (halfGreedyResidualDisplayedNumerator n).natAbs = 1 := by
    simp [hp]
  have hsafe' :
      BlockDyadicSafeAt
        (halfGreedyResidualDisplayedNumerator n).natAbs
        (halfGreedyPrefixDenominator n) (n + 1) := by
    simpa [hpabs] using hsafe
  exact (greedyHalfRemainder_le_nextDyadic_iff_excess_nonpos n).1
    (greedyHalfRemainder_le_nextDyadic_of_BlockSafe n hsafe')

/-! ## Exact certification through decision index nineteen -/

theorem halfGreedyPrefixRat_eq_half_sub_remainder (n : ℕ) :
    halfGreedyPrefixRat n =
      (1 / 2 : ℚ) - greedyMersenneRemainderRat (1 / 2 : ℚ) n := by
  unfold halfGreedyPrefixRat
  linarith [greedyMersenneRemainderRat_eq_sub_finiteErdosSum
    (1 / 2 : ℚ) n]

/-- The displayed residual numerator is exactly `1` at every decision index `n ≤ 19`. -/
theorem halfGreedyResidualDisplayedNumerator_eq_one_of_le_19
    (n : ℕ) (hn : n ≤ 19) :
    halfGreedyResidualDisplayedNumerator n = 1 := by
  rw [halfGreedyResidualDisplayedNumerator,
    halfGreedyPrefixDenominator,
    halfGreedyPrefixRat_eq_half_sub_remainder]
  interval_cases n <;>
    norm_num [greedyMersenneRemainderRat, mersenneWeightRat]

/-- Every actual skip at a decision index `n ≤ 19` has nonpositive dyadic excess. -/
theorem halfGreedy_skip_dyadic_safe_of_le_19
    (n : ℕ) (hn : n ≤ 19)
    (hskip : ¬ mersenneWeight (n + 1) ≤
      greedyMersenneRemainder (1 / 2 : ℝ) n) :
    halfGreedyNextDyadicExcessNumerator n ≤ 0 :=
  halfGreedy_skip_dyadic_safe_of_unit_numerator n
    (halfGreedyResidualDisplayedNumerator_eq_one_of_le_19 n hn) hskip

/-- Every actual skip at a decision index `n ≤ 19` satisfies the block-coordinate dyadic
bound used by the existing compression theorem. -/
theorem halfGreedy_actualBlockSafe_of_le_19
    (n : ℕ) (hn : n ≤ 19)
    (hskip : ¬ mersenneWeight (n + 1) ≤
      greedyMersenneRemainder (1 / 2 : ℝ) n) :
    BlockDyadicSafeAt
      (halfGreedyResidualDisplayedNumerator n).natAbs
      (halfGreedyPrefixDenominator n) (n + 1) := by
  have hp := halfGreedyResidualDisplayedNumerator_eq_one_of_le_19 n hn
  have hsafe := greedyHalf_unit_skip_blockDyadicSafe n hp hskip
  have habs :
      (halfGreedyResidualDisplayedNumerator n).natAbs = 1 := by
    simp [hp]
  simpa [habs] using hsafe

end Erdos249257
