import Erdos257PeriodNoncollapse.BooleanMobiusSkipRow
import Erdos257PeriodNoncollapse.HalfCylinderFullShellSeamBridge

/-!
# Cofinal exact rows from cofinal positive greedy skips

The skipped-core constructor is local: one positive rational-greedy skip at
rank `c` produces an exact quotient row at `2c-2`.  This module records the
corresponding cofinal fan-in.  It intentionally leaves visible the only
missing global input: positive skipped ranks must occur cofinally (or the
greedy remainder must already vanish, which gives half-membership directly).
-/

namespace Erdos257PeriodNoncollapse

open Set

/-- Positive skipped ranks of the rational half-greedy support occur
arbitrarily far out.  Positivity separates the skipped-core construction
from the already-terminal case in which a finite greedy prefix equals one
half exactly. -/
def CofinalPositiveHalfGreedySkips : Prop :=
  ∀ N : ℕ, ∃ c : ℕ,
    max N 4 ≤ c ∧
      0 < greedyMersenneRemainderRat (1 / 2 : ℚ) (c - 1) ∧
      greedyMersenneRemainderRat (1 / 2 : ℚ) (c - 1) <
        mersenneWeightRat c

/-- Every finite rational half-greedy residual is strictly positive.  Weak
nonnegativity comes from greedy subtraction; equality would make one half a
finite positive Mersenne sum, contradicting the odd-denominator theorem. -/
theorem greedyMersenneRemainderRat_half_pos (n : ℕ) :
    0 < greedyMersenneRemainderRat (1 / 2 : ℚ) n := by
  have hnonneg := greedyMersenneRemainderRat_nonneg_of_nonneg
    (x := (1 / 2 : ℚ)) (by norm_num) n
  apply lt_of_le_of_ne hnonneg
  intro hzero
  have hrem := greedyMersenneRemainderRat_eq_sub_finiteErdosSum
    (1 / 2 : ℚ) n
  rw [hzero] at hrem
  have hsum :
      finiteErdosSum (greedyMersennePrefixRat (1 / 2 : ℚ) n) 2 =
        (1 / 2 : ℚ) := by
    linarith
  have hodd := finiteErdosSum_den_odd
    (greedyMersennePrefixRat (1 / 2 : ℚ) n)
    (zero_not_mem_greedyMersennePrefixRat (1 / 2 : ℚ) n)
  rw [hsum] at hodd
  obtain ⟨k, hk⟩ := hodd
  norm_num at hk
  omega

/-- One positive rational-greedy skip supplies an actual exact local
Mersenne half row. -/
theorem exactLocalMersenneHalfRow_of_positiveHalfGreedySkip
    {c : ℕ} (hc : 4 ≤ c)
    (hpos : 0 < greedyMersenneRemainderRat (1 / 2 : ℚ) (c - 1))
    (hskip : greedyMersenneRemainderRat (1 / 2 : ℚ) (c - 1) <
      mersenneWeightRat c) :
    ExactLocalMersenneHalfRow (2 * c - 2) := by
  let D := halfGreedyPrefixSupport (c - 1)
  have hD : ∀ d ∈ D, 2 ≤ d ∧ d < c := by
    simpa [D] using halfGreedyPrefixSupport_pred_below c (by omega)
  have hrem :
      greedyMersenneRemainderRat (1 / 2 : ℚ) (c - 1) =
        (1 / 2 : ℚ) - localMersennePrefixValue D := by
    rw [localMersennePrefixValue_eq_finiteErdosSum]
    simpa [D, halfGreedyPrefixSupport] using
      (greedyMersenneRemainderRat_eq_sub_finiteErdosSum
        (1 / 2 : ℚ) (c - 1))
  have hbelow : localMersennePrefixValue D < (1 / 2 : ℚ) := by
    rw [hrem] at hpos
    linarith
  have hskip' :
      (1 / 2 : ℚ) - localMersennePrefixValue D < mersenneWeightRat c := by
    rw [← hrem]
    exact hskip
  exact exactLocalMersenneHalfRow_two_mul_sub_two_of_skippedCore
    hc hD hbelow hskip'

/-- Cofinal positive rational-greedy skips yield cofinal exact quotient
rows.  The row endpoints `2c-2` are automatically cofinal with the skipped
ranks `c`. -/
theorem cofinalExactLocalMersenneHalfRows_of_positiveHalfGreedySkips
    (hskips : CofinalPositiveHalfGreedySkips) :
    CofinalExactLocalMersenneHalfRows := by
  intro N
  obtain ⟨c, hcN, hpos, hskip⟩ := hskips N
  have hc : 4 ≤ c := (le_max_right N 4).trans hcN
  refine ⟨2 * c - 2, ?_,
    exactLocalMersenneHalfRow_of_positiveHalfGreedySkip hc hpos hskip⟩
  have hNc : N ≤ c := (le_max_left N 4).trans hcN
  omega

/-- The new exact-row route reaches the closed Mersenne achievement set as
soon as the positive-skip supply is cofinal. -/
theorem half_mem_mersenneAchievementSet_of_positiveHalfGreedySkips
    (hskips : CofinalPositiveHalfGreedySkips) :
    (1 / 2 : ℝ) ∈ mersenneAchievementSet := by
  exact half_mem_mersenneAchievementSet_of_cofinalExactLocalRows
    (cofinalExactLocalMersenneHalfRows_of_positiveHalfGreedySkips hskips)

/-- **Exact obstruction for the cofinal skipped-core route.**  The proposed
cofinal positive-skip supply is not a weaker producer than half-membership:
it is equivalent to the endpoint itself.  The reverse implication uses the
general rational cofinal-skip characterization; strict positivity contributes
no extra escape hatch because finite half-greedy residuals never vanish.

This theorem does not prove either side and does not decide Erdős #257. -/
theorem cofinalPositiveHalfGreedySkips_iff_half_mem :
    CofinalPositiveHalfGreedySkips ↔
      (1 / 2 : ℝ) ∈ mersenneAchievementSet := by
  constructor
  · exact half_mem_mersenneAchievementSet_of_positiveHalfGreedySkips
  · intro hhalf N
    have hhalf' :
        ((((1 : ℚ) / 2 : ℚ) : ℝ)) ∈ mersenneAchievementSet := by
      simpa using hhalf
    have hcofinal :=
      (rat_mem_mersenneAchievementSet_iff_cofinal_greedy_skips
        ((1 : ℚ) / 2) (by norm_num)).mp hhalf'
    obtain ⟨n, hn, hskipReal⟩ := hcofinal (max N 4)
    have hskipRat :
        ¬ mersenneWeightRat (n + 1) ≤
          greedyMersenneRemainderRat (1 / 2 : ℚ) n := by
      intro htakeRat
      exact hskipReal
        ((rational_greedy_take_iff_real ((1 : ℚ) / 2) n).mp htakeRat)
    refine ⟨n + 1, by omega, ?_, ?_⟩
    · simpa using greedyMersenneRemainderRat_half_pos n
    · simpa using (lt_of_not_ge hskipRat)

end Erdos257PeriodNoncollapse
