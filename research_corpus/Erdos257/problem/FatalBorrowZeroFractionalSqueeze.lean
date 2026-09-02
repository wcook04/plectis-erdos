import ErdosProblems.Erdos257.FatalBorrowCofiniteCarryTransfer
import Erdos257PeriodNoncollapse.HalfGreedyFatalGap

/-!
# Erdős #257: fatal zero rows squeeze the quotient phase

The reduced denominator of the half-greedy remainder is genuinely enormous,
so denominator separation is the wrong coordinate at a possible fatal row.
This module instead records the exact renormalised statement.

If rank `d` is skipped, but inserting it produces the exact midpoint quotient
at row `2d`, then the entire fractional phase is

`4^d * (mersenneWeight d - greedyRemainder (d - 1))`.

A nonpositive complement budget places the remainder beyond the complete
future tail.  The phase is therefore squeezed below the explicit tail gap
`4^d * (mersenneWeight d - mersenneTail d)`.  This is an ancestry/phase
obligation and contains no reduced-denominator estimate.
-/

namespace ErdosProblems.Erdos257

open Set
open Erdos257PeriodNoncollapse

noncomputable section

/-- Exact rational phase identity at a skipped midpoint-zero row. -/
theorem midpointZeroRow_localFractionMass_eq_scaled_skipGapRat
    {d : ℕ} (hd : 2 ≤ d)
    (hskip : ¬ mersenneWeight d ≤
      greedyMersenneRemainder (1 / 2 : ℝ) (d - 1))
    (hrow :
      localPrefixQuotient
          (insert d (halfGreedyPrefixSupport (d - 1))) (2 * d) =
        2 ^ (2 * d - 1)) :
    localFractionMass
        (insert d (halfGreedyPrefixSupport (d - 1))) (2 * d) =
      (2 : ℚ) ^ (2 * d) *
        (mersenneWeightRat d -
          greedyMersenneRemainderRat (1 / 2 : ℚ) (d - 1)) := by
  let P := halfGreedyPrefixSupport (d - 1)
  have hP := halfGreedyPrefixSupport_pred_below d hd
  have hdnot : d ∉ P := by
    intro hmem
    exact (Nat.lt_irrefl d) (hP d hmem).2
  have hD : ∀ e ∈ insert d P, 2 ≤ e := by
    intro e he
    rw [Finset.mem_insert] at he
    rcases he with rfl | he
    · exact hd
    · exact (hP e he).1
  have hpref :
      localMersennePrefixValue P =
        (1 / 2 : ℚ) -
          greedyMersenneRemainderRat (1 / 2 : ℚ) (d - 1) := by
    have hrem := greedyMersenneRemainderRat_eq_sub_finiteErdosSum
      (1 / 2 : ℚ) (d - 1)
    change greedyMersenneRemainderRat (1 / 2 : ℚ) (d - 1) =
      (1 / 2 : ℚ) - localMersennePrefixValue P at hrem
    linarith
  have hinsert :
      localMersennePrefixValue (insert d P) =
        localMersennePrefixValue P + mersenneWeightRat d := by
    unfold localMersennePrefixValue
    rw [Finset.sum_insert hdnot]
    ring
  have hscale := scaled_localMersennePrefixValue
    (D := insert d P) (M := 2 * d) hD
  rw [hrow] at hscale
  rw [hinsert, hpref] at hscale
  have htwo : (2 : ℚ) ^ (2 * d) =
      2 * ((2 ^ (2 * d - 1) : ℕ) : ℚ) := by
    rw [show 2 * d = (2 * d - 1) + 1 by omega, pow_succ']
    norm_num
  have hmid : ((2 ^ (2 * d - 1) : ℕ) : ℚ) =
      (2 : ℚ) ^ (2 * d) / 2 := by linarith
  rw [hmid] at hscale
  linarith

/-- The rational identity transported to the real quotient-phase coordinate. -/
theorem midpointZeroRow_localFractionMass_cast_eq_scaled_skipGap
    {d : ℕ} (hd : 2 ≤ d)
    (hskip : ¬ mersenneWeight d ≤
      greedyMersenneRemainder (1 / 2 : ℝ) (d - 1))
    (hrow :
      localPrefixQuotient
          (insert d (halfGreedyPrefixSupport (d - 1))) (2 * d) =
        2 ^ (2 * d - 1)) :
    ((localFractionMass
        (insert d (halfGreedyPrefixSupport (d - 1))) (2 * d) : ℚ) : ℝ) =
      (2 : ℝ) ^ (2 * d) *
        (mersenneWeight d -
          greedyMersenneRemainder (1 / 2 : ℝ) (d - 1)) := by
  have h := midpointZeroRow_localFractionMass_eq_scaled_skipGapRat
    hd hskip hrow
  have hcast := congrArg (fun q : ℚ ↦ (q : ℝ)) h
  push_cast at hcast
  simpa [cast_mersenneWeightRat, cast_greedyMersenneRemainderRat] using hcast

/-- Fatality squeezes the midpoint-zero phase below the complete-tail gap. -/
theorem nonpositiveComplementBudget_midpointZeroRow_fractionalSqueeze
    {d : ℕ} (hd : 2 ≤ d)
    (hskip : ¬ mersenneWeight d ≤
      greedyMersenneRemainder (1 / 2 : ℝ) (d - 1))
    (hfatal : halfSelectedAncestryComplementBudget d ≤ 0)
    (hrow :
      localPrefixQuotient
          (insert d (halfGreedyPrefixSupport (d - 1))) (2 * d) =
        2 ^ (2 * d - 1)) :
    ((localFractionMass
        (insert d (halfGreedyPrefixSupport (d - 1))) (2 * d) : ℚ) : ℝ) ≤
      (2 : ℝ) ^ (2 * d) *
        (mersenneWeight d - mersenneTail d) := by
  have hphase := midpointZeroRow_localFractionMass_cast_eq_scaled_skipGap
    hd hskip hrow
  have hremEq : greedyMersenneRemainder (1 / 2 : ℝ) d =
      greedyMersenneRemainder (1 / 2 : ℝ) (d - 1) := by
    have hskip' : ¬ mersenneWeight ((d - 1) + 1) ≤
        greedyMersenneRemainder (1 / 2 : ℝ) (d - 1) := by
      simpa [Nat.sub_add_cancel (by omega : 1 ≤ d)] using hskip
    have hs := greedyMersenneRemainder_succ (1 / 2 : ℝ) (d - 1)
    rw [if_neg hskip'] at hs
    simpa [Nat.sub_add_cancel (by omega : 1 ≤ d)] using hs
  have htail : mersenneTail d ≤
      greedyMersenneRemainder (1 / 2 : ℝ) (d - 1) := by
    rw [halfSelectedAncestryComplementBudget_eq_tail_sub_remainder,
      hremEq] at hfatal
    linarith
  rw [hphase]
  have hpow : 0 ≤ (2 : ℝ) ^ (2 * d) := by positivity
  exact mul_le_mul_of_nonneg_left (sub_le_sub_left htail _) hpow

/-- The same squeeze with the explicit three-channel lower approximation to
the tail.  This exposes the asymptotic `2/3` cell without denominator growth. -/
theorem nonpositiveComplementBudget_midpointZeroRow_fractionalSqueezeLB3
    {d : ℕ} (hd : 2 ≤ d)
    (hskip : ¬ mersenneWeight d ≤
      greedyMersenneRemainder (1 / 2 : ℝ) (d - 1))
    (hfatal : halfSelectedAncestryComplementBudget d ≤ 0)
    (hrow :
      localPrefixQuotient
          (insert d (halfGreedyPrefixSupport (d - 1))) (2 * d) =
        2 ^ (2 * d - 1)) :
    ((localFractionMass
        (insert d (halfGreedyPrefixSupport (d - 1))) (2 * d) : ℚ) : ℝ) <
      (2 : ℝ) ^ (2 * d) *
        (mersenneWeight d -
          HalfGreedyFatalGap.mersenneTailLB3 d) := by
  have hsqueeze :=
    nonpositiveComplementBudget_midpointZeroRow_fractionalSqueeze
      hd hskip hfatal hrow
  have htail := HalfGreedyFatalGap.mersenneTailLB3_lt_mersenneTail d
  have hpow : 0 < (2 : ℝ) ^ (2 * d) := by positivity
  exact hsqueeze.trans_lt
    (mul_lt_mul_of_pos_left (sub_lt_sub_left htail _) hpow)

/-- The explicit three-channel squeeze is already strictly below one.  In
the coordinate `t = 2^d`, the left side is
`t/(t-1) - 1/3 - 1/(7t)`; its excess above `1` is at most
`1/3 - 1/3 - 1/(7t)`. -/
theorem scaled_mersenneWeight_sub_tailLB3_lt_one
    {d : ℕ} (hd : 2 ≤ d) :
    (2 : ℝ) ^ (2 * d) *
        (mersenneWeight d - HalfGreedyFatalGap.mersenneTailLB3 d) < 1 := by
  set t : ℝ := 2 ^ d with ht
  have ht4 : (4 : ℝ) ≤ t := by
    calc
      (4 : ℝ) = (2 : ℝ) ^ 2 := by norm_num
      _ ≤ (2 : ℝ) ^ d := pow_le_pow_right₀ (by norm_num) hd
      _ = t := ht.symm
  have ht0 : 0 < t := by linarith
  have ht1 : 0 < t - 1 := by linarith
  have hform :
      (2 : ℝ) ^ (2 * d) *
          (mersenneWeight d - HalfGreedyFatalGap.mersenneTailLB3 d) =
        t / (t - 1) - 1 / 3 - 1 / (7 * t) := by
    have hsq : (2 : ℝ) ^ (2 * d) = t ^ 2 := by
      rw [show 2 * d = d * 2 by omega, pow_mul, ht]
    rw [hsq]
    unfold mersenneWeight HalfGreedyFatalGap.mersenneTailLB3
    rw [show (2 : ℝ) ^ d = t by exact ht.symm]
    field_simp
    ring
  have hthird : 1 / (t - 1) ≤ (1 / 3 : ℝ) := by
    rw [div_le_div_iff₀ ht1 (by norm_num : (0 : ℝ) < 3)]
    linarith
  have hdecomp : t / (t - 1) = 1 + 1 / (t - 1) := by
    field_simp
    ring
  rw [hform, hdecomp]
  have hlast : 0 < 1 / (7 * t) := by positivity
  linarith

/-- A fatal midpoint-zero row must lie in the open unit fractional cell.
This is the denominator-free obstruction to be contradicted by moving
selected-support ancestry. -/
theorem nonpositiveComplementBudget_midpointZeroRow_fractionalMass_lt_one
    {d : ℕ} (hd : 2 ≤ d)
    (hskip : ¬ mersenneWeight d ≤
      greedyMersenneRemainder (1 / 2 : ℝ) (d - 1))
    (hfatal : halfSelectedAncestryComplementBudget d ≤ 0)
    (hrow :
      localPrefixQuotient
          (insert d (halfGreedyPrefixSupport (d - 1))) (2 * d) =
        2 ^ (2 * d - 1)) :
    ((localFractionMass
        (insert d (halfGreedyPrefixSupport (d - 1))) (2 * d) : ℚ) : ℝ) < 1 := by
  exact
    (nonpositiveComplementBudget_midpointZeroRow_fractionalSqueezeLB3
      hd hskip hfatal hrow).trans
        (scaled_mersenneWeight_sub_tailLB3_lt_one hd)

#print axioms midpointZeroRow_localFractionMass_eq_scaled_skipGapRat
#print axioms midpointZeroRow_localFractionMass_cast_eq_scaled_skipGap
#print axioms nonpositiveComplementBudget_midpointZeroRow_fractionalSqueeze
#print axioms nonpositiveComplementBudget_midpointZeroRow_fractionalSqueezeLB3
#print axioms scaled_mersenneWeight_sub_tailLB3_lt_one
#print axioms nonpositiveComplementBudget_midpointZeroRow_fractionalMass_lt_one

end

end ErdosProblems.Erdos257
