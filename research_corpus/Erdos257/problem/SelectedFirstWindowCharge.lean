import ErdosProblems.Erdos257.SelectedAncestryBudget
import Erdos257PeriodNoncollapse.HalfCylinderFullShellSeamBridge

/-!
# Erdős #257: selected-ancestry budget / frozen-margin bridge

The selected-ancestry audit rediscovered the full first-window divisor charge
in budget coordinates.  The charge itself is not a new producer:
`HalfCylinderFiniteShadow` already formalizes it as the frozen full-shell
margin and identifies it with future-skip capacity minus the terminal carry.

This module supplies the missing source-current bridge.  At an actual skipped
rank `n`, the full-shell margin is exactly

`2^(2n) * B_n - Phi_(A_n)(2n)`.

Consequently the selected-ancestry tail-coverage condition below is exactly
the existing `HalfGreedySkippedFullShellNonnegative` producer.  The final
consumer therefore introduces no new hypothesis and does not claim to solve
Erdős #257.
-/

namespace ErdosProblems.Erdos257

open Set
open Erdos257PeriodNoncollapse
open Erdos257PeriodNoncollapse.HalfCarryReachability
open Erdos257PeriodNoncollapse.HalfCylinderFiniteShadow

/-- At a skipped rank the rational selected-ancestry budget is the dyadic
safety slack of the unchanged real greedy remainder. -/
theorem halfSelectedAncestryBudget_cast_eq_dyadic_sub_remainder_of_skip
    (n : ℕ) (hn : 1 ≤ n)
    (hskip : ¬ mersenneWeight n ≤
      greedyMersenneRemainder (1 / 2 : ℝ) (n - 1)) :
    (halfSelectedAncestryBudgetRat n : ℝ) =
      1 / (2 : ℝ) ^ n -
        greedyMersenneRemainder (1 / 2 : ℝ) (n - 1) := by
  have hremReal :
      greedyMersenneRemainder (1 / 2 : ℝ) n =
        greedyMersenneRemainder (1 / 2 : ℝ) (n - 1) := by
    obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : n ≠ 0)
    have hskip' : ¬ mersenneWeight (k + 1) ≤
        greedyMersenneRemainder (1 / 2 : ℝ) k := by
      simpa using hskip
    rw [greedyMersenneRemainder_succ, if_neg hskip']
    simp
  have hbudgetQ :=
    halfGreedyRemainderRat_eq_dyadic_sub_selectedAncestryBudget n
  have hbudgetR :
      ((greedyMersenneRemainderRat (1 / 2 : ℚ) n : ℚ) : ℝ) =
        ((halfDyadicWeightRat n -
          halfSelectedAncestryBudgetRat n : ℚ) : ℝ) := by
    exact_mod_cast hbudgetQ
  rw [cast_greedyMersenneRemainderRat] at hbudgetR
  simp only [halfDyadicWeightRat, Rat.cast_sub, Rat.cast_div,
    Rat.cast_one, Rat.cast_pow, Rat.cast_ofNat] at hbudgetR
  rw [hremReal] at hbudgetR
  linarith

/-- Exact integration seam: the old selected-divisor first-window charge is
the amplified selected-ancestry budget after paying the frozen coefficient
tail beyond row `2n`. -/
theorem greedyHalfFrozenMargin_fullShell_cast_eq_selectedBudget_sub_tail
    (n : ℕ) (hn : 1 ≤ n)
    (hskip : ¬ mersenneWeight n ≤
      greedyMersenneRemainder (1 / 2 : ℝ) (n - 1)) :
    (greedyHalfFrozenMargin (n - 1) n : ℝ) =
      (2 : ℝ) ^ (2 * n) *
          (halfSelectedAncestryBudgetRat n : ℝ) -
        binaryCoeffTail
          (supportCoeff
            (↑(halfGreedyPrefixSupport (n - 1)) : Set ℕ)) (2 * n) := by
  have hmargin :=
    greedyHalfFrozenMargin_fullShell_cast_eq_slack_sub_tail (n - 1)
  have hbudget :=
    halfSelectedAncestryBudget_cast_eq_dyadic_sub_remainder_of_skip
      n hn hskip
  have hpow : (2 : ℝ) ^ n ≠ 0 := by positivity
  have hslack :
      1 - (2 : ℝ) ^ n *
          greedyMersenneRemainder (1 / 2 : ℝ) (n - 1) =
        (2 : ℝ) ^ n * (halfSelectedAncestryBudgetRat n : ℝ) := by
    rw [hbudget]
    field_simp [hpow]
  rw [Nat.sub_add_cancel hn] at hmargin
  rw [hslack] at hmargin
  calc
    (greedyHalfFrozenMargin (n - 1) n : ℝ) =
        (2 : ℝ) ^ n *
            ((2 : ℝ) ^ n * (halfSelectedAncestryBudgetRat n : ℝ)) -
          binaryCoeffTail
            (supportCoeff
              (↑(halfGreedyPrefixSupport (n - 1)) : Set ℕ)) (n + n) :=
      hmargin
    _ = (2 : ℝ) ^ (2 * n) *
            (halfSelectedAncestryBudgetRat n : ℝ) -
          binaryCoeffTail
            (supportCoeff
              (↑(halfGreedyPrefixSupport (n - 1)) : Set ℕ)) (2 * n) := by
      rw [show 2 * n = n + n by omega, pow_add]
      ring

/-- The budget-coordinate full-shell condition.  This is deliberately named
as a coverage restatement, not as a second independent producer. -/
def HalfSelectedAncestryFullShellCoverage : Prop :=
  ∀ n : ℕ, 3 ≤ n →
    (¬ mersenneWeight n ≤
      greedyMersenneRemainder (1 / 2 : ℝ) (n - 1)) →
    binaryCoeffTail
        (supportCoeff
          (↑(halfGreedyPrefixSupport (n - 1)) : Set ℕ)) (2 * n) ≤
      (2 : ℝ) ^ (2 * n) *
        (halfSelectedAncestryBudgetRat n : ℝ)

/-- No producer is double-counted: selected-ancestry coverage is exactly the
existing skipped full-shell nonnegativity socket. -/
theorem halfSelectedAncestryFullShellCoverage_iff_skippedFullShellNonnegative :
    HalfSelectedAncestryFullShellCoverage ↔
      HalfGreedySkippedFullShellNonnegative := by
  constructor
  · intro hcoverage n hn hskip
    have hid :=
      greedyHalfFrozenMargin_fullShell_cast_eq_selectedBudget_sub_tail
        n (by omega) hskip
    have h := hcoverage n hn hskip
    have hcast : (0 : ℝ) ≤
        (greedyHalfFrozenMargin (n - 1) n : ℝ) := by
      rw [hid]
      linarith
    exact_mod_cast hcast
  · intro hsign n hn hskip
    have hid :=
      greedyHalfFrozenMargin_fullShell_cast_eq_selectedBudget_sub_tail
        n (by omega) hskip
    have hmargin := hsign n hn hskip
    have hcast : (0 : ℝ) ≤
        (greedyHalfFrozenMargin (n - 1) n : ℝ) := by
      exact_mod_cast hmargin
    rw [hid] at hcast
    linarith

/-- The selected-ancestry coverage restatement feeds the already-landed
full-shell consumer and hence closes exact half-membership. -/
theorem half_mem_mersenneAchievementSet_of_selectedAncestryFullShellCoverage
    (hcoverage : HalfSelectedAncestryFullShellCoverage) :
    (1 / 2 : ℝ) ∈ mersenneAchievementSet :=
  half_mem_mersenneAchievementSet_of_skippedFullShellNonnegative
    (halfSelectedAncestryFullShellCoverage_iff_skippedFullShellNonnegative.mp
      hcoverage)

/-! ## Logarithmic first-passage producer

The full-shell condition above waits `n` rows.  Exact replay suggests a much
more local statement: after a skipped rank `k + 1`, the frozen divisor charge
crosses the centered carry within twice the binary length of the rank.  This
is a strictly stronger quantitative producer, not a proved orbit fact.  The
point of naming it is to expose the finite arithmetic lemma whose proof would
close the problem without returning to the quadratically large rational
remainder denominator.
-/

/-- Quantitative selected-ancestry producer: at every actual half-greedy
skip, the frozen-margin recurrence reaches a nonnegative state in a
logarithmic window. -/
def HalfGreedyLogWindowFrozenMarginProducer : Prop :=
  ∀ k : ℕ,
    ¬ mersenneWeight (k + 1) ≤
        greedyMersenneRemainder (1 / 2 : ℝ) k →
      ∃ J : ℕ,
        J ≤ k + 1 ∧
        J ≤ 2 * (Nat.log2 (k + 1) + 1) ∧
        0 ≤ greedyHalfFrozenMargin k J

/-- Forgetting the logarithmic bound recovers the existing governed
first-passage producer. -/
theorem governedFrozenMarginProducer_of_logWindow
    (hlog : HalfGreedyLogWindowFrozenMarginProducer) :
    HalfGreedyGovernedFrozenMarginProducer := by
  intro k hskip
  obtain ⟨J, hJ, _, hmargin⟩ := hlog k hskip
  exact ⟨J, hJ, hmargin⟩

/-- The logarithmic selected-ancestry producer is sufficient for exact
`1/2` membership, and therefore for the rational counterexample route to
Erdős #257. -/
theorem half_mem_mersenneAchievementSet_of_logWindow
    (hlog : HalfGreedyLogWindowFrozenMarginProducer) :
    (1 / 2 : ℝ) ∈ mersenneAchievementSet :=
  half_mem_mersenneAchievementSet_of_governedFrozenMarginProducer
    (governedFrozenMarginProducer_of_logWindow hlog)

#print axioms halfSelectedAncestryBudget_cast_eq_dyadic_sub_remainder_of_skip
#print axioms greedyHalfFrozenMargin_fullShell_cast_eq_selectedBudget_sub_tail
#print axioms halfSelectedAncestryFullShellCoverage_iff_skippedFullShellNonnegative
#print axioms half_mem_mersenneAchievementSet_of_selectedAncestryFullShellCoverage
#print axioms governedFrozenMarginProducer_of_logWindow
#print axioms half_mem_mersenneAchievementSet_of_logWindow

end ErdosProblems.Erdos257
