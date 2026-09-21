import Erdos249257.TerminalOnlyScaledVanishing
import Erdos249257.HalfCylinderIntegerGreedy

/-!
# Positive-support terminal approximation endpoint for Erdős 257

This module keeps the `0 ∉ A` clause from short `res:terminalhalf` explicit.
It also records the exact index conversion between the paper's terminal carry
`K_A(M)` and the affine carry used by the scaled-vanishing producer.
-/

noncomputable section

namespace ErdosProblems.Erdos257.PaperCompleteR20

open Erdos249257
open Erdos249257.HalfCarryReachability

/-- The paper's terminal carry, with its sum reindexed from `j = 2, ..., M`
to `j = 0, ..., M - 2`. -/
def terminalPaperCarry (A : Set ℕ) (M : ℕ) : ℤ :=
  (2 : ℤ) ^ (M - 1) -
    ∑ j ∈ Finset.range (M - 1),
      (2 : ℤ) ^ (M - 2 - j) * (supportCoeff A (j + 2) : ℤ)

/-- The literal `K_A(M)` is the existing affine carry at index `M - 1`. -/
theorem terminalPaperCarry_eq_integerHalfCarry
    (A : Set ℕ) (M : ℕ) :
    terminalPaperCarry A M = integerHalfCarry A (M - 1) := by
  have hsub : M - 1 - 1 = M - 2 := by omega
  simpa only [terminalPaperCarry, hsub] using
    (HalfCylinderIntegerGreedy.integerHalfCarry_eq_pow_sub_sum A (M - 1)).symm

/-- Exact short `res:terminalhalf`: scaled terminal vanishing produces an
infinite support contained in the positive integers whose Mersenne subseries
has value exactly `1/2`. -/
theorem exists_infinite_positive_support_half_of_terminalScaledVanishing
    (S : HalfTerminalOnlyScaledVanishingSequence) :
    ∃ A : Set ℕ, 0 ∉ A ∧ A.Infinite ∧
      erdosSupportSeries 2 A = (1 : ℝ) / 2 := by
  rcases half_mem_mersenneAchievementSet_of_terminalScaledVanishing S with
    ⟨A, hA0, hvalue⟩
  have hseries : erdosSupportSeries 2 A = (1 : ℝ) / 2 := by
    rw [← positiveMersenneSupportValue_eq_erdosSupportSeries]
    exact hvalue.symm
  refine ⟨A, hA0, ?_, hseries⟩
  intro hfinite
  exact finite_boolSupport_ne_half A hfinite hA0 hseries

/-- Literal set-valued finite approximants from short `res:terminalhalf`. -/
theorem paper_terminalhalf
    (M : ℕ → ℕ) (A : ℕ → Set ℕ)
    (hM : ∀ j, 1 ≤ M j)
    (hlim : Filter.Tendsto M Filter.atTop Filter.atTop)
    (hA : ∀ j n, n ∈ A j → 2 ≤ n ∧ n ≤ M j)
    (herr : Filter.Tendsto
      (fun j ↦ |(terminalPaperCarry (A j) (M j) : ℝ)| / (2 : ℝ) ^ M j)
      Filter.atTop (nhds 0)) :
    ∃ B : Set ℕ, 0 ∉ B ∧ B.Infinite ∧
      erdosSupportSeries 2 B = (1 : ℝ) / 2 := by
  classical
  let w : ∀ j, HalfWord (M j) := fun j n ↦ decide (n.val ∈ A j)
  have hw : ∀ j, wordSupport (w j) = A j := by
    intro j
    ext n
    simp only [wordSupport, Set.mem_setOf_eq, w, decide_eq_true_eq]
    constructor
    · rintro ⟨_, hn⟩; exact hn
    · intro hn; exact ⟨by have := (hA j n hn).2; omega, hn⟩
  apply exists_infinite_positive_support_half_of_terminalScaledVanishing
  refine {
    depth := M
    word := w
    depth_pos := hM
    depth_tendsto := hlim
    zero := ?_
    one := ?_
    carry_scaled_tendsto := ?_ }
  · intro j
    simp only [w, decide_eq_false_iff_not]
    intro hn
    have := (hA j 0 hn).1
    omega
  · intro j hj
    simp only [w, decide_eq_false_iff_not]
    intro hn
    have := (hA j 1 hn).1
    omega
  · simpa only [hw, terminalPaperCarry_eq_integerHalfCarry] using herr

#print axioms paper_terminalhalf
#print axioms terminalPaperCarry_eq_integerHalfCarry
#print axioms exists_infinite_positive_support_half_of_terminalScaledVanishing

end ErdosProblems.Erdos257.PaperCompleteR20
