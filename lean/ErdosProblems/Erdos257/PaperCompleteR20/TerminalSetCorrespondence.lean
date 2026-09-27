import Erdos249257.TerminalOnlyScaledVanishing
import Erdos249257.HalfCylinderIntegerGreedy

/-!
# Positive-support terminal approximation endpoint for Erdős 257

This module keeps the `0 ∉ A` clause from short `res:terminalhalf` explicit.
It also records the exact index conversion between the paper's terminal carry
`K_A(M)` and the affine carry used by the scaled-vanishing producer.

The converse holds with no further hypothesis: a support with series value `1/2`
omits the exponent `1`, and the terminal carry of its prefix through `M` is the
scaled coefficient tail of the full support, which lies in `[0, 2√M + 4]`.
`paper_terminalhalf_iff` states the paper's equivalence as one theorem.
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

/-! ## Converse and equivalence -/

/-- A support whose Mersenne series has value `1/2` omits the exponent `1`:
the `n = 1` term alone is `1/(2^1 - 1) = 1`, and every term is nonnegative. -/
theorem one_notMem_of_erdosSupportSeries_two_eq_half {B : Set ℕ}
    (hvalue : erdosSupportSeries 2 B = (1 : ℝ) / 2) : 1 ∉ B := by
  intro h1
  have hs := summable_erdosSupport_indicator 2 B le_rfl
  have hle : Set.indicator B (fun a : ℕ => (1 : ℝ) / (((2 : ℕ) : ℝ) ^ a - 1)) 1 ≤
      erdosSupportSeries 2 B := by
    refine hs.le_tsum 1 (fun j _ => ?_)
    refine Set.indicator_nonneg (fun a _ => ?_) j
    have hpow : (1 : ℝ) ≤ ((2 : ℕ) : ℝ) ^ a := one_le_pow₀ (by norm_num)
    exact div_nonneg zero_le_one (by linarith)
  have hterm :
      Set.indicator B (fun a : ℕ => (1 : ℝ) / (((2 : ℕ) : ℝ) ^ a - 1)) 1 = 1 := by
    rw [Set.indicator_of_mem h1]
    norm_num
  linarith

/-- Converse identity of short `res:terminalhalf`.  For a support `A` with
`1 ∉ A` and series value `1/2`, the terminal carry of its prefix through `M`
is the scaled coefficient tail of the full support,
`K_{A_M}(M) = ∑_{r ≥ 1} c_A(M + r) 2^{-r}`.  Truncation does not change the
coefficients through `M`. -/
theorem terminalPaperCarry_inter_Iic_eq_binaryCoeffTail
    (A : Set ℕ) (hone : 1 ∉ A) (hvalue : erdosSupportSeries 2 A = (1 : ℝ) / 2)
    (M : ℕ) (hM : 1 ≤ M) :
    (terminalPaperCarry (A ∩ Set.Iic M) M : ℝ) =
      binaryCoeffTail (supportCoeff A) M := by
  rw [terminalPaperCarry_eq_integerHalfCarry,
    integerHalfCarry_inter_Iic_eq_of_succ_le A M (M - 1) (by omega),
    integerHalfCarry_eq_scaled_residual_add_tail A hone (M - 1), hvalue, sub_self,
    mul_zero, zero_add, Nat.sub_add_cancel hM]

/-- The converse bound of short `res:terminalhalf`:
`0 ≤ K_{A_M}(M) ≤ 2√M + 4` for every depth `M ≥ 1`. -/
theorem terminalPaperCarry_inter_Iic_bounds
    (A : Set ℕ) (hone : 1 ∉ A) (hvalue : erdosSupportSeries 2 A = (1 : ℝ) / 2)
    (M : ℕ) (hM : 1 ≤ M) :
    0 ≤ (terminalPaperCarry (A ∩ Set.Iic M) M : ℝ) ∧
      (terminalPaperCarry (A ∩ Set.Iic M) M : ℝ) ≤ 2 * Real.sqrt (M : ℝ) + 4 := by
  rw [terminalPaperCarry_inter_Iic_eq_binaryCoeffTail A hone hvalue M hM]
  exact ⟨binaryCoeffTail_nonneg (supportCoeff A) M,
    binaryCoeffTail_supportCoeff_le_two_sqrt_add_four A M⟩

/-- Converse of short `res:terminalhalf` with explicit approximants.  For every
support `B` with `0 ∉ B` and series value `1/2`, the depths `M_j = j + 1` and
the prefixes `A_j = B ∩ {0, …, j + 1}` (which lie in `{2, …, j + 1}`) satisfy
all four hypotheses of `paper_terminalhalf`.  Infinitude of `B` is not used. -/
theorem paper_terminalhalf_converse
    (B : Set ℕ) (hzero : 0 ∉ B) (hvalue : erdosSupportSeries 2 B = (1 : ℝ) / 2) :
    (∀ j : ℕ, 1 ≤ j + 1) ∧
      Filter.Tendsto (fun j : ℕ ↦ j + 1) Filter.atTop Filter.atTop ∧
      (∀ j n : ℕ, n ∈ B ∩ Set.Iic (j + 1) → 2 ≤ n ∧ n ≤ j + 1) ∧
      Filter.Tendsto
        (fun j : ℕ ↦
          |(terminalPaperCarry (B ∩ Set.Iic (j + 1)) (j + 1) : ℝ)| /
            (2 : ℝ) ^ (j + 1))
        Filter.atTop (nhds 0) := by
  have hone : 1 ∉ B := one_notMem_of_erdosSupportSeries_two_eq_half hvalue
  refine ⟨fun j ↦ by omega, Filter.tendsto_add_atTop_nat 1, ?_, ?_⟩
  · rintro j n ⟨hnB, hnle⟩
    have hn0 : n ≠ 0 := by
      rintro rfl
      exact hzero hnB
    have hn1 : n ≠ 1 := by
      rintro rfl
      exact hone hnB
    exact ⟨by omega, Set.mem_Iic.mp hnle⟩
  · have htail :=
      tendsto_two_sqrt_add_four_div_pow_zero.comp (Filter.tendsto_add_atTop_nat 1)
    apply squeeze_zero'
      (Filter.Eventually.of_forall fun j ↦ by positivity)
      (Filter.Eventually.of_forall fun j ↦ ?_)
      htail
    have hb := terminalPaperCarry_inter_Iic_bounds B hone hvalue (j + 1) (by omega)
    have habs : |(terminalPaperCarry (B ∩ Set.Iic (j + 1)) (j + 1) : ℝ)| ≤
        2 * Real.sqrt ((j + 1 : ℕ) : ℝ) + 4 := by
      rw [abs_of_nonneg hb.1]
      exact hb.2
    exact div_le_div_of_nonneg_right habs (by positivity)

/-- Short `res:terminalhalf` as an equivalence.  An infinite support of positive
integers with Mersenne series value `1/2` exists exactly when there are depths
`M_j ≥ 1` tending to infinity and sets `A_j ⊆ {2, …, M_j}` whose terminal
carries satisfy `|K_{A_j}(M_j)| / 2^{M_j} → 0`.  The right-to-left direction is
`paper_terminalhalf`; the left-to-right direction is
`paper_terminalhalf_converse`. -/
theorem paper_terminalhalf_iff :
    (∃ B : Set ℕ, 0 ∉ B ∧ B.Infinite ∧ erdosSupportSeries 2 B = (1 : ℝ) / 2) ↔
      ∃ (M : ℕ → ℕ) (A : ℕ → Set ℕ),
        (∀ j, 1 ≤ M j) ∧
          Filter.Tendsto M Filter.atTop Filter.atTop ∧
          (∀ j n, n ∈ A j → 2 ≤ n ∧ n ≤ M j) ∧
          Filter.Tendsto
            (fun j ↦ |(terminalPaperCarry (A j) (M j) : ℝ)| / (2 : ℝ) ^ M j)
            Filter.atTop (nhds 0) := by
  constructor
  · rintro ⟨B, hzero, -, hvalue⟩
    exact ⟨fun j ↦ j + 1, fun j ↦ B ∩ Set.Iic (j + 1),
      paper_terminalhalf_converse B hzero hvalue⟩
  · rintro ⟨M, A, hM, hlim, hA, herr⟩
    exact paper_terminalhalf M A hM hlim hA herr

#print axioms paper_terminalhalf
#print axioms terminalPaperCarry_eq_integerHalfCarry
#print axioms exists_infinite_positive_support_half_of_terminalScaledVanishing
#print axioms one_notMem_of_erdosSupportSeries_two_eq_half
#print axioms terminalPaperCarry_inter_Iic_eq_binaryCoeffTail
#print axioms terminalPaperCarry_inter_Iic_bounds
#print axioms paper_terminalhalf_converse
#print axioms paper_terminalhalf_iff

end ErdosProblems.Erdos257.PaperCompleteR20
