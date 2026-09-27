import ErdosProblems.Erdos257.PaperCompleteR8.CountableGaugeBudget
import ErdosProblems.Erdos257.PaperCompleteR8.CoverPotentialBounds
import Mathlib

/-!
# Genuine positive-weight padding and the finite-frame infimum limit

Every natural-number index has strictly positive weight. Dummy frames are
empty; their coefficients, not their weights, vanish. The infimum upper
bound is a limit of admissible costs, not a claim of attainment.
-/
noncomputable section
namespace ErdosProblems.Erdos257.PaperCompleteR8
open Filter Finset
open ErdosProblems.Erdos257.PaperCompleteR7

/-- One genuine frame, with the remaining probability spread over empty frames. -/
def paddedWeight (ε : ℝ) : ℕ → ℝ
  | 0 => 1 - ε
  | j + 1 => coverThreshold ε j

@[simp] theorem paddedWeight_zero (ε : ℝ) : paddedWeight ε 0 = 1 - ε := rfl
@[simp] theorem paddedWeight_succ (ε : ℝ) (j : ℕ) :
    paddedWeight ε (j + 1) = coverThreshold ε j := rfl

theorem paddedWeight_positive {ε : ℝ} (hε : 0 < ε) (hε1 : ε < 1) :
    ∀ j, 0 < paddedWeight ε j
  | 0 => sub_pos.mpr hε1
  | j + 1 => coverThreshold_pos hε j

theorem paddedWeight_hasSum (ε : ℝ) : HasSum (paddedWeight ε) 1 := by
  have htail : HasSum (fun j => paddedWeight ε (j + 1)) ε := by
    simpa only [paddedWeight_succ, tsum_coverThreshold] using
      (summable_coverThreshold ε).hasSum
  have h := htail.zero_add
  simpa only [paddedWeight_zero, sub_add_cancel] using h

/-- A summable sequence supported on its zeroth term. -/
theorem summable_zero_supported (f : ℕ → ℝ) (hf : ∀ j, f (j + 1) = 0) :
    Summable f := by
  apply (summable_nat_add_iff 1).mp
  have he : (fun j => f (j + 1)) = fun _ => (0 : ℝ) := funext hf
  rw [he]
  exact summable_zero

theorem tsum_zero_supported (f : ℕ → ℝ) (hf : ∀ j, f (j + 1) = 0) :
    (∑' j, f j) = f 0 := by
  have hs := summable_zero_supported f hf
  rw [hs.tsum_eq_zero_add]
  simp only [hf, tsum_zero, add_zero]

/-- Literal finite-frame data, before the countable positive padding. -/
structure FiniteCoverFrame where
  support : Finset ℕ
  exponent : ℝ
  coefficient : ℕ → ℝ
  positive : 0 ∉ support
  exponent_pos : 0 < exponent
  exponent_le_one : exponent ≤ 1
  coefficient_nonneg : ∀ d, 0 < d → 0 ≤ coefficient d
  column_summable : Summable (fun d : ℕ => coefficient d / (d : ℝ))
  majorises : ∀ n, 0 < n →
    ((support.filter (fun a => a ∣ n)).card : ℝ) ^ exponent ≤
      ∑ d ∈ n.divisors, coefficient d

def FiniteCoverFrame.cost (F : FiniteCoverFrame) : ℝ :=
  ∑' d : ℕ, F.coefficient d / (d : ℝ)

def FiniteCoverFrame.scalarCost (F : FiniteCoverFrame) : ℝ :=
  F.cost / ((2 : ℝ) ^ F.exponent - 1)

theorem FiniteCoverFrame.cost_nonneg (F : FiniteCoverFrame) : 0 ≤ F.cost := by
  apply tsum_nonneg
  intro d
  by_cases hd : d = 0
  · simp [hd]
  · exact div_nonneg (F.coefficient_nonneg d (Nat.pos_of_ne_zero hd)) (Nat.cast_nonneg d)

/-- No zero dummy weights and no unproved covering-property field. -/
def FiniteCoverFrame.padded (F : FiniteCoverFrame) (ε : ℝ)
    (hε : 0 < ε) (hε1 : ε < 1) : LogBudgetCover (F.support : Set ℕ) where
  frame := fun j => if j = 0 then F.support else ∅
  weight := paddedWeight ε
  exponent := fun _ => F.exponent
  coefficient := fun j d => if j = 0 then F.coefficient d else 0
  frame_positive := by
    intro j
    split_ifs
    · exact F.positive
    · simp
  weight_positive := paddedWeight_positive hε hε1
  weight_sum := paddedWeight_hasSum ε
  exponent_bounds := fun _ => ⟨F.exponent_pos, F.exponent_le_one⟩
  coefficient_nonneg := by
    intro j d hd
    split_ifs
    · exact F.coefficient_nonneg d hd
    · exact le_rfl
  column_summable := by
    intro j
    by_cases hj : j = 0
    · simpa only [if_pos hj] using F.column_summable
    · simp only [if_neg hj, zero_div]
      exact summable_zero
  covers := fun a ha => ⟨0, by simpa using ha⟩
  majorises := by
    intro j n hn
    by_cases hj : j = 0
    · simpa only [if_pos hj] using F.majorises n hn
    · simp [hj, Real.zero_rpow F.exponent_pos.ne']
  budget_summable := by
    apply summable_zero_supported
    intro j
    simp

/-- The precise epsilon penalty, before taking an infimum. -/
theorem FiniteCoverFrame.padded_cost (F : FiniteCoverFrame) (ε : ℝ)
    (hε : 0 < ε) (hε1 : ε < 1) :
    (F.padded ε hε hε1).cost =
      F.cost / ((1 - ε) ^ F.exponent) / ((2 : ℝ) ^ F.exponent - 1) := by
  unfold LogBudgetCover.cost
  rw [tsum_zero_supported]
  · simp only [FiniteCoverFrame.padded, ↓reduceIte, paddedWeight_zero,
      FiniteCoverFrame.cost]
  · intro j
    simp only [FiniteCoverFrame.padded, Nat.succ_ne_zero, if_false,
      zero_div, tsum_zero]

/-- Every literal finite frame has a strictly-positive countable cover. -/
theorem FiniteCoverFrame.cover_nonempty (F : FiniteCoverFrame) :
    Nonempty (LogBudgetCover (F.support : Set ℕ)) :=
  ⟨F.padded (1 / 2) (by norm_num) (by norm_num)⟩

theorem LogBudgetCover.cost_nonneg {A : Set ℕ} (C : LogBudgetCover A) :
    0 ≤ C.cost := by
  unfold LogBudgetCover.cost
  apply tsum_nonneg
  intro j
  apply div_nonneg _ (sub_pos.mpr (Real.one_lt_rpow (by norm_num)
    (C.exponent_bounds j).1)).le
  apply div_nonneg _ (Real.rpow_pos_of_pos (C.weight_positive j) _).le
  apply tsum_nonneg
  intro d
  by_cases hd : d = 0
  · simp [hd]
  · exact div_nonneg (C.coefficient_nonneg j d (Nat.pos_of_ne_zero hd))
      (Nat.cast_nonneg d)

theorem admissibleLogCoverCosts_bddBelow (A : Set ℕ) :
    BddBelow (admissibleLogCoverCosts A) := by
  refine ⟨0, ?_⟩
  rintro _ ⟨C, rfl⟩
  exact C.cost_nonneg

theorem optimizedLogCoverCost_le_cost {A : Set ℕ} (C : LogBudgetCover A) :
    optimizedLogCoverCost A ≤ C.cost :=
  csInf_le (admissibleLogCoverCosts_bddBelow A) ⟨C, rfl⟩

theorem optimizedLogCoverCost_nonneg {A : Set ℕ} (C : LogBudgetCover A) :
    0 ≤ optimizedLogCoverCost A := by
  apply le_csInf (show (admissibleLogCoverCosts A).Nonempty from ⟨C.cost, C, rfl⟩)
  rintro _ ⟨D, rfl⟩
  exact D.cost_nonneg

/-- Pass to the limit through actual admissible positive-weight covers. -/
theorem FiniteCoverFrame.optimizedCost_le (F : FiniteCoverFrame) :
    optimizedLogCoverCost (F.support : Set ℕ) ≤ F.scalarCost := by
  let ε : ℕ → ℝ := fun k => 1 / ((k : ℝ) + 2)
  have hε : ∀ k, 0 < ε k := fun k => by dsimp [ε]; positivity
  have hε1 : ∀ k, ε k < 1 := by
    intro k
    dsimp [ε]
    apply (div_lt_one (by positivity : 0 < (k : ℝ) + 2)).mpr
    have := Nat.cast_nonneg (α := ℝ) k
    linarith
  have hNat : Tendsto (fun k : ℕ => (k : ℝ) + 2) atTop atTop := by
    apply Filter.tendsto_atTop.2
    intro R
    filter_upwards [(tendsto_natCast_atTop_atTop : Tendsto
      (fun k : ℕ => (k : ℝ)) atTop atTop).eventually (eventually_ge_atTop R)] with k hk
    linarith
  have hεlim : Tendsto ε atTop (nhds 0) := tendsto_const_nhds.div_atTop hNat
  have hbase : Tendsto (fun k => 1 - ε k) atTop (nhds 1) := by
    simpa using tendsto_const_nhds.sub hεlim
  have hp : Tendsto (fun k => (1 - ε k) ^ F.exponent) atTop (nhds 1) := by
    simpa using hbase.rpow_const (Or.inl (by norm_num : (1 : ℝ) ≠ 0))
  have hlim : Tendsto (fun k => F.cost / ((1 - ε k) ^ F.exponent) /
      ((2 : ℝ) ^ F.exponent - 1)) atTop (nhds F.scalarCost) := by
    simpa only [div_one, FiniteCoverFrame.scalarCost] using
      (tendsto_const_nhds.div hp (by norm_num : (1 : ℝ) ≠ 0)).div_const
        ((2 : ℝ) ^ F.exponent - 1)
  apply ge_of_tendsto hlim
  exact Filter.Eventually.of_forall fun k => by
    have h := optimizedLogCoverCost_le_cost (F.padded (ε k) (hε k) (hε1 k))
    rwa [F.padded_cost] at h

end ErdosProblems.Erdos257.PaperCompleteR8
end
