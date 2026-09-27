import ErdosProblems.Erdos257.PaperCompleteR8.CountableGaugeBudget
import ErdosProblems.Erdos257.PaperCompleteR8.CoverClassTransport
import Mathlib

/-!
# The historical two-inverse-power class, not merely fixed exponents

The definition below is the old displayed cost after reindexing j>=1 by j+1.
The obstruction quantifies over every finite-frame cover, every enumeration,
every overlap, and every sequence of admissible exponents.
-/
noncomputable section
namespace ErdosProblems.Erdos257.PaperCompleteR8
open Finset
open ErdosProblems.Erdos257.PaperCompleteR7

/-- A convenient elementary estimate; no Taylor-series certificate is needed. -/
theorem sq_le_exp_of_nonneg {u : ℝ} (hu : 0 ≤ u) : u ^ 2 ≤ Real.exp u := by
  by_cases hu0 : u = 0
  · simp [hu0]
  have hupos : 0 < u := lt_of_le_of_ne hu (Ne.symm hu0)
  have hup : 0 < u / 2 := by linarith
  have he : (2 : ℝ) ≤ Real.exp 1 := by linarith [Real.add_one_le_exp (1 : ℝ)]
  have htan := exp_one_mul_le_exp hup
  have huE : u ≤ Real.exp (u / 2) := by nlinarith
  have hs : u ^ 2 ≤ Real.exp (u / 2) ^ 2 := by nlinarith [Real.exp_pos (u / 2)]
  have heq : Real.exp (u / 2) ^ 2 = Real.exp u := by
    rw [pow_two, ← Real.exp_add]
    congr 1
    ring
  exact hs.trans_eq heq

def oldScalarKernel (α : ℝ) : ℝ := (2 : ℝ) ^ α / (((2 : ℝ) ^ α - 1) ^ 2)

theorem oldScalarKernel_nonneg (α : ℝ) : 0 ≤ oldScalarKernel α :=
  div_nonneg (Real.rpow_nonneg (by norm_num) _) (sq_nonneg _)

/-- The paper's constant 1/2 is retained, although the elementary estimate
used here also permits a stronger constant. -/
theorem half_log_sq_le_old_scalar_cost {t α : ℝ} (ht : 1 ≤ t)
    (hα : 0 < α) (hα1 : α ≤ 1) :
    (Real.log t) ^ 2 / 2 ≤ t ^ α * oldScalarKernel α := by
  have ht0 : 0 < t := by linarith
  have hlog : 0 ≤ Real.log t := Real.log_nonneg ht
  have hB : 1 < (2 : ℝ) ^ α := Real.one_lt_rpow (by norm_num) hα
  have hd : 0 < (2 : ℝ) ^ α - 1 := by linarith
  have hdα : (2 : ℝ) ^ α - 1 ≤ α := two_rpow_sub_one_le_self hα.le hα1
  have hsq : ((2 : ℝ) ^ α - 1) ^ 2 ≤ α ^ 2 := by nlinarith
  have hexp := sq_le_exp_of_nonneg (mul_nonneg hα.le hlog)
  have hp : (α * Real.log t) ^ 2 ≤ t ^ α := by
    rw [Real.rpow_def_of_pos ht0]
    simpa only [mul_comm] using hexp
  have hpow : 0 ≤ t ^ α := Real.rpow_nonneg ht0.le _
  have hprod := mul_le_mul_of_nonneg_left hsq (sq_nonneg (Real.log t))
  have hbprod := mul_le_mul_of_nonneg_left hB.le hpow
  unfold oldScalarKernel
  rw [← mul_div_assoc]
  apply (le_div_iff₀ (sq_pos_of_pos hd)).mpr
  nlinarith [sq_nonneg (Real.log t)]

/-- A general scalar comparison may be averaged through a countable cover.
The scalar premise is local and is proved explicitly for the old kernel below. -/
theorem countable_cover_scalar_kernel_mean_le_cost
    (φ : ℕ → ℝ) (k : ℝ → ℝ) (hφ0 : φ 0 = 0)
    (hk : ∀ α, 0 < α → α ≤ 1 → 0 ≤ k α)
    (hscalar : ∀ f : ℕ, f ≠ 0 → ∀ α, 0 < α → α ≤ 1 → φ f ≤ (f : ℝ) ^ α * k α)
    (F : Finset ℕ) (G : ℕ → Finset ℕ) (η α : ℕ → ℝ) (c : ℕ → ℕ → ℝ)
    (X : ℕ) (hX : 0 < X) (hη : HasSum η 1) (hηpos : ∀ j, 0 < η j)
    (hα : ∀ j, 0 < α j ∧ α j ≤ 1)
    (hc : ∀ j d, 0 < d → 0 ≤ c j d)
    (hcolumn : ∀ j, Summable (fun d : ℕ => c j d / (d : ℝ)))
    (hcover : ∀ a ∈ F, ∃ j, a ∈ G j)
    (hmaj : ∀ j n, 0 < n →
      (((G j).filter (fun a => a ∣ n)).card : ℝ) ^ α j ≤ ∑ d ∈ n.divisors, c j d)
    (hcost : Summable (fun j => (∑' d : ℕ, c j d / (d : ℝ)) / (η j ^ α j) * k (α j))) :
    (∑ n ∈ Icc 1 X, φ ((F.filter (fun a => a ∣ n)).card)) / X ≤
      ∑' j, (∑' d : ℕ, c j d / (d : ℝ)) / (η j ^ α j) * k (α j) := by
  classical
  let K : ℕ → ℝ := fun j => (∑' d : ℕ, c j d / (d : ℝ)) / (η j ^ α j) * k (α j)
  have hK : ∀ j, 0 ≤ K j := by
    intro j
    apply mul_nonneg _ (hk _ (hα j).1 (hα j).2)
    apply div_nonneg _ (Real.rpow_pos_of_pos (hηpos j) _).le
    apply tsum_nonneg
    intro d
    by_cases hd : d = 0
    · simp [hd]
    · exact div_nonneg (hc j d (Nat.pos_of_ne_zero hd)) (Nat.cast_nonneg d)
  by_cases hF : F = ∅
  · simp only [hF, filter_empty, card_empty, hφ0, sum_const_zero, zero_div]
    exact tsum_nonneg hK
  obtain ⟨J, hFJ⟩ := exists_finite_frame_subcover F G hcover
  have hJ : J.Nonempty := by
    obtain ⟨a, ha⟩ := Finset.nonempty_iff_ne_empty.mpr hF
    obtain ⟨j, hj, _⟩ := mem_biUnion.mp (hFJ ha)
    exact ⟨j, hj⟩
  have hηJ : ∑ j ∈ J, η j ≤ 1 := by
    simpa only [hη.tsum_eq] using hη.summable.sum_le_tsum J (fun j _ => (hηpos j).le)
  have hpoint : ∀ n, φ ((F.filter (fun a => a ∣ n)).card) ≤
      ∑ j ∈ J, (((G j).filter (fun a => a ∣ n)).card : ℝ) ^ α j /
        (η j ^ α j) * k (α j) := by
    intro n
    let f := (F.filter (fun a => a ∣ n)).card
    let g := fun j => ((G j).filter (fun a => a ∣ n)).card
    have hnonneg : ∀ j ∈ J, 0 ≤ (g j : ℝ) ^ α j / (η j ^ α j) * k (α j) :=
      fun j _ => mul_nonneg (div_nonneg (Real.rpow_nonneg (Nat.cast_nonneg _) _)
        (Real.rpow_pos_of_pos (hηpos j) _).le) (hk _ (hα j).1 (hα j).2)
    by_cases hf : f = 0
    · change φ f ≤ _
      rw [hf, hφ0]
      exact Finset.sum_nonneg hnonneg
    have hcov : (f : ℝ) ≤ ∑ j ∈ J, (g j : ℝ) := by
      exact_mod_cast divisor_count_le_sum_of_frame_cover F J G hFJ n
    obtain ⟨j, hj, hshare⟩ := exists_frame_ge_subprobability_share J η
      (fun j => (g j : ℝ)) f hJ hηJ (Nat.cast_nonneg f) hcov
    have hratio : (f : ℝ) ≤ (g j : ℝ) / η j :=
      (le_div_iff₀ (hηpos j)).mpr (by simpa [mul_comm] using hshare)
    have hp := Real.rpow_le_rpow (Nat.cast_nonneg f) hratio (hα j).1.le
    rw [Real.div_rpow (Nat.cast_nonneg _) (hηpos j).le] at hp
    exact (hscalar f hf _ (hα j).1 (hα j).2).trans
      ((mul_le_mul_of_nonneg_right hp (hk _ (hα j).1 (hα j).2)).trans
        (Finset.single_le_sum hnonneg hj))
  calc
    _ ≤ (∑ n ∈ Icc 1 X, ∑ j ∈ J,
        (((G j).filter (fun a => a ∣ n)).card : ℝ) ^ α j /
          (η j ^ α j) * k (α j)) / X :=
      div_le_div_of_nonneg_right (Finset.sum_le_sum (fun n _ => hpoint n)) (Nat.cast_nonneg X)
    _ = ∑ j ∈ J, ((∑ n ∈ Icc 1 X,
        (((G j).filter (fun a => a ∣ n)).card : ℝ) ^ α j) / X) /
          (η j ^ α j) * k (α j) := by
      rw [Finset.sum_comm, Finset.sum_div]
      apply Finset.sum_congr rfl
      intro j hj
      rw [← Finset.sum_mul, ← Finset.sum_div]
      ring
    _ ≤ ∑ j ∈ J, K j := by
      apply Finset.sum_le_sum
      intro j hj
      have hav := cesaro_le_tsum_divisorMajorantCost
        (fun n => (((G j).filter (fun a => a ∣ n)).card : ℝ) ^ α j)
        (c j) X hX (fun n => Real.rpow_nonneg (Nat.cast_nonneg _) _)
        (hc j) (hcolumn j) (hmaj j)
      exact mul_le_mul_of_nonneg_right
        (div_le_div_of_nonneg_right hav (Real.rpow_pos_of_pos (hηpos j) _).le)
        (hk _ (hα j).1 (hα j).2)
    _ ≤ _ := hcost.sum_le_tsum J (fun j _ => hK j)

/-- The exact historical cost, indexed by j+1. -/
def _root_.ErdosProblems.Erdos257.PaperCompleteR7.PositiveCoverData.oldCostTerm (C : PositiveCoverData) (j : ℕ) : ℝ :=
  C.cost j * (2 : ℝ) ^ (((j + 1 : ℕ) : ℝ) * C.exponent j) *
    (2 : ℝ) ^ C.exponent j / (((2 : ℝ) ^ C.exponent j - 1) ^ 2)

def _root_.ErdosProblems.Erdos257.PaperCompleteR7.PositiveCoverData.OldCostSummable (C : PositiveCoverData) : Prop :=
  Summable C.oldCostTerm

def HasOldPositiveCover (A : Set ℕ) : Prop :=
  ∃ C : PositiveCoverData, A ⊆ C.host ∧ C.OldCostSummable

def finiteLogSquareMean (F : Finset ℕ) (X : ℕ) : ℝ :=
  (∑ n ∈ Icc 1 X, (Real.log ((F.filter (fun a => a ∣ n)).card : ℝ)) ^ 2 / 2) / X

theorem geometric_weight_inverse_rpow (j : ℕ) (α : ℝ) :
    (coverThreshold 1 j ^ α)⁻¹ = (2 : ℝ) ^ (((j + 1 : ℕ) : ℝ) * α) := by
  unfold coverThreshold
  rw [one_mul, Real.inv_rpow (by positivity : 0 ≤ (2 : ℝ) ^ (j + 1)), inv_inv,
    ← Real.rpow_natCast, ← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 2)]

theorem oldCostTerm_eq_kernel (C : PositiveCoverData) (j : ℕ) :
    C.oldCostTerm j = C.cost j / (coverThreshold 1 j ^ C.exponent j) * oldScalarKernel (C.exponent j) := by
  rw [div_eq_mul_inv, geometric_weight_inverse_rpow]
  unfold PositiveCoverData.oldCostTerm oldScalarKernel
  ring

theorem finiteLogSquareMean_le_old_cost (C : PositiveCoverData) (hC : C.OldCostSummable)
    (F : Finset ℕ) (hF : (F : Set ℕ) ⊆ C.host) (X : ℕ) (hX : 0 < X) :
    finiteLogSquareMean F X ≤ ∑' j, C.oldCostTerm j := by
  have hη : HasSum (coverThreshold 1) 1 := by
    simpa only [tsum_coverThreshold] using (summable_coverThreshold 1).hasSum
  have hsc : ∀ f : ℕ, f ≠ 0 → ∀ α, 0 < α → α ≤ 1 →
      (Real.log (f : ℝ)) ^ 2 / 2 ≤ (f : ℝ) ^ α * oldScalarKernel α := by
    intro f hf α hα hα1
    exact half_log_sq_le_old_scalar_cost
      (by exact_mod_cast Nat.one_le_iff_ne_zero.mpr hf) hα hα1
  have hs : Summable (fun j => C.cost j / (coverThreshold 1 j ^ C.exponent j) *
      oldScalarKernel (C.exponent j)) := by
    simpa only [← oldCostTerm_eq_kernel] using hC
  have h := countable_cover_scalar_kernel_mean_le_cost
    (fun f => (Real.log (f : ℝ)) ^ 2 / 2) oldScalarKernel (by simp)
    (fun α _ _ => oldScalarKernel_nonneg α) hsc F C.frame (coverThreshold 1)
    C.exponent C.coefficient X hX hη
    (fun j => coverThreshold_pos (by norm_num) j) C.exponent_bounds
    C.coefficient_nonneg C.column_summable (fun a ha => hF ha) C.majorises hs
  rw [tsum_congr (oldCostTerm_eq_kernel C)]
  simpa only [finiteLogSquareMean, PositiveCoverData.cost] using h

/-- Every old variable-exponent cover is excluded, not just the displayed one. -/
theorem no_old_cover_of_unbounded_logSquare_means (A : Set ℕ)
    (hlarge : ∀ R : ℝ, ∃ F : Finset ℕ, (F : Set ℕ) ⊆ A ∧
      ∃ X : ℕ, 0 < X ∧ R < finiteLogSquareMean F X) :
    ¬ HasOldPositiveCover A := by
  rintro ⟨C, hAC, hC⟩
  obtain ⟨F, hFA, X, hX, hR⟩ := hlarge (∑' j, C.oldCostTerm j)
  exact (not_lt_of_ge (finiteLogSquareMean_le_old_cost C hC F (hFA.trans hAC) X hX)) hR

end ErdosProblems.Erdos257.PaperCompleteR8
end
