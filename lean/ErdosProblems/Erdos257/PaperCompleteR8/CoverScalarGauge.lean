import ErdosProblems.Erdos257.PaperCompleteR7.CoverKernel
import Mathlib

/-!
# The actual scalar cover gauge and its first exact branch

Proof source. The infimum is over genuine admissible exponents.
This module proves nonnegativity, the e*log lower bound, and the exact branch
Psi(t)=t for 1<=t<=4. The large-t exact branch is proved in analytic_proofs.md
but is not asserted as a Lean theorem in this module.
-/
noncomputable section
namespace ErdosProblems.Erdos257.PaperCompleteR8
open ErdosProblems.Erdos257.PaperCompleteR7

/-- Values of the scalar cost at all admissible exponents. -/
def scalarCoverCosts (t : ℝ) : Set ℝ :=
  {v | ∃ α : ℝ, 0 < α ∧ α ≤ 1 ∧ v = t ^ α / ((2 : ℝ) ^ α - 1)}

/-- The paper's actual scalar gauge, including its separate zero convention. -/
def coverGauge (t : ℝ) : ℝ := if t = 0 then 0 else sInf (scalarCoverCosts t)

theorem scalarCoverCosts_nonempty (t : ℝ) : (scalarCoverCosts t).Nonempty := by
  refine ⟨t, 1, by norm_num, le_rfl, ?_⟩
  norm_num

theorem scalarCoverCosts_nonneg {t v : ℝ} (ht : 0 ≤ t) (hv : v ∈ scalarCoverCosts t) :
    0 ≤ v := by
  obtain ⟨α, hα, hα1, rfl⟩ := hv
  have hd : 0 < (2 : ℝ) ^ α - 1 := sub_pos.mpr (Real.one_lt_rpow (by norm_num) hα)
  exact div_nonneg (Real.rpow_nonneg ht _) hd.le

theorem scalarCoverCosts_bddBelow {t : ℝ} (ht : 0 ≤ t) : BddBelow (scalarCoverCosts t) :=
  ⟨0, fun _ hv => scalarCoverCosts_nonneg ht hv⟩

@[simp] theorem coverGauge_zero : coverGauge 0 = 0 := by simp [coverGauge]

theorem coverGauge_nonneg {t : ℝ} (ht : 0 ≤ t) : 0 ≤ coverGauge t := by
  by_cases h0 : t = 0
  · simp [h0]
  · rw [coverGauge, if_neg h0]
    exact le_csInf (scalarCoverCosts_nonempty t) (fun _ hv => scalarCoverCosts_nonneg ht hv)

theorem coverGauge_le_cost {t α : ℝ} (ht : 0 ≤ t) (hα : 0 < α) (hα1 : α ≤ 1) :
    coverGauge t ≤ t ^ α / ((2 : ℝ) ^ α - 1) := by
  by_cases h0 : t = 0
  · rw [h0, coverGauge_zero]
    exact scalarCoverCosts_nonneg (by norm_num) ⟨α, hα, hα1, rfl⟩
  · rw [coverGauge, if_neg h0]
    exact csInf_le (scalarCoverCosts_bddBelow ht) ⟨α, hα, hα1, rfl⟩

theorem coverGauge_le_self {t : ℝ} (ht : 0 ≤ t) : coverGauge t ≤ t := by
  have h := coverGauge_le_cost ht (by norm_num : (0 : ℝ) < 1) le_rfl
  norm_num at h
  exact h

theorem exp_one_mul_log_le_coverGauge {t : ℝ} (ht : 1 ≤ t) :
    Real.exp 1 * Real.log t ≤ coverGauge t := by
  have ht0 : t ≠ 0 := by linarith
  rw [coverGauge, if_neg ht0]
  apply le_csInf (scalarCoverCosts_nonempty t)
  rintro v ⟨α, hα, hα1, rfl⟩
  exact exp_one_mul_log_le_rpow_div ht hα hα1

/-- For t<=4, the exponent-one cost beats every admissible fractional exponent.
The proof is algebraic: 4(x-1)<=x^2, with x=2^alpha. -/
theorem self_le_scalarCoverCost_of_le_four {t α : ℝ}
    (ht1 : 1 ≤ t) (ht4 : t ≤ 4) (hα : 0 < α) (hα1 : α ≤ 1) :
    t ≤ t ^ α / ((2 : ℝ) ^ α - 1) := by
  have ht : 0 < t := by linarith
  have hβ : 0 ≤ 1 - α := by linarith
  let x : ℝ := (2 : ℝ) ^ α
  let v : ℝ := t ^ (1 - α)
  have hx : 1 < x := Real.one_lt_rpow (by norm_num) hα
  have hv : 0 ≤ v := Real.rpow_nonneg ht.le _
  have hpow : v ≤ (4 : ℝ) ^ (1 - α) := Real.rpow_le_rpow ht.le ht4 hβ
  have hx2 : x ^ (2 : ℕ) = (2 : ℝ) ^ (α * 2) := by
    dsimp [x]
    rw [← Real.rpow_natCast, ← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 2)]
    norm_num
  have hfour : (4 : ℝ) ^ (1 - α) * x ^ (2 : ℕ) = 4 := by
    rw [hx2]
    have hbase : (4 : ℝ) = (2 : ℝ) ^ (2 : ℝ) := by norm_num
    rw [hbase, ← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 2),
      ← Real.rpow_add (by norm_num : (0 : ℝ) < 2)]
    have he : (2 : ℝ) * (1 - α) + α * 2 = 2 := by ring
    rw [he]
  have hprod : v * x ^ (2 : ℕ) ≤ 4 := by
    calc
      _ ≤ (4 : ℝ) ^ (1 - α) * x ^ (2 : ℕ) :=
        mul_le_mul_of_nonneg_right hpow (sq_nonneg x)
      _ = 4 := hfour
  have hquad : 4 * (x - 1) ≤ x ^ (2 : ℕ) := by nlinarith [sq_nonneg (x - 2)]
  have hquadV := mul_le_mul_of_nonneg_left hquad hv
  have hsmall : v * (x - 1) ≤ 1 := by nlinarith only [hprod, hquadV]
  have htprod : t ^ α * v = t := by
    dsimp [v]
    rw [← Real.rpow_add ht]
    have he : α + (1 - α) = 1 := by ring
    rw [he, Real.rpow_one]
  apply (le_div_iff₀ (sub_pos.mpr hx)).2
  have hscaled := mul_le_mul_of_nonneg_left hsmall (Real.rpow_nonneg ht.le α)
  change t * (x - 1) ≤ t ^ α
  calc
    t * (x - 1) = (t ^ α * v) * (x - 1) :=
      congrArg (fun y : ℝ => y * (x - 1)) htprod.symm
    _ = t ^ α * (v * (x - 1)) := mul_assoc _ _ _
    _ ≤ t ^ α := by simpa only [mul_one] using hscaled

/-- Exact minimisation on the entire small-t branch, including the join t=4. -/
theorem coverGauge_eq_self_of_one_le_le_four {t : ℝ} (ht1 : 1 ≤ t) (ht4 : t ≤ 4) :
    coverGauge t = t := by
  apply le_antisymm (coverGauge_le_self (by linarith))
  have ht0 : t ≠ 0 := by linarith
  rw [coverGauge, if_neg ht0]
  apply le_csInf (scalarCoverCosts_nonempty t)
  rintro v ⟨α, hα, hα1, rfl⟩
  exact self_le_scalarCoverCost_of_le_four ht1 ht4 hα hα1

end ErdosProblems.Erdos257.PaperCompleteR8
end
