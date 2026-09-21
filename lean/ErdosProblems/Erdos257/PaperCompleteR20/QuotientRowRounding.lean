import Erdos249257.HalfCylinderIntegerGreedy

namespace ErdosProblems.Erdos257.PaperCompleteR20
open Erdos249257 Erdos249257.HalfCylinderIntegerGreedy

noncomputable def rowRoundingError (n : ℕ) (D : Finset ℕ) : ℝ :=
  ∑ d ∈ D, ((4 : ℝ)^n*mersenneWeight d-(truncatedMersenneWeight n d : ℝ))

theorem row_rounding_error_bounds (n : ℕ) (D : Finset ℕ)
    (hD : ∀ d ∈ D, 1 ≤ d) :
    0 ≤ rowRoundingError n D ∧ rowRoundingError n D ≤ D.card ∧
      (D.Nonempty → rowRoundingError n D < D.card) := by
  have hl : ∀ d ∈ D, 0 ≤ (4 : ℝ)^n*mersenneWeight d-(truncatedMersenneWeight n d : ℝ) := by
    intro d hd
    exact sub_nonneg.mpr (truncatedMersenneWeight_cast_le_scaled (hD d hd))
  have hu : ∀ d ∈ D, (4 : ℝ)^n*mersenneWeight d-(truncatedMersenneWeight n d : ℝ) < 1 := by
    intro d hd
    have h := scaled_lt_truncatedMersenneWeight_cast_add_one (s := n) (hD d hd)
    push_cast at h
    linarith
  unfold rowRoundingError
  refine ⟨Finset.sum_nonneg hl, ?_, ?_⟩
  · calc
      _ ≤ ∑ d ∈ D, (1 : ℝ) := Finset.sum_le_sum (fun d hd ↦ (hu d hd).le)
      _ = _ := by simp
  · intro hne
    calc
      _ < ∑ d ∈ D, (1 : ℝ) := Finset.sum_lt_sum_of_nonempty hne hu
      _ = _ := by simp

/-- Sufficient and necessary separation margins keep the additive error. -/
theorem deviation_error_margins (delta a eta H B : ℝ)
    (heq : delta = a+eta) (hb : |eta| < B) :
    (H+B < |a| → H < |delta|) ∧
    (H < |delta| → H-B < |a|) := by
  have hu : |delta| ≤ |a|+|eta| := by rw [heq]; exact abs_add_le a eta
  have hl : |a| ≤ |delta|+|eta| := by
    have he : a = delta-eta := by linarith
    rw [he]
    simpa only [sub_zero, zero_sub, abs_neg] using abs_sub_le delta 0 eta
  constructor <;> intro h <;> linarith

#print axioms row_rounding_error_bounds
#print axioms deviation_error_margins
end ErdosProblems.Erdos257.PaperCompleteR20
